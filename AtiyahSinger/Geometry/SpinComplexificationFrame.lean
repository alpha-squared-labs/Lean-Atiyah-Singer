/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorComplexification
public import AtiyahSinger.Geometry.SpinFrame
public import AtiyahSinger.Topology.ComplexificationBundle

/-!
# Native complexification frames from the specified spin lift

Public module ID: M1446.

Extend the actual real frame at the supplied principal point by complex scalars.
The source coordinates are those of the original complex Clifford algebra.
The frame family is continuous for the original real/imaginary total topology
and covariant for the same native Spin action. These are the geometric inputs
for descending the self-tensor exterior comparison to the original bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

/-- Extend the original frame at the supplied principal point, in the fixed Clifford coordinates. -/
def TopologicalSpinStructure.complexificationFrame
    (S : TopologicalSpinStructure m E o hm hP) (p : P) (b : B) (hp : projection p = b) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) ≃ₗ[ℂ] (ℂ ⊗[ℝ] E b) :=
  (complexSpinorComplexificationEquiv m).symm.trans
    (((realSpinorCoordinateIsometry m).symm.toLinearEquiv.trans
      (S.frame p b hp).toLinearEquiv).baseChange ℝ ℂ)

/-- Changing the principal point uses exactly the complexification of its native Spin action. -/
theorem TopologicalSpinStructure.complexificationFrame_covariant
    (S : TopologicalSpinStructure m E o hm hP) (p : P) (b : B) (hp : projection p = b)
    (g : spinGroup (realSpinorQuadraticForm m))
    (u : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    S.complexificationFrame (MulOpposite.op g • p) b ((hP.projection_smul g p).trans hp) u =
      S.complexificationFrame p b hp (complexSpinVectorComplexification m g u) := by
  -- Compare the actual real frames before extending either side by complex scalars.
  have hframe (q : P) (hq : projection q = b) (v : EuclideanSpace ℝ (Fin (2 * m))) :
      (⟨b, S.frame q b hq v⟩ : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 v⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  have hreal (v : EuclideanSpace ℂ (Fin m)) :
      S.frame (MulOpposite.op g • p) b ((hP.projection_smul g p).trans hp)
          ((realSpinorCoordinateIsometry m).symm v) =
        S.frame p b hp ((realSpinorCoordinateIsometry m).symm
          (realSpinVectorRepresentation m g v)) := by
    have h := S.equivariant g p ((realSpinorCoordinateIsometry m).symm v)
    rw [← hframe _ ((hP.projection_smul g p).trans hp), ← hframe p hp,
      LinearIsometryEquiv.apply_symm_apply] at h
    exact TotalSpace.mk_injective b h
  -- The native pure tensors span the unchanged scalar extension.
  obtain ⟨z, rfl⟩ := (complexSpinorComplexificationEquiv m).surjective u
  simp only [TopologicalSpinStructure.complexificationFrame,
    complexSpinVectorComplexification, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z v =>
    simp only [LinearEquiv.baseChange_tmul, LinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toLinearEquiv, hreal]

set_option maxHeartbeats 600000 in
-- Original orthogonal columns give local linear coordinates; no principal section is chosen.
/-- The extended frame is continuous in its actual principal point and Clifford vector. -/
theorem TopologicalSpinStructure.continuous_complexificationFrame
    (S : TopologicalSpinStructure m E o hm hP) :
    letI := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
    Continuous (fun z : P × (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) ↦
      (⟨projection z.1, S.complexificationFrame z.1 (projection z.1) rfl z.2⟩ :
        TotalSpace Unit (fun b ↦ ℂ ⊗[ℝ] E b))) := by
  classical
  let R := EuclideanSpace ℝ (Fin (2 * m))
  let V := EuclideanSpace ℂ (Fin m)
  let U := V × V
  let := ComplexBundle.complexificationTopology R E
  have hframe (p : P) (b : B) (hp : projection p = b) (v : R) :
      (⟨b, S.frame p b hp v⟩ : TotalSpace R E) =
        ⟨(S.frameMap p).val.1, (S.frameMap p).val.2 v⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection p).trans hp
    rfl
  let := orthogonalFrameTopology (2 * m) E
  have hforget : Continuous (fun q : OrientedOrthogonalFrameBundle m E o ↦ q.val) :=
    continuous_induced_dom
  have hcols : Continuous (fun q : OrthogonalFrameBundle (2 * m) E ↦
      (q.1, fun j : Fin (2 * m) ↦
        (⟨q.1, q.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩ : TotalSpace R E))) :=
    continuous_induced_dom
  have hcolumn (j : Fin (2 * m)) : Continuous (fun p : P ↦
      (⟨projection p, S.frame p (projection p) rfl
        (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩ : TotalSpace R E)) :=
    ((continuous_apply j).comp (hcols.comp (hforget.comp S.frameMap.continuous)).snd).congr
      (fun p ↦ (hframe p (projection p) rfl _).symm)
  -- A vector is its finite sum of original frame columns, also in every native bundle chart.
  have heval : Continuous (fun z : P × R ↦
      (⟨projection z.1, S.frame z.1 (projection z.1) rfl z.2⟩ : TotalSpace R E)) := by
    have hb := hP.projection_properties.1.comp (continuous_fst : Continuous (Prod.fst : P × R → P))
    rw [continuous_iff_continuousAt]
    intro z₀
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let t := trivializationAt R E (projection z₀.1)
    have hj (j : Fin (2 * m)) : ContinuousAt (fun z : P × R ↦
        (t ⟨projection z.1, S.frame z.1 (projection z.1) rfl
          (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩).2) z₀ :=
      ((FiberBundle.continuousAt_totalSpace R _).mp
        ((hcolumn j).comp continuous_fst).continuousAt).2
    have hsum : ContinuousAt (fun z : P × R ↦ ∑ j : Fin (2 * m),
        z.2 j • (t ⟨projection z.1, S.frame z.1 (projection z.1) rfl
          (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩).2) z₀ := by
      apply tendsto_finsetSum
      intro j _
      exact ((EuclideanSpace.proj j).continuous.comp continuous_snd).continuousAt.smul (hj j)
    apply hsum.congr_of_eventuallyEq
    filter_upwards [hb.continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt R E (projection z₀.1)))] with z hz
    change (t ⟨projection z.1, S.frame z.1 (projection z.1) rfl z.2⟩).2 = _
    have ht (w : E (projection z.1)) :
        (t ⟨projection z.1, w⟩).2 = t.continuousLinearMapAt ℝ (projection z.1) w :=
      (t.continuousLinearMapAt_apply_of_mem ℝ hz w).symm
    simp_rw [ht]
    have hs := (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).sum_repr z.2
    have h := congrArg (fun w ↦ t.continuousLinearMapAt ℝ (projection z.1)
      (S.frame z.1 (projection z.1) rfl w)) hs
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr] using h.symm
  -- Real and imaginary coordinates retain the same two actual real frame evaluations.
  let a : U ≃ₗ[ℝ] (V × V) :=
    ((complexSpinorComplexificationEquiv m).symm.restrictScalars ℝ).trans
      (complexificationReIm V)
  let L (p : P) := (realSpinorCoordinateIsometry m).symm.toLinearEquiv.trans
    (S.frame p (projection p) rfl).toLinearEquiv
  have hcoords (p : P) (u : U) :
      complexificationReIm (E (projection p))
          (S.complexificationFrame p (projection p) rfl u) =
        (L p (a u).1, L p (a u).2) := by
    obtain ⟨z, rfl⟩ := (complexSpinorComplexificationEquiv m).surjective u
    have ha : a (complexSpinorComplexificationEquiv m z) = complexificationReIm V z := by
      change complexificationReIm V ((complexSpinorComplexificationEquiv m).symm
        (complexSpinorComplexificationEquiv m z)) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [ha]
    clear ha
    simp only [TopologicalSpinStructure.complexificationFrame, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
    change complexificationReIm (E (projection p)) ((L p).baseChange ℝ ℂ _ _ z) =
      (L p (complexificationReIm V z).1, L p (complexificationReIm V z).2)
    induction z using TensorProduct.inductionOn with
    | tmul z v =>
      rw [LinearEquiv.baseChange_tmul, (complexificationReIm_properties _).1,
        (complexificationReIm_properties _).1, map_smul, map_smul]
    | add z w hz hw => simp only [map_add, hz, hw, Prod.fst_add, Prod.snd_add]; rfl
  have ha : Continuous (fun z : P × U ↦ a z.2) :=
    a.continuous_of_finiteDimensional.comp continuous_snd
  have hre := heval.comp (continuous_fst.prodMk
    ((realSpinorCoordinateIsometry m).symm.continuous.comp ha.fst))
  have him := heval.comp (continuous_fst.prodMk
    ((realSpinorCoordinateIsometry m).symm.continuous.comp ha.snd))
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply (hre.prodMk him).congr
  intro z
  change ((⟨projection z.1, L z.1 (a z.2).1⟩ : TotalSpace R E),
    (⟨projection z.1, L z.1 (a z.2).2⟩ : TotalSpace R E)) =
      ((⟨projection z.1, (complexificationReIm (E (projection z.1))
          (S.complexificationFrame z.1 (projection z.1) rfl z.2)).1⟩ : TotalSpace R E),
        (⟨projection z.1, (complexificationReIm (E (projection z.1))
          (S.complexificationFrame z.1 (projection z.1) rfl z.2)).2⟩ : TotalSpace R E))
  rw [hcoords]

end AtiyahSinger
