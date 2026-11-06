/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteRepresentationTensor
public import AtiyahSinger.Algebra.SpinorExteriorDoubling
public import AtiyahSinger.Geometry.SpinComplexificationFrame
public import AtiyahSinger.Topology.AssociatedVectorDescent
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.ExteriorFamilyContinuity
public import AtiyahSinger.Topology.SpinorBundle

/-!
# Self-tensor spinors on the original complexified bundle

Public module ID: M2178.

The actual algebraic self-tensor comparison descends at the same principal
point in both spinor factors. Its target is the exterior algebra of the native
scalar extension, with the original wedge-sum topology. The representative
formula retains the chosen invariant bilinear duality and the corrected right
phase in the algebraic comparison. No independently chosen bundle or action
is substituted for either side.

Source: SG I.5 and II.3, the Clifford exterior model and associated bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.exteriorTopology

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

set_option maxHeartbeats 900000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The self-tensor exterior isomorphism retains every pair of original representatives. -/
theorem TopologicalSpinStructure.exists_spinorTensor_exterior_iso
    (S : TopologicalSpinStructure m E o hm hP)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t)) :
    letI := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
    ∃ d : ComplexBundle.Iso (fun b ↦ SpinorBundle m hP b ⊗[ℂ] SpinorBundle m hP b)
        (fun b ↦ ExteriorAlgebra ℂ (ℂ ⊗[ℝ] E b)),
      ∀ (b : B) (p : P) (hp : projection p = b) (s t : ComplexSpinor m),
        d.linearEquiv b
          (associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp s ⊗ₜ[ℂ]
            associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp t) =
          ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
            (complexSpinorDoublingExteriorEquiv m e (s ⊗ₜ[ℂ] t)) := by
  classical
  let V := ComplexSpinor m
  let U := EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)
  let A := SpinorBundle m hP
  let F (b : B) := ℂ ⊗[ℝ] E b
  let H (b : B) := ExteriorAlgebra ℂ (F b)
  let := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := ComplexBundle.isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
  let := ComplexBundle.isFiniteRank_exterior (E := F)
  let ρ := complexSpinContRepresentation m
  let := isFiniteRank_associatedVector hP ρ (continuous_complexSpinRepresentation m)
  let := ComplexBundle.isFiniteRank_tensor (E := A) (F := A)
  let n := Module.finrank ℂ V
  let c : V ≃L[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  let σ := FiniteContinuousRepresentation.ofEquiv ρ (continuous_complexSpinRepresentation m) c
  let τ := σ.tensor σ
  let q := FiniteContinuousRepresentation.tensorCoordinates n n
  let Q : (Fin (n * n) → ℂ) ≃ₗ[ℂ] (V ⊗[ℂ] V) :=
    q.symm.trans (TensorProduct.congr c.symm.toLinearEquiv c.symm.toLinearEquiv)
  let Φ := complexSpinorDoublingExteriorEquiv m e
  let f (b : B) (p : P) (hp : projection p = b) := Q.trans
    (TensorProduct.congr (associatedVectorFiberMkLinearEquiv hP ρ p hp)
      (associatedVectorFiberMkLinearEquiv hP ρ p hp))
  have hmk : Continuous (fun z : P × V ↦
      (⟨projection z.1, associatedVectorFiberMk hP ρ z.1 rfl z.2⟩ : TotalSpace Unit A)) :=
    (associatedVectorTotalHomeomorph hP ρ).symm.continuous.comp continuous_quot_mk
  have hrep (b : B) (p : P) (hp : projection p = b)
      (g : spinGroup (realSpinorQuadraticForm m)) (v : V) :
      associatedVectorFiberMkLinearEquiv hP ρ (MulOpposite.op g • p)
          ((hP.projection_smul g p).trans hp) v =
        associatedVectorFiberMkLinearEquiv hP ρ p hp (ρ g v) := by
    let := associatedRepresentationAction ρ
    apply Subtype.ext
    exact associatedBundleMk_smul p g v
  have hQ (g : spinGroup (realSpinorQuadraticForm m)) (v : Fin (n * n) → ℂ) :
      Q (τ.representation g v) =
        TensorProduct.map (ρ g).toLinearMap (ρ g).toLinearMap (Q v) := by
    have haction : q.symm (τ.representation g v) =
        TensorProduct.map (σ.representation g).toLinearMap (σ.representation g).toLinearMap
          (q.symm v) := by
      change q.symm (q _) = _
      exact q.symm_apply_apply _
    change TensorProduct.congr c.symm.toLinearEquiv c.symm.toLinearEquiv
      (q.symm (τ.representation g v)) = TensorProduct.map (ρ g).toLinearMap (ρ g).toLinearMap
        (TensorProduct.congr c.symm.toLinearEquiv c.symm.toLinearEquiv (q.symm v))
    rw [haction]
    generalize q.symm v = w
    induction w using TensorProduct.inductionOn with
    | add w z hw hz => simp only [map_add, hw, hz]
    | tmul s t =>
      simp only [TensorProduct.map_tmul, TensorProduct.congr_tmul]
      congr 1 <;> exact c.symm_apply_apply _
  have hcov (b : B) (p : P) (hp : projection p = b)
      (g : spinGroup (realSpinorQuadraticForm m)) (v : Fin (n * n) → ℂ) :
      f b (MulOpposite.op g • p) ((hP.projection_smul g p).trans hp) v =
        f b p hp (τ.representation g v) := by
    change TensorProduct.congr _ _ (Q v) = TensorProduct.congr _ _ (Q (τ.representation g v))
    rw [hQ]
    generalize Q v = w
    induction w using TensorProduct.inductionOn with
    | add w z hw hz => simp only [map_add, hw, hz]
    | tmul s t =>
      simp only [TensorProduct.map_tmul, TensorProduct.congr_tmul]
      rw [hrep b p hp g s, hrep b p hp g t]
      rfl
  -- Finite tensor sums give continuity in the unchanged tensor total topology.
  let b := Module.finBasis ℂ V
  let basis := (b.tensorProduct b).reindex finProdFinEquiv
  let D := TotalSpace Unit (fun x ↦ (Fin (n * n) → A x) × (Fin (n * n) → A x))
  let : TopologicalSpace D := TopologicalSpace.induced (fun z : D ↦
    (z.proj, (fun k ↦ (⟨z.proj, z.snd.1 k⟩ : TotalSpace Unit A)),
      (fun k ↦ (⟨z.proj, z.snd.2 k⟩ : TotalSpace Unit A)))) inferInstance
  let gen (z : D) : TotalSpace Unit (fun x ↦ A x ⊗[ℂ] A x) :=
    ⟨z.proj, ∑ k : Fin (n * n), z.snd.1 k ⊗ₜ[ℂ] z.snd.2 k⟩
  have hgen : Continuous gen := continuous_iSup_rng (i := n * n) continuous_coinduced_rng
  let lift (z : P × (Fin (n * n) → ℂ)) : D :=
    ⟨projection z.1,
      (fun k ↦ associatedVectorFiberMk hP ρ z.1 rfl
        (basis.repr (Q z.2) k • b (finProdFinEquiv.symm k).1)),
      (fun k ↦ associatedVectorFiberMk hP ρ z.1 rfl (b (finProdFinEquiv.symm k).2))⟩
  have hlift : Continuous lift := by
    apply continuous_induced_rng.mpr
    refine (hP.projection_properties.1.comp continuous_fst).prodMk ?_
    apply Continuous.prodMk
    · apply continuous_pi
      intro k
      have hcoef : Continuous (fun z : P × (Fin (n * n) → ℂ) ↦ basis.repr (Q z.2) k) :=
        ((basis.coord k).comp Q.toLinearMap).continuous_of_finiteDimensional.comp continuous_snd
      exact hmk.comp (continuous_fst.prodMk (hcoef.smul continuous_const))
    · apply continuous_pi
      intro k
      exact hmk.comp (continuous_fst.prodMk continuous_const)
  have hc : Continuous (fun z : P × (Fin (n * n) → ℂ) ↦
      (⟨projection z.1, f (projection z.1) z.1 rfl z.2⟩ :
        TotalSpace Unit (fun x ↦ A x ⊗[ℂ] A x))) := by
    apply (hgen.comp hlift).congr
    intro z
    apply TotalSpace.mk_inj.mpr
    let L := TensorProduct.congr (associatedVectorFiberMkLinearEquiv hP ρ z.1 rfl)
      (associatedVectorFiberMkLinearEquiv hP ρ z.1 rfl)
    change (∑ k : Fin (n * n),
      associatedVectorFiberMkLinearEquiv hP ρ z.1 rfl
          (basis.repr (Q z.2) k • b (finProdFinEquiv.symm k).1) ⊗ₜ[ℂ]
        associatedVectorFiberMkLinearEquiv hP ρ z.1 rfl (b (finProdFinEquiv.symm k).2)) = _
    calc
      _ = L (∑ k : Fin (n * n), basis.repr (Q z.2) k • basis k) := by
        simp only [map_sum, map_smul, basis, Module.Basis.reindex_apply,
          Module.Basis.tensorProduct_apply', L, TensorProduct.congr_tmul,
          TensorProduct.smul_tmul']
        rfl
      _ = f (projection z.1) z.1 rfl z.2 := by rw [basis.sum_repr]; rfl
  obtain ⟨a, ha⟩ := exists_associatedVector_iso_of_covariant_equiv hP τ
    (fun x ↦ A x ⊗[ℂ] A x) f hc hcov
  -- The same finite representation also descends through the native complexified frames.
  let ext (b : B) (p : P) (hp : projection p = b) : ExteriorAlgebra ℂ U ≃ₗ[ℂ] H b :=
    LinearEquiv.ofBijective
      (ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap).toLinearMap
      ⟨ExteriorAlgebra.map_injective ⟨(S.complexificationFrame p b hp).symm.toLinearMap,
          by
            apply LinearMap.ext
            intro v
            exact (S.complexificationFrame p b hp).symm_apply_apply v⟩,
        ExteriorAlgebra.map_surjective_iff.mpr (S.complexificationFrame p b hp).surjective⟩
  let fE (b : B) (p : P) (hp : projection p = b) := Q.trans (Φ.trans (ext b p hp))
  have hExt : Continuous (fun z : P × ExteriorAlgebra ℂ U ↦
      (⟨projection z.1,
        ExteriorAlgebra.map (S.complexificationFrame z.1 (projection z.1) rfl).toLinearMap z.2⟩ :
          TotalSpace Unit H)) :=
    ComplexBundle.continuous_exteriorMap_family (X := B) (Y := P) (V := U) (E := F)
      ⟨projection, hP.projection_properties.1⟩
      (fun p ↦ (S.complexificationFrame p (projection p) rfl).toLinearMap)
      S.continuous_complexificationFrame
  have hcE : Continuous (fun z : P × (Fin (n * n) → ℂ) ↦
      (⟨projection z.1, fE (projection z.1) z.1 rfl z.2⟩ : TotalSpace Unit H)) := by
    have h := hExt.comp (continuous_fst.prodMk
      ((Q.trans Φ).continuous_of_finiteDimensional.comp continuous_snd))
    exact h
  have hcovE (b : B) (p : P) (hp : projection p = b)
      (g : spinGroup (realSpinorQuadraticForm m)) (v : Fin (n * n) → ℂ) :
      fE b (MulOpposite.op g • p) ((hP.projection_smul g p).trans hp) v =
        fE b p hp (τ.representation g v) := by
    change ExteriorAlgebra.map (S.complexificationFrame (MulOpposite.op g • p) b _).toLinearMap
      (Φ (Q v)) = ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
        (Φ (Q (τ.representation g v)))
    have hspin : Φ (TensorProduct.map (ρ g).toLinearMap (ρ g).toLinearMap (Q v)) =
        ExteriorAlgebra.map (complexSpinVectorComplexification m g).toLinearMap (Φ (Q v)) :=
      complexSpinorDoublingExteriorEquiv_spin m e he g (Q v)
    rw [hQ, hspin]
    have hframe : (S.complexificationFrame (MulOpposite.op g • p) b
          ((hP.projection_smul g p).trans hp)).toLinearMap =
        (S.complexificationFrame p b hp).toLinearMap.comp
          (complexSpinVectorComplexification m g).toLinearMap := by
      apply LinearMap.ext
      intro u
      exact S.complexificationFrame_covariant p b hp g u
    rw [hframe, ← ExteriorAlgebra.map_comp_map]
    rfl
  obtain ⟨aE, haE⟩ := exists_associatedVector_iso_of_covariant_equiv hP τ H fE hcE hcovE
  -- Compose the two descents and evaluate the inverse on the same principal representative.
  refine ⟨a.symm.trans aE, ?_⟩
  intro b p hp s t
  let v := Q.symm (s ⊗ₜ[ℂ] t)
  have hA : a.linearEquiv b (associatedVectorFiberMk hP τ.representation p hp v) =
      associatedVectorFiberMk hP ρ p hp s ⊗ₜ[ℂ] associatedVectorFiberMk hP ρ p hp t := by
    rw [ha]
    change TensorProduct.congr _ _ (Q (Q.symm (s ⊗ₜ[ℂ] t))) = _
    rw [LinearEquiv.apply_symm_apply, TensorProduct.congr_tmul]
    rfl
  change aE.linearEquiv b ((a.linearEquiv b).symm _) = _
  rw [← hA, LinearEquiv.symm_apply_apply, haE]
  change ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
    (Φ (Q (Q.symm (s ⊗ₜ[ℂ] t)))) = _
  rw [LinearEquiv.apply_symm_apply]

end AtiyahSinger
