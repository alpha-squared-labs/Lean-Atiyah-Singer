/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantIndexTensor
public import AtiyahSinger.Analysis.EquivariantSmoothIndexEquivalence

/-!
# The full index of an actual finite tensor section operator

Public module ID: M0575.

The specified section equivalences identify the actual operator with a finite
coordinatewise copy and retain the mixing matrix of the original finite
representation. The actual kernels and quotient cokernels identify with their
tensor representations. Their finite coordinates suffice; no Hilbert norm on
a space of all smooth sections or dimension-only comparison is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [CompactSpace N] [T2Space N] [SecondCountableTopology N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : SmoothFiniteComplexBundle (n := m) N)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (τA : letI := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
    EquivariantStructure G A.Fiber)
  (τB : letI := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
    EquivariantStructure G B.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (hτA : τA.IsSmooth (n := m) (r := A.rank) IG)
  (hτB : τB.IsSmooth (n := m) (r := B.rank) IG)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
/-- A finite tensor section square multiplies the full smooth index by its coefficient. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_mul_of_sectionEquiv
    (ρ : FiniteContinuousRepresentation G)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν] {l l' : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ l)
    (Q : PseudodifferentialOperator (n := m) (r := A.rank) (q := B.rank)
      A.Fiber B.Fiber ν l')
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
    (hQg : Q.IsEquivariant IG τA τB hτA hτB) (hQ : Q.IsElliptic)
    (S : smoothSections (n := n) (r := E.rank) E.Fiber ≃ₗ[ℂ]
      (Fin ρ.dimension → smoothSections (n := m) (r := A.rank) A.Fiber))
    (T : smoothSections (n := n) (r := F.rank) F.Fiber ≃ₗ[ℂ]
      (Fin ρ.dimension → smoothSections (n := m) (r := B.rank) B.Fiber))
    (hS : ∀ g u i, S (σE.smoothSectionRepresentation IG hσE g u) i =
      ∑ j, ρ.representation g (Pi.single j 1) i •
        τA.smoothSectionRepresentation IG hτA g (S u j))
    (hT : ∀ g v i, T (σF.smoothSectionRepresentation IG hσF g v) i =
      ∑ j, ρ.representation g (Pi.single j 1) i •
        τB.smoothSectionRepresentation IG hτB g (T v j))
    (hinter : ∀ u i, Q.toLinearMap (S u i) = T (P.toLinearMap u) i) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
      finiteRepresentationClass ρ *
        Q.smoothEquivariantAnalyticIndex IG τA τB hτA hτB hQg hQ := by
  classical
  -- Coordinate restriction gives the actual product kernel and original range quotient.
  let K : P.toLinearMap.ker ≃ₗ[ℂ] (Fin ρ.dimension → Q.toLinearMap.ker) := {
    toFun u i := ⟨S u.val i, by rw [LinearMap.mem_ker, hinter, u.property, map_zero]; rfl⟩
    invFun v := ⟨S.symm (fun i ↦ (v i).val), by
      apply T.injective
      rw [map_zero]
      funext i
      rw [← hinter, S.apply_symm_apply]
      exact (v i).property⟩
    left_inv u := Subtype.ext (S.symm_apply_apply u.val)
    right_inv v := funext (fun i ↦ Subtype.ext (congrFun (S.apply_symm_apply _) i))
    map_add' u v := funext (fun i ↦ Subtype.ext (congrFun (S.map_add u.val v.val) i))
    map_smul' c u := funext (fun i ↦ Subtype.ext (congrFun (S.map_smul c u.val) i)) }
  let R : smoothSections (n := n) (r := F.rank) F.Fiber →ₗ[ℂ]
      (Fin ρ.dimension → smoothSections (n := m) (r := B.rank) B.Fiber ⧸
        Q.toLinearMap.range) :=
    (LinearMap.piMap (fun _ ↦ Q.toLinearMap.range.mkQ)).comp T.toLinearMap
  have hsurj : Function.Surjective R := by
    intro y
    choose v hv using fun i ↦ Q.toLinearMap.range.mkQ_surjective (y i)
    refine ⟨T.symm v, ?_⟩
    change (fun i ↦ Q.toLinearMap.range.mkQ (T (T.symm v) i)) = y
    rw [T.apply_symm_apply]
    exact funext hv
  have hRker : R.ker = P.toLinearMap.range := by
    ext v
    constructor
    · intro hv
      have hi (i : Fin ρ.dimension) : T v i ∈ Q.toLinearMap.range :=
        (Submodule.Quotient.mk_eq_zero (p := Q.toLinearMap.range)).mp (congrFun hv i)
      choose u hu using hi
      refine ⟨S.symm u, ?_⟩
      apply T.injective
      funext i
      rw [← hinter, S.apply_symm_apply]
      exact hu i
    · rintro ⟨u, rfl⟩
      funext i
      change Q.toLinearMap.range.mkQ (T (P.toLinearMap u) i) = 0
      rw [← hinter]
      exact (Submodule.Quotient.mk_eq_zero (p := Q.toLinearMap.range)).mpr ⟨S u i, rfl⟩
  let C := (Submodule.quotEquivOfEq _ _ hRker.symm).trans (R.quotKerEquivOfSurjective hsurj)
  have hC (v : smoothSections (n := n) (r := F.rank) F.Fiber) (i : Fin ρ.dimension) :
      C (P.toLinearMap.range.mkQ v) i = Q.toLinearMap.range.mkQ (T v i) := rfl
  obtain ⟨κ, χ, a, b, ha, hb⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  obtain ⟨κ₀, χ₀, a₀, b₀, ha₀, hb₀⟩ :=
    Q.exists_smoothKernelCokernelRepresentations IG τA τB hτA hτB hQg hQ
  let eK := (a.trans K).trans (LinearEquiv.piCongrRight fun _ ↦ a₀.symm)
  let eC := (b.trans C).trans (LinearEquiv.piCongrRight fun _ ↦ b₀.symm)
  have heK (g : G) (v : Fin κ.dimension → ℂ) (i : Fin ρ.dimension) :
      eK (κ.representation g v) i =
        ∑ j, ρ.representation g (Pi.single j 1) i • κ₀.representation g (eK v j) := by
    apply a₀.injective
    change a₀ (a₀.symm (K (a (κ.representation g v)) i)) = _
    rw [LinearEquiv.apply_symm_apply, map_sum]
    apply Subtype.ext
    change S (a (κ.representation g v)).val i = _
    rw [ha, hS]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    apply Finset.sum_congr rfl
    intro j _
    rw [ha₀]
    change _ = _ • τA.smoothSectionRepresentation IG hτA g
      (a₀ (a₀.symm (K (a v) j))).val
    rw [a₀.apply_symm_apply]
    rfl
  have heC (g : G) (v : Fin χ.dimension → ℂ) (i : Fin ρ.dimension) :
      eC (χ.representation g v) i =
        ∑ j, ρ.representation g (Pi.single j 1) i • χ₀.representation g (eC v j) := by
    obtain ⟨w, hw⟩ := P.toLinearMap.range.mkQ_surjective (b v)
    have hv : v = b.symm (P.toLinearMap.range.mkQ w) := by rw [hw, b.symm_apply_apply]
    apply b₀.injective
    change b₀ (b₀.symm (C (b (χ.representation g v)) i)) = _
    rw [LinearEquiv.apply_symm_apply, hv, hb, hC, hT, map_sum]
    simp only [map_smul, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change _ = _ • b₀ (χ₀.representation g
      (b₀.symm (C (b (b.symm (P.toLinearMap.range.mkQ w))) j)))
    rw [b.apply_symm_apply, hC, hb₀]
  -- Matrix-mixed finite coordinates are the original tensor representation, including rank zero.
  have classTensor (ζ ζ₀ : FiniteContinuousRepresentation G)
      (e : (Fin ζ.dimension → ℂ) ≃ₗ[ℂ] (Fin ρ.dimension → Fin ζ₀.dimension → ℂ))
      (he : ∀ g v i, e (ζ.representation g v) i =
        ∑ j, ρ.representation g (Pi.single j 1) i • ζ₀.representation g (e v j)) :
      finiteRepresentationClass ζ = finiteRepresentationClass ρ * finiteRepresentationClass ζ₀ := by
    let u := finiteTensorCoordinates ρ.dimension (Fin ζ₀.dimension → ℂ)
    let v := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension ζ₀.dimension
    let d := u.symm.trans v
    have hd (x : Fin ρ.dimension → ℂ) (y : Fin ζ₀.dimension → ℂ) :
        d (u (x ⊗ₜ[ℂ] y)) = v (x ⊗ₜ[ℂ] y) := by
      simp only [d, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have hmix (g : G) (w : Fin ρ.dimension → Fin ζ₀.dimension → ℂ) :
        d (finiteTensorRepresentation ρ ζ₀.representation g w) =
          (ρ.tensor ζ₀).representation g (d w) := by
      obtain ⟨z, rfl⟩ := u.surjective w
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        rw [finiteTensorRepresentation_tmul, hd, hd, FiniteContinuousRepresentation.tensor_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hiso : ζ.IsEquivalent (ρ.tensor ζ₀) := by
      refine ⟨ContRepresentation.Equiv.mk (e.trans d).toContinuousLinearEquiv ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro w
      change d (e (ζ.representation g w)) = (ρ.tensor ζ₀).representation g (d (e w))
      have hh : e (ζ.representation g w) =
          finiteTensorRepresentation ρ ζ₀.representation g (e w) := by
        funext i
        change e (ζ.representation g w) i =
          finiteTensorActionOperator ρ ζ₀.representation g (e w) i
        simp only [finiteTensorActionOperator,
          ContinuousLinearMap.pi_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply]
        change e (ζ.representation g w) i =
          ∑ j, ρ.representation g (Pi.single j 1) i • ζ₀.representation g (e w j)
        exact he g w i
      rw [hh, hmix]
    change finiteRepresentationClass ζ =
      representationMul G (finiteRepresentationClass ρ) (finiteRepresentationClass ζ₀)
    rw [representationMul_finiteClass]
    exact finiteRepresentationClass_eq_of_isEquivalent ζ (ρ.tensor ζ₀) hiso
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP κ χ a b ha hb,
    classTensor κ κ₀ eK heK, classTensor χ χ₀ eC heC,
    Q.smoothEquivariantAnalyticIndex_eq IG τA τB hτA hτB hQg hQ κ₀ χ₀ a₀ b₀ ha₀ hb₀,
    mul_sub]

end AtiyahSinger
