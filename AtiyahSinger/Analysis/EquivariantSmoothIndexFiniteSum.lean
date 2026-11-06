/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteRepresentationSum
public import AtiyahSinger.Analysis.SmoothEquivariantIndex
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Finite additivity of the full smooth equivariant index

Public module ID: M0574.

A specified equivariant decomposition of the actual section map identifies its
kernel and quotient cokernel with the finite products of the given operators'
defects. Their original finite continuous representation classes therefore add.
This is the representation-valued finite decomposition used for clopen assembly;
no equality of virtual representations is inferred from their dimensions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {n m k : ℕ} {M : Type*} {N : Fin k → Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin m)) (N i)]
  [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (N i)]
  [∀ i, CompactSpace (N i)] [∀ i, T2Space (N i)] [∀ i, SecondCountableTopology (N i)]
  [∀ i, MeasurableSpace (N i)] [∀ i, BorelSpace (N i)]
  [∀ i, MulAction G (N i)] [∀ i, ContinuousSMul G (N i)]
  [∀ i, ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G (N i)]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : ∀ i, SmoothFiniteComplexBundle (n := m) (N i))
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (τA : ∀ i, letI := modelTopology (EuclideanSpace ℂ (Fin (A i).rank)) (A i).Fiber
    EquivariantStructure G (A i).Fiber)
  (τB : ∀ i, letI := modelTopology (EuclideanSpace ℂ (Fin (B i).rank)) (B i).Fiber
    EquivariantStructure G (B i).Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (hτA : ∀ i, (τA i).IsSmooth (n := m) (r := (A i).rank) IG)
  (hτB : ∀ i, (τB i).IsSmooth (n := m) (r := (B i).rank) IG)

/-- An actual finite equivariant decomposition adds the original smooth indices. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_sum_of_sectionEquiv
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : ∀ i, Measure (N i)) [∀ i, IsSmoothPositiveMeasure (n := m) (ν i)]
    {l : ℝ} {l' : Fin k → ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ l)
    (Q : ∀ i, PseudodifferentialOperator (n := m) (r := (A i).rank) (q := (B i).rank)
      (A i).Fiber (B i).Fiber (ν i) (l' i))
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
    (hQg : ∀ i, (Q i).IsEquivariant IG (τA i) (τB i) (hτA i) (hτB i))
    (hQ : ∀ i, (Q i).IsElliptic)
    (S : smoothSections (n := n) (r := E.rank) E.Fiber ≃ₗ[ℂ]
      ∀ i, smoothSections (n := m) (r := (A i).rank) (A i).Fiber)
    (T : smoothSections (n := n) (r := F.rank) F.Fiber ≃ₗ[ℂ]
      ∀ i, smoothSections (n := m) (r := (B i).rank) (B i).Fiber)
    (hS : ∀ g u i, S (σE.smoothSectionRepresentation IG hσE g u) i =
      (τA i).smoothSectionRepresentation IG (hτA i) g (S u i))
    (hT : ∀ g v i, T (σF.smoothSectionRepresentation IG hσF g v) i =
      (τB i).smoothSectionRepresentation IG (hτB i) g (T v i))
    (hinter : ∀ u i, (Q i).toLinearMap (S u i) = T (P.toLinearMap u) i) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
      ∑ i, (Q i).smoothEquivariantAnalyticIndex
        IG (τA i) (τB i) (hτA i) (hτB i) (hQg i) (hQ i) := by
  classical
  -- The source decomposition restricts to the actual finite product of kernels.
  let K : P.toLinearMap.ker ≃ₗ[ℂ] ∀ i, (Q i).toLinearMap.ker := {
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
  -- Coordinate quotient maps have precisely the original global range as their common kernel.
  let R : smoothSections (n := n) (r := F.rank) F.Fiber →ₗ[ℂ]
      ∀ i, smoothSections (n := m) (r := (B i).rank) (B i).Fiber ⧸
        (Q i).toLinearMap.range :=
    (LinearMap.piMap (fun i ↦ (Q i).toLinearMap.range.mkQ)).comp T.toLinearMap
  have hsurj : Function.Surjective R := by
    intro y
    choose v hv using fun i ↦ (Q i).toLinearMap.range.mkQ_surjective (y i)
    refine ⟨T.symm v, ?_⟩
    change (fun i ↦ (Q i).toLinearMap.range.mkQ (T (T.symm v) i)) = y
    rw [T.apply_symm_apply]
    exact funext hv
  have hRker : R.ker = P.toLinearMap.range := by
    ext v
    constructor
    · intro hv
      have hi (i : Fin k) : T v i ∈ (Q i).toLinearMap.range :=
        (Submodule.Quotient.mk_eq_zero (p := (Q i).toLinearMap.range)).mp (congrFun hv i)
      choose u hu using hi
      refine ⟨S.symm u, ?_⟩
      apply T.injective
      funext i
      rw [← hinter, S.apply_symm_apply]
      exact hu i
    · rintro ⟨u, rfl⟩
      funext i
      change (Q i).toLinearMap.range.mkQ (T (P.toLinearMap u) i) = 0
      rw [← hinter]
      exact (Submodule.Quotient.mk_eq_zero (p := (Q i).toLinearMap.range)).mpr ⟨S u i, rfl⟩
  let C := (Submodule.quotEquivOfEq _ _ hRker.symm).trans (R.quotKerEquivOfSurjective hsurj)
  have hC (v : smoothSections (n := n) (r := F.rank) F.Fiber) (i : Fin k) :
      C (P.toLinearMap.range.mkQ v) i = (Q i).toLinearMap.range.mkQ (T v i) := rfl
  obtain ⟨ρ, τ, a, b, ha, hb⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  choose ρi τi ai bi hai hbi using fun i ↦
    (Q i).exists_smoothKernelCokernelRepresentations
      IG (τA i) (τB i) (hτA i) (hτB i) (hQg i) (hQ i)
  -- The same finite coordinates identify the full actions on kernels and quotients.
  let eK := (a.trans K).trans (LinearEquiv.piCongrRight fun i ↦ (ai i).symm)
  let eC := (b.trans C).trans (LinearEquiv.piCongrRight fun i ↦ (bi i).symm)
  have heK (g : G) (v : Fin ρ.dimension → ℂ) (i : Fin k) :
      eK (ρ.representation g v) i = (ρi i).representation g (eK v i) := by
    apply (ai i).injective
    change ai i ((ai i).symm (K (a (ρ.representation g v)) i)) =
      ai i ((ρi i).representation g ((ai i).symm (K (a v) i)))
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change S (a (ρ.representation g v)).val i = _
    rw [ha, hS, hai, LinearEquiv.apply_symm_apply]
    rfl
  have heC (g : G) (v : Fin τ.dimension → ℂ) (i : Fin k) :
      eC (τ.representation g v) i = (τi i).representation g (eC v i) := by
    obtain ⟨w, hw⟩ := P.toLinearMap.range.mkQ_surjective (b v)
    have hv : v = b.symm (P.toLinearMap.range.mkQ w) := by rw [hw, b.symm_apply_apply]
    apply (bi i).injective
    change bi i ((bi i).symm (C (b (τ.representation g v)) i)) =
      bi i ((τi i).representation g ((bi i).symm (C (b v) i)))
    rw [LinearEquiv.apply_symm_apply, hv, hb, hC, hT,
      b.apply_symm_apply, hC, hbi]
  -- A true intertwining with a finite product gives its sum class in the original R(G).
  have classPi (ζ : FiniteContinuousRepresentation G)
      (ζi : Fin k → FiniteContinuousRepresentation G)
      (e : (Fin ζ.dimension → ℂ) ≃ₗ[ℂ] ∀ i, Fin (ζi i).dimension → ℂ)
      (he : ∀ g v i, e (ζ.representation g v) i = (ζi i).representation g (e v i)) :
      finiteRepresentationClass ζ = ∑ i, finiteRepresentationClass (ζi i) := by
    obtain ⟨ζ', d, hd, hclass⟩ := exists_finiteContinuousRepresentation_finPi k ζi
    have hiso : ζ.IsEquivalent ζ' := by
      refine ⟨ContRepresentation.Equiv.mk (e.trans d.symm).toContinuousLinearEquiv ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro v
      change d.symm (e (ζ.representation g v)) = ζ'.representation g (d.symm (e v))
      apply d.injective
      rw [d.apply_symm_apply]
      funext i
      rw [he, hd, d.apply_symm_apply]
    exact (finiteRepresentationClass_eq_of_isEquivalent ζ ζ' hiso).trans hclass
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP ρ τ a b ha hb,
    classPi ρ ρi eK heK, classPi τ τi eC heC, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact ((Q i).smoothEquivariantAnalyticIndex_eq
    IG (τA i) (τB i) (hτA i) (hτB i) (hQg i) (hQ i)
    (ρi i) (τi i) (ai i) (bi i) (hai i) (hbi i)).symm

end AtiyahSinger
