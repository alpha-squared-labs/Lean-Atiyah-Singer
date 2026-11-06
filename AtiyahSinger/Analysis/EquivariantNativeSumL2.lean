/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantL2
public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.SmoothBundleSumDecomposition

/-!
# Equivariance of an actual native smooth sum in integral L²

Public module ID: M0541.

The specified fiber sum and its original inverse projections determine the
same bounded L² equivalence. Its action comparison follows on the original
smooth sections and extends by density. All three given metrics are retained;
the sum identification need not be an isometry for these metrics.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n r₁ r₂ r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E₁ E₂ E : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₂)) E₂)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₂)) E₂]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₂)) E₂]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₂) E₂]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
    EquivariantStructure G E₁)
  (σ₂ : letI := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
    EquivariantStructure G E₂)
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ₁ : σ₁.IsSmooth (n := n) (r := r₁) IG)
  (hσ₂ : σ₂.IsSmooth (n := n) (r := r₂) IG)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (k₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
  (k₂ : SmoothHermitianMetric (n := n) (r := r₂) E₂)
  (k : SmoothHermitianMetric (n := n) (r := r) E)
  (hk₁ : letI := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
    ∀ (g : G) (x : M) (u v : E₁ x),
      k₁.pairing (g • x) (σ₁.linearMap g x u) (σ₁.linearMap g x v) = k₁.pairing x u v)
  (hk₂ : letI := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
    ∀ (g : G) (x : M) (u v : E₂ x),
      k₂.pairing (g • x) (σ₂.linearMap g x u) (σ₂.linearMap g x v) = k₂.pairing x u v)
  (hk : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      k.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) = k.pairing x u v)
  (hμ : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every specified native sum equivalence intertwines the three actual integral L² actions. -/
theorem l2Equiv_intertwines_of_smoothBundleSum
    (e : ∀ x, (E₁ x × E₂ x) ≃ₗ[ℂ] E x)
    (h₁ : IsSmoothBundleMap (n := n) (r := r₁) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))))
    (h₂ : IsSmoothBundleMap (n := n) (r := r₂) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))))
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
      letI := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
      letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (g : G) (x : M) (v : E₁ x × E₂ x),
        e (g • x) (σ₁.linearMap g x v.1, σ₂.linearMap g x v.2) =
          σ.linearMap g x (e x v)) :
    let p₁ := smoothSectionMap
      (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
      (isSmoothBundleMap_sumInverse e h₁ h₂).1
    let p₂ := smoothSectionMap
      (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
      (isSmoothBundleMap_sumInverse e h₁ h₂).2
    ∀ (U : k.L2SectionSpace μ ≃L[ℂ] (k₁.L2SectionSpace μ × k₂.L2SectionSpace μ))
      (_hU : ∀ u, U (k.smoothToL2 μ u) =
        (k₁.smoothToL2 μ (p₁ u), k₂.smoothToL2 μ (p₂ u))),
      let ρ := k.l2ContRepresentation μ IG σ hσ hk hμ
      let ρ₁ := k₁.l2ContRepresentation μ IG σ₁ hσ₁ hk₁ hμ
      let ρ₂ := k₂.l2ContRepresentation μ IG σ₂ hσ₂ hk₂ hμ
      ∀ (g : G) (v : k.L2SectionSpace μ), U (ρ g v) = (ρ₁ g (U v).1, ρ₂ g (U v).2) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
  let := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let p₁ := smoothSectionMap
    (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).1
  let p₂ := smoothSectionMap
    (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).2
  let R := σ.smoothSectionRepresentation IG hσ
  let R₁ := σ₁.smoothSectionRepresentation IG hσ₁
  let R₂ := σ₂.smoothSectionRepresentation IG hσ₂
  have heInv (g : G) (x : M) (u : E x) :
      (e (g • x)).symm (σ.linearMap g x u) =
        (σ₁.linearMap g x ((e x).symm u).1, σ₂.linearMap g x ((e x).symm u).2) := by
    apply (e (g • x)).injective
    rw [(e (g • x)).apply_symm_apply, he, (e x).apply_symm_apply]
  -- The actual inverse projections intertwine the original smooth section actions.
  have hp (g : G) (u : smoothSections (n := n) (r := r) E) :
      (p₁ (R g u), p₂ (R g u)) = (R₁ g (p₁ u), R₂ g (p₂ u)) := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      obtain ⟨y, rfl⟩ := MulAction.surjective g x
      change ((e (g • y)).symm (σ.sectionLinearMap g u.val (g • y))).1 =
        σ₁.sectionLinearMap g (p₁ u).val (g • y)
      rw [σ.sectionLinearMap_smul, σ₁.sectionLinearMap_smul]
      exact congrArg Prod.fst (heInv g y (u.val y))
    · apply Subtype.ext
      funext x
      obtain ⟨y, rfl⟩ := MulAction.surjective g x
      change ((e (g • y)).symm (σ.sectionLinearMap g u.val (g • y))).2 =
        σ₂.sectionLinearMap g (p₂ u).val (g • y)
      rw [σ.sectionLinearMap_smul, σ₂.sectionLinearMap_smul]
      exact congrArg Prod.snd (heInv g y (u.val y))
  dsimp only
  intro U hU
  let ρ := k.l2ContRepresentation μ IG σ hσ hk hμ
  let ρ₁ := k₁.l2ContRepresentation μ IG σ₁ hσ₁ hk₁ hμ
  let ρ₂ := k₂.l2ContRepresentation μ IG σ₂ hσ₂ hk₂ hμ
  intro g v
  let A := U.toContinuousLinearMap.comp (ρ g)
  let B := ((ρ₁ g).prodMap (ρ₂ g)).comp U.toContinuousLinearMap
  have hAB : (A : _ → _) = B := by
    apply (k.denseRange_smoothToL2 μ).equalizer A.continuous B.continuous
    funext u
    change U (ρ g (k.smoothToL2 μ u)) =
      (ρ₁ g (U (k.smoothToL2 μ u)).1, ρ₂ g (U (k.smoothToL2 μ u)).2)
    have hρ : ρ g (k.smoothToL2 μ u) = k.smoothToL2 μ (R g u) :=
      k.l2IsometryRepresentation_smoothToL2 μ IG σ hσ hk hμ g u
    rw [hρ, hU, hU]
    apply Prod.ext
    · change k₁.smoothToL2 μ (p₁ (R g u)) = ρ₁ g (k₁.smoothToL2 μ (p₁ u))
      rw [show p₁ (R g u) = R₁ g (p₁ u) from congrArg Prod.fst (hp g u)]
      exact (k₁.l2IsometryRepresentation_smoothToL2 μ IG σ₁ hσ₁ hk₁ hμ g _).symm
    · change k₂.smoothToL2 μ (p₂ (R g u)) = ρ₂ g (k₂.smoothToL2 μ (p₂ u))
      rw [show p₂ (R g u) = R₂ g (p₂ u) from congrArg Prod.snd (hp g u)]
      exact (k₂.l2IsometryRepresentation_smoothToL2 μ IG σ₂ hσ₂ hk₂ hμ g _).symm
  exact congrFun hAB v

end AtiyahSinger
