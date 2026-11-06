/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantMetricL2Average

/-!
# Averaging on a fixed invariant domain realization

Public module ID: M0500.

The actual smooth PDO average realizes strong unitary averaging on any fixed
normed domain with a dense equivariant smooth inclusion. In particular this
applies to the original Hilbert graph domain of the product operator, without
asserting that an arbitrary atlas Sobolev norm is invariant.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

variable {m : ℝ}
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

/-- The original PDO average equals strong averaging on the same fixed invariant domain. -/
theorem boundedRealization_average
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (γ : G →* (X ≃ₗᵢ[ℂ] X))
    (hγ : Continuous (fun p : G × X ↦ γ p.1 p.2))
    (j : smoothSections (n := n) (r := r) E →ₗ[ℂ] X) (hj : DenseRange j)
    (hjg : ∀ (g : G) (u : smoothSections (n := n) (r := r) E),
      γ g (j u) = j (σE.smoothSectionRepresentation IG hσE g u))
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (T Tavg : X →L[ℂ] k.L2SectionSpace μ)
    (hT : ∀ u, T (j u) = k.smoothToL2 μ (P.toLinearMap u))
    (hTavg : ∀ u, Tavg (j u) =
      k.smoothToL2 μ ((P.average IG σE σF hσE hσF).toLinearMap u)) :
    let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
    let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
    Tavg = unitaryOperatorAverage ν γ
      (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant) hγ
      (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant) T := by
  classical
  dsimp only
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  let τ := k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant
  let hτ := k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  -- Density concerns this original domain; the group acts by its supplied fixed norm.
  apply DFunLike.coe_injective
  apply hj.equalizer Tavg.continuous (unitaryOperatorAverage ν γ τ hγ hτ T).continuous
  funext u
  change Tavg (j u) = unitaryOperatorAverage ν γ τ hγ hτ T (j u)
  rw [hTavg]
  change k.smoothToL2 μ ((P.average IG σE σF hσE hσF).toLinearMap u) =
    ∫ g, τ g (T (γ g⁻¹ (j u))) ∂ν
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let R := σE.smoothSectionRepresentation IG hσE
  let S := σF.smoothSectionRepresentation IG hσF
  let f (g : G) := B.smoothSectionEquiv.symm (S g (P.toLinearMap (R g⁻¹ u)))
  have hf : Continuous f := by
    have hi := (A.continuous_smoothSectionAction_of_isManifold IG σE hσE).comp
      (continuous_inv.prodMk (continuous_const (y := A.smoothSectionEquiv.symm u)))
    have hp := (P.continuous_smoothSectionMap A B).comp hi
    exact (B.continuous_smoothSectionAction_of_isManifold IG σF hσF).comp
      (continuous_id.prodMk hp)
  -- Evaluate the same conjugated operator before taking either of the two integrals.
  have heval (g : G) : τ g (T (γ g⁻¹ (j u))) =
      k.smoothToL2 μ (B.smoothSectionEquiv (f g)) := by
    rw [hjg, hT]
    exact k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF
      kInvariant hμInvariant g (P.toLinearMap (R g⁻¹ u))
  rw [show (∫ g, τ g (T (γ g⁻¹ (j u))) ∂ν) =
      ∫ g, k.smoothToL2 μ (B.smoothSectionEquiv (f g)) ∂ν from
    integral_congr_ae (Filter.Eventually.of_forall heval)]
  exact k.smoothToL2_integral μ B ν f hf
    ((P.average IG σE σF hσE hσF).toLinearMap u)
    (fun x ↦ P.average_apply IG σE σF hσE hσF u x)

end AtiyahSinger.PseudodifferentialOperator
