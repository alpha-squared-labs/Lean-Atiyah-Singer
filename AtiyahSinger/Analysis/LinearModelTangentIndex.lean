/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LinearModelAnalyticIndex
public import AtiyahSinger.Analysis.TangentAnalyticIndex
public import AtiyahSinger.Geometry.LinearModelMusical

/-!
# Analytic index and the actual tangent map of a full model change

Public module ID: M0782.

The full-model metric musical map and the specified Euclidean model change
form an exact square with the corresponding tangent map. Apply the original
compact-support functor and component analytic index to this same square.
The result identifies the full-model index with the tangent index in the
specified Euclidean atlas, for any supplied smooth positive density.

This is a model-comparison supplement used by the normal sphere proof of
SG III.13 Property 2. No embedding-index or final index theorem is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Topology
open scoped Manifold ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  t2Space_cotangent locallyCompactSpace_cotangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

set_option maxSynthPendingDepth 45 in
set_option maxHeartbeats 1800000 in
-- The extended limit accommodates the full-model tangent index and supplied-metric transport
-- comparison.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tangent model map intertwines the supplied-metric full-model analytic index. -/
theorem exists_linearModelTangentIndex_comparison
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (μ : Measure M) (hμ : letI := linearModelChartedSpace e M
      IsSmoothPositiveMeasure (n := n) μ) :
    letI : FiniteDimensional ℝ E := .of_injective e.toLinearMap e.injective
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    letI := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
    letI := hμ
    let d := (exists_tangentMusical_diffeomorph h).choose
    letI : T2Space (TangentBundle 𝓘(ℝ, E) M) := (tangentBundle_topology E M).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M) :=
      ChartedSpace.locallyCompactSpace (E × E) _
    let c := cotangentLinearModelHomeomorph e M
    letI := c.symm.t2Space
    letI := c.isOpenEmbedding.locallyCompactSpace
    letI : T2Space (TangentBundle (𝓡 n) M) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
    ∃ t : TangentBundle 𝓘(ℝ, E) M ≃ₜ TangentBundle (𝓡 n) M,
      (∀ z, t z = ⟨z.proj, e z.snd⟩) ∧
        ∀ u : CompactSupportKZero (TangentBundle 𝓘(ℝ, E) M),
          analyticIndexLinearModel e M (compactSupportKZeroHomeomorph d.toHomeomorph u) =
            tangentAnalyticIndex μ (compactSupportKZeroHomeomorph t u) := by
  classical
  let : FiniteDimensional ℝ E := .of_injective e.toLinearMap e.injective
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let := hμ
  let d := (exists_tangentMusical_diffeomorph h).choose
  let c := cotangentLinearModelHomeomorph e M
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := (tangentBundle_topology E M).1
  let : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M) :=
    ChartedSpace.locallyCompactSpace (E × E) _
  let := c.symm.t2Space
  let := c.isOpenEmbedding.locallyCompactSpace
  let : T2Space (TangentBundle (𝓡 n) M) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
  let : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
  obtain ⟨g, t, ht, hsquare⟩ := exists_linearModelMusical_comparison e M h
  refine ⟨t, ht, ?_⟩
  intro u
  -- Apply the same inverse-pullback functor to the exact original homeomorphism square.
  have hK : (compactSupportKZeroHomeomorph c).comp
      (compactSupportKZeroHomeomorph d.toHomeomorph) =
      (compactSupportKZeroHomeomorph g.flatHomeomorph).comp
        (compactSupportKZeroHomeomorph t) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph c,
      ← compactSupportKZeroOpenPushforward_homeomorph d.toHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph g.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph t,
      ← compactSupportKZeroOpenPushforward_comp, ← compactSupportKZeroOpenPushforward_comp]
    congr 1
    exact congrArg (fun h : _ ≃ₜ _ ↦ (h : _ → _)) hsquare
  -- Both index expressions now use the same Euclidean metric and the supplied density.
  rw [analyticIndexLinearModel_eq_comp e M μ hμ, tangentAnalyticIndex_eq μ g]
  exact congrArg (analyticIndexOfComponents μ) (DFunLike.congr_fun hK u)

end AtiyahSinger
