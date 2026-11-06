/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.TangentAnalyticIndex
public import AtiyahSinger.Analysis.UnrestrictedAnalyticExcision
public import AtiyahSinger.Topology.TangentCotangentOpenNaturality

/-!
# Excision for the original tangent analytic index

Public module ID: M0364.

Apply cotangent excision to the musical image of one source tangent class.
Musical naturality identifies both images with the actual differential open
pushforwards. Independent ambient densities and the original tangent index
maps remain unchanged. This is the analytic comparison needed after the
normal Thom and sphere classes have been identified geometrically.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] tangentBundleFullChartedSpace

variable {n : ℕ} {O M N : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold (𝓡 n) ∞ O] [T2Space O] [SecondCountableTopology O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One original tangent class has equal indices after the two actual open differential maps. -/
theorem tangentAnalyticIndex_excision_of_compact_targets
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U) (g : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ V)
    (hTf : IsOpenEmbedding (tangentMap (𝓡 n) (𝓡 n) (fun x : O ↦ (f x : M))))
    (hTg : IsOpenEmbedding (tangentMap (𝓡 n) (𝓡 n) (fun x : O ↦ (g x : N)))) :
    letI : T2Space (TangentBundle (𝓡 n) O) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) O).1
    letI : T2Space (TangentBundle (𝓡 n) M) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
    letI : T2Space (TangentBundle (𝓡 n) N) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) N).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 n) O) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
    letI : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
    letI : LocallyCompactSpace (TangentBundle (𝓡 n) N) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
    (tangentAnalyticIndex μ).comp (compactSupportKZeroOpenPushforward
      (tangentMap (𝓡 n) (𝓡 n) (fun x : O ↦ (f x : M))) hTf) =
        (tangentAnalyticIndex ν).comp (compactSupportKZeroOpenPushforward
          (tangentMap (𝓡 n) (𝓡 n) (fun x : O ↦ (g x : N))) hTg) := by
  classical
  let : T2Space (TangentBundle (𝓡 n) O) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) O).1
  let : T2Space (TangentBundle (𝓡 n) M) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
  let : T2Space (TangentBundle (𝓡 n) N) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) N).1
  let : LocallyCompactSpace (TangentBundle (𝓡 n) O) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
  let : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
  let : LocallyCompactSpace (TangentBundle (𝓡 n) N) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
  let qO : SmoothTangentMetric (n := n) (M := O) :=
    Classical.choice SmoothTangentMetric.nonempty
  let qM : SmoothTangentMetric (n := n) (M := M) :=
    Classical.choice SmoothTangentMetric.nonempty
  let qN : SmoothTangentMetric (n := n) (M := N) :=
    Classical.choice SmoothTangentMetric.nonempty
  obtain ⟨_, hfK⟩ := tangentCotangentKZeroEquiv_openEmbedding U f qO qM
  obtain ⟨_, hgK⟩ := tangentCotangentKZeroEquiv_openEmbedding V g qO qN
  apply AddMonoidHom.ext
  intro u
  -- The same musical image is the input to both original cotangent extensions.
  have hindex := DFunLike.congr_fun
    (analyticIndexOfComponents_excision_of_openSource μ ν U V f g)
      ((tangentCotangentKZeroEquiv qO) u)
  have hfValue := DFunLike.congr_fun hfK u
  have hgValue := DFunLike.congr_fun hgK u
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass] at hindex hfValue hgValue
  rw [hfValue, hgValue] at hindex
  -- Any chosen ambient metric computes the original tangent index, with its given density.
  rw [tangentAnalyticIndex_eq μ qM, tangentAnalyticIndex_eq ν qN]
  exact hindex

end AtiyahSinger
