/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactTangentAnalyticExcision
public import AtiyahSinger.Geometry.FiniteDimensionalLocalDiffeomorph
public import AtiyahSinger.Geometry.OpenManifoldDerivative
public import AtiyahSinger.Topology.TangentEmbeddingOpenRestriction

/-!
# Locality of the analytic index of an embedding pushforward

Public module ID: M1030.

If two proper embeddings factor through the same embedding in a common
open neighborhood, their original tangent pushforwards have the same
analytic index. The geometric open-naturality squares are applied before
analytic excision, so the comparison retains the actual normal Thom maps.
This reduces the compact embedding argument to its normal sphere model.

Source: SG III.13 Property 2; this is the explicit common-neighborhood
reduction in its proof, with the original geometric pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold MeasureTheory TopologicalSpace Topology
open scoped ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n m : ℕ} {M O N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin m)) O]
  [IsManifold (𝓡 m) ∞ O] [T2Space O] [SecondCountableTopology O]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 m) ∞ N] [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin m)) P]
  [IsManifold (𝓡 m) ∞ P] [T2Space P] [SecondCountableTopology P] [CompactSpace P]
  [MeasurableSpace P] [BorelSpace P]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Both original geometric pushforwards are evaluated on the identical source class.
/-- The analytic index of an embedding pushforward depends only on its common open model. -/
theorem tangentAnalyticIndex_embedding_eq_of_commonOpen
    (f : ContMDiffMap (𝓡 n) (𝓡 m) M N ∞)
    (hf : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ f) (hpf : IsProperMap f)
    (g : ContMDiffMap (𝓡 n) (𝓡 m) M P ∞)
    (hg : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ g) (hpg : IsProperMap g)
    (s : ContMDiffMap (𝓡 n) (𝓡 m) M O ∞)
    (hs : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ s) (hps : IsProperMap s)
    (U : Opens N) (V : Opens P)
    (e : O ≃ₘ⟮𝓡 m, 𝓡 m⟯ U) (d : O ≃ₘ⟮𝓡 m, 𝓡 m⟯ V)
    (he : ∀ x : M, (e (s x) : N) = f x)
    (hd : ∀ x : M, (d (s x) : P) = g x)
    (μ : Measure N) [IsSmoothPositiveMeasure (n := m) μ]
    (ν : Measure P) [IsSmoothPositiveMeasure (n := m) ν] :
    letI : T2Space (TangentBundle (𝓡 n) M) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
    letI : T2Space (TangentBundle (𝓡 m) N) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) N).1
    letI : T2Space (TangentBundle (𝓡 m) P) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) P).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
    letI : LocallyCompactSpace (TangentBundle (𝓡 m) N) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) _
    letI : LocallyCompactSpace (TangentBundle (𝓡 m) P) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) _
    ∀ u : CompactSupportKZero (TangentBundle (𝓡 n) M),
      tangentAnalyticIndex μ (tangentEmbeddingPushforward f hf hpf u) =
        tangentAnalyticIndex ν (tangentEmbeddingPushforward g hg hpg u) := by
  classical
  let : T2Space (TangentBundle (𝓡 n) M) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
  let : T2Space (TangentBundle (𝓡 m) O) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) O).1
  let : T2Space (TangentBundle (𝓡 m) N) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) N).1
  let : T2Space (TangentBundle (𝓡 m) P) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) P).1
  let : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
  let : LocallyCompactSpace (TangentBundle (𝓡 m) O) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) _
  let : LocallyCompactSpace (TangentBundle (𝓡 m) N) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) _
  let : LocallyCompactSpace (TangentBundle (𝓡 m) P) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) _
  intro u
  let j : ContMDiffMap (𝓡 m) (𝓡 m) O N ∞ :=
    ⟨fun x ↦ (e x : N), contMDiff_subtype_val.comp e.contMDiff⟩
  let k : ContMDiffMap (𝓡 m) (𝓡 m) O P ∞ :=
    ⟨fun x ↦ (d x : P), contMDiff_subtype_val.comp d.contMDiff⟩
  -- The inherited open inclusions have identity derivative in the same native charts.
  have hj : IsLocalDiffeomorph (𝓡 m) (𝓡 m) ∞ j := by
    apply isLocalDiffeomorph_of_isInvertible_mfderiv j
    intro x
    have hD : mfderiv (𝓡 m) (𝓡 m) j x = mfderiv (𝓡 m) (𝓡 m) e x := by
      change mfderiv (𝓡 m) (𝓡 m) ((Subtype.val : U → N) ∘ e) x = _
      rw [mfderiv_comp x ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (e x))
        (e.contMDiff.mdifferentiable (by simp) x), mfderiv_openSubtype_val]
      exact ContinuousLinearMap.id_comp _
    rw [hD]
    exact e.isInvertible_mfderiv (by simp)
  have hk : IsLocalDiffeomorph (𝓡 m) (𝓡 m) ∞ k := by
    apply isLocalDiffeomorph_of_isInvertible_mfderiv k
    intro x
    have hD : mfderiv (𝓡 m) (𝓡 m) k x = mfderiv (𝓡 m) (𝓡 m) d x := by
      change mfderiv (𝓡 m) (𝓡 m) ((Subtype.val : V → P) ∘ d) x = _
      rw [mfderiv_comp x ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (d x))
        (d.contMDiff.mdifferentiable (by simp) x), mfderiv_openSubtype_val]
      exact ContinuousLinearMap.id_comp _
    rw [hD]
    exact d.isInvertible_mfderiv (by simp)
  have hinj : Function.Injective j := Subtype.val_injective.comp e.injective
  have hkinj : Function.Injective k := Subtype.val_injective.comp d.injective
  have hTj := isOpenEmbedding_smoothTangentMap j hj hinj
  have hTk := isOpenEmbedding_smoothTangentMap k hk hkinj
  let idM : ContMDiffMap (𝓡 n) (𝓡 n) M M ∞ := ⟨id, contMDiff_id⟩
  have hid : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ idM :=
    (Diffeomorph.refl (𝓡 n) M ∞).isLocalDiffeomorph
  -- The two geometric Thom squares share the same proper embedding s and identity on M.
  have hpushF := tangentEmbeddingPushforward_open_naturality f hf hpf s hs hps
    idM hid Function.injective_id j hj hinj (fun x ↦ (he x).symm)
  have hpushG := tangentEmbeddingPushforward_open_naturality g hg hpg s hs hps
    idM hid Function.injective_id k hk hkinj (fun x ↦ (hd x).symm)
  have hTid : (smoothTangentMap idM : TangentBundle (𝓡 n) M → TangentBundle (𝓡 n) M) =
      id := by
    funext z
    change tangentMap (𝓡 n) (𝓡 n) id z = z
    simp only [tangentMap, mfderiv_id]
    rfl
  simp only [hTid, compactSupportKZeroOpenPushforward_id, AddMonoidHom.comp_id]
    at hpushF hpushG
  -- Analytic excision is evaluated only after the same geometric source class has been fixed.
  have hex := DFunLike.congr_fun
    (tangentAnalyticIndex_excision_of_compact_targets μ ν U V e d hTj hTk)
      (tangentEmbeddingPushforward s hs hps u)
  rw [← hpushF, ← hpushG]
  exact hex

end AtiyahSinger
