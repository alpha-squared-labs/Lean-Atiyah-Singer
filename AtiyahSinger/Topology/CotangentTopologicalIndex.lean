/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactTopologicalIndex
public import AtiyahSinger.Topology.CotangentEmbeddingPushforward

/-!
# The topological index on the actual cotangent K group

Public module ID: M1750.

SG III.13 uses tangent bundles for the topological index and cotangent bundles
for the analytic index. The metric identification is explicit in SG II.5.
Here the original positive Bott normalization is transported by that actual
metric identification. The supplied-metric formula removes the implementation
choice, and the embedding formula uses the same source and target metrics as
the actual cotangent pushforward. No new orientation convention is introduced.

Sources: SG II.5, printed p.113, and III.13, Definition 13.1 and the discussion
of the analytic index, printed pp.243--247. The two comparison proofs retain the
original metric and embedding pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold
open scoped ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable (n : ℕ) (M : Type*) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The topological index on covectors, with its metric choice internal to the construction. -/
def cotangentTopologicalIndex :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+ ℤ := by
  let g : SmoothTangentMetric (n := n) (M := M) :=
    Classical.choice SmoothTangentMetric.nonempty
  exact (topologicalIndex (EuclideanSpace ℝ (Fin n)) M).comp
    (tangentCotangentKZeroEquiv g).symm.toAddMonoidHom

variable {n M}

/-- Every supplied smooth metric gives the same cotangent topological index. -/
theorem cotangentTopologicalIndex_eq (g : SmoothTangentMetric (n := n) (M := M)) :
    cotangentTopologicalIndex n M =
      (topologicalIndex (EuclideanSpace ℝ (Fin n)) M).comp
        (tangentCotangentKZeroEquiv g).symm.toAddMonoidHom := by
  -- Substitute the supplied metric into the same inverse musical K equivalence.
  dsimp only [cotangentTopologicalIndex]
  rw [tangentCotangentKZeroEquiv_independent_metric
    (Classical.choice SmoothTangentMetric.nonempty) g]

variable {m : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]

/-- The cotangent topological index is natural for the transported actual embedding pushforward. -/
theorem cotangentTopologicalIndex_pushforward
    (f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (hp : IsProperMap f)
    (g : SmoothTangentMetric (n := n) (M := M))
    (h : SmoothTangentMetric (n := m) (M := N)) :
    (cotangentTopologicalIndex m N).comp (cotangentEmbeddingPushforward f hf hp g h) =
      cotangentTopologicalIndex n M := by
  -- Retain the supplied metrics at both ends before cancelling the middle transport.
  rw [cotangentTopologicalIndex_eq h, cotangentTopologicalIndex_eq g]
  unfold cotangentEmbeddingPushforward
  have hpush := topologicalIndex_pushforward f hf hp
  ext a
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, AddEquiv.symm_apply_apply]
  exact DFunLike.congr_fun hpush ((tangentCotangentKZeroEquiv g).symm a)

end AtiyahSinger
