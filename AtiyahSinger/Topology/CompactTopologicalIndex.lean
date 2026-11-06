/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.TopologicalIndexIndependence

/-!
# The embedding-independent topological index of a compact smooth manifold

Public module ID: M1689.

Select one actual proper Euclidean embedding from the compact Whitney existence
theorem and use its already defined index homomorphism. The comparison theorem
identifies this map with the index of every supplied embedding. Thus the choice
is implementation data, not an additional mathematical input of the public map.
Composition gives its naturality for the actual tangent embedding pushforward.

Source: SG III.13, Definition 13.1 and its independence argument, printed p.244
/ PDF p.256. The group-level map here applies to arbitrary compact-support
tangent K classes. Identifying it with an analytic index or a characteristic
number is a further theorem, not part of this construction. The comparison
and naturality proofs use the actual embedding-independence and composition interfaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

/-- One dimension and actual embedding, selected together from the same existence witness. -/
def compactEuclideanEmbedding :
    Σ n : ℕ, { f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞ //
      IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f ∧ IsProperMap f } := by
  let h := exists_proper_smoothEmbedding_euclidean (E := E) (M := M)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

variable [SecondCountableTopology M]

/-- The topological index on the original compact-support tangent K group. -/
def topologicalIndex :
    letI : T2Space (TangentBundle 𝓘(ℝ, E) M) := (tangentBundle_topology E M).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M) :=
      ChartedSpace.locallyCompactSpace (E × E) (TangentBundle 𝓘(ℝ, E) M)
    CompactSupportKZero (TangentBundle 𝓘(ℝ, E) M) →+ ℤ := by
  let e := compactEuclideanEmbedding E M
  exact topologicalIndexOfEmbedding e.2.1 e.2.2.1 e.2.2.2

variable {E M}

/-- The chosen public index agrees with the formula for every actual proper Euclidean embedding. -/
theorem topologicalIndex_eq_of_embedding {n : ℕ}
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hp : IsProperMap f) :
    topologicalIndex E M = topologicalIndexOfEmbedding f hf hp := by
  -- The dimension and all embedding certificates come from one original chosen witness.
  let e := compactEuclideanEmbedding E M
  exact topologicalIndexOfEmbedding_eq e.2.1 f e.2.2.1 hf e.2.2.2 hp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T2Space N] [CompactSpace N] [SecondCountableTopology N]

/-- The compact topological index is natural for the actual tangent embedding pushforward. -/
theorem topologicalIndex_pushforward
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (hp : IsProperMap f) :
    (topologicalIndex F N).comp (tangentEmbeddingPushforward f hf hp) =
      topologicalIndex E M := by
  -- Compose the supplied map with the same actual Euclidean embedding chosen for N.
  let e := compactEuclideanEmbedding F N
  let hcomp := isSmoothEmbedding_comp f e.2.1 hf e.2.2.1
  have hsource := topologicalIndex_eq_of_embedding (e.2.1.comp f) hcomp (e.2.2.2.comp hp)
  change (topologicalIndexOfEmbedding e.2.1 e.2.2.1 e.2.2.2).comp
    (tangentEmbeddingPushforward f hf hp) = topologicalIndex E M
  apply Eq.trans _ hsource.symm
  -- Actual composition preserves the specified target Bott coordinate.
  dsimp only [topologicalIndexOfEmbedding]
  rw [tangentEmbeddingPushforward_comp f e.2.1 hf e.2.2.1 hp e.2.2.2]
  rfl

end AtiyahSinger
