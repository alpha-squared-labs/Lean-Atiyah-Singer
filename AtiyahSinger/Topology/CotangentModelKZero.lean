/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentModelChange
public import AtiyahSinger.Topology.CompactSupportFunctoriality

/-!
# Compact-support K transport to a specified Euclidean cotangent model

Public module ID: M1747.

The original full-model cotangent space is compared with the Euclidean model
through the specified inverse-dual coordinate map. Its K transport is pullback
along the inverse homeomorphism. Only Hausdorffness of the base is required;
the target Euclidean manifold provides local compactness. Transferring these
property certificates leaves both native bundle topologies unchanged.

Sources: SG III.3 coordinate covariance and III.13 (13.7)--(13.8), together
with the proper-map compact-support functor from Karoubi II.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Inverse pullback along the specified cotangent model change, on the original K groups. -/
def cotangentKZeroLinearModel :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    let c := cotangentLinearModelHomeomorph e M
    letI := c.symm.t2Space
    letI := c.isOpenEmbedding.locallyCompactSpace
    CompactSupportKZero
        (TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)) ≃+
      CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) := by
  letI := linearModelChartedSpace e M
  letI := isManifold_linearModelChartedSpace e M
  let c := cotangentLinearModelHomeomorph e M
  -- These are proofs about the original topologies, not new topological structures.
  letI := c.symm.t2Space
  letI := c.isOpenEmbedding.locallyCompactSpace
  exact compactSupportKZeroHomeomorphEquiv c

end AtiyahSinger
