/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Connected components with their inherited manifold structures

Public module ID: M1298.

D01/A10: components are the actual fibers of mathlib's connected-component
quotient. Local connectedness makes them open, so their charts are inherited.
Any ambient smooth-manifold structure restricts to these opens. Connectedness
and compactness below only adapt
existing mathlib results to this open-subspace presentation. Finiteness of the
component set is reused directly from mathlib when needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- A connected component as an open submanifold, retaining the original base points. -/
def manifoldComponent (c : ConnectedComponents M) : Opens M :=
  letI := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  ⟨ConnectedComponents.mk ⁻¹' {c},
    (isOpen_discrete {c}).preimage ConnectedComponents.continuous_coe⟩

/-- The inherited open-subspace presentation is a connected space. -/
instance connectedSpace_manifoldComponent (c : ConnectedComponents M) :
    ConnectedSpace (manifoldComponent (n := n) c) := by
  -- Identify the quotient fiber with a connected component from mathlib.
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  apply isConnected_iff_connectedSpace.mp
  change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- A component of a compact manifold is compact with the original subspace topology. -/
instance compactSpace_manifoldComponent [CompactSpace M] (c : ConnectedComponents M) :
    CompactSpace (manifoldComponent (n := n) c) := by
  -- Components are closed; use the existing compact-subspace certificate.
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  apply isCompact_iff_compactSpace.mp
  change IsCompact (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent.isCompact

end AtiyahSinger
