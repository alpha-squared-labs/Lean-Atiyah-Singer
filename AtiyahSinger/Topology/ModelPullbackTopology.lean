/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Retyping commutes with the original pullback topology

Public module ID: M1961.

Pulling back the original modeled total space and then changing its phantom
model to `Unit` gives exactly the topology obtained by first retyping the
original bundle and then pulling it back. Both constructions use the same
base point and fiber vector. This interface permits original flag coordinate
maps to be used with the native projective pullback without a new topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace V E)] (f : Y → X)

local instance : ∀ y, NormedAddCommGroup ((f *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))

local instance : ∀ y, NormedSpace ℂ ((f *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))

set_option linter.unusedSectionVars false in
/-- Phantom-model retyping and original bundle pullback give the same total-space topology. -/
theorem modelTopology_pullback :
    modelTopology V (f *ᵖ E) =
      letI := modelTopology V E
      (inferInstance : TopologicalSpace (TotalSpace Unit (f *ᵖ E))) := by
  -- Both induced topologies record the new base point and the same original lifted vector.
  simp only [modelTopology, inferInstance, Pullback.TotalSpace.topologicalSpace,
    pullbackTopology_def, induced_inf, induced_compose]
  rfl

end AtiyahSinger.ComplexBundle
