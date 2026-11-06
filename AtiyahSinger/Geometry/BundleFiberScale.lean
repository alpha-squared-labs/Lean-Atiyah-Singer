/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Scalar dilation in the original vector-bundle topology

Public module ID: M1106.

Joint continuity of scalar dilation is checked in the original linear frames.
This operation is used on both sides of the tubular transition map when
deforming it to its normal derivative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology

variable {B F : Type*} {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Scalar dilation keeps the original base point and scales only its fiber vector. -/
def bundleFiberScale (a : ℝ) (z : TotalSpace F V) : TotalSpace F V :=
  ⟨z.proj, a • z.2⟩

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Fiber dilation is jointly continuous in its scalar and its original total-space argument. -/
theorem continuous_bundleFiberScale_of_vectorBundle :
    Continuous (fun p : ℝ × TotalSpace F V ↦ bundleFiberScale p.1 p.2) := by
  have hb : Continuous (fun z : ℝ × TotalSpace F V ↦ z.2.proj) :=
    (FiberBundle.continuous_proj F V).comp continuous_snd
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  let e := trivializationAt F V p.2.proj
  have hv := ((FiberBundle.continuousAt_totalSpace F (x₀ := p)
    (f := fun z : ℝ × TotalSpace F V ↦ z.2)).mp continuous_snd.continuousAt).2
  apply (continuous_fst.continuousAt.smul hv).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V p.2.proj))] with z hz
  change (e ⟨z.2.proj, z.1 • z.2.2⟩).2 = z.1 • (e z.2).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hz, map_smul]

end AtiyahSinger
