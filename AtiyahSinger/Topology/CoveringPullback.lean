/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Pullbacks of covering maps

Public module ID: M1751.

A covering map remains a covering after pullback along an arbitrary continuous
map. The fiber product has its original subtype topology. The construction uses
the original evenly covered neighborhoods, and also permits empty fibers.

This standard covering-space result supplies the covering condition for pullbacks
of the project's topological spin structures, without restrictions on the base.
-/

@[expose] public noncomputable section

namespace IsCoveringMap

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

/-- Pulling back a covering along a continuous map preserves the covering property. -/
theorem pullback {p : E → Y} (hp : IsCoveringMap p) (f : C(X, Y)) :
    IsCoveringMap (fun z : {z : X × E // f z.1 = p z.2} ↦ z.val.1) := by
  intro x
  obtain ⟨hI, U, hxU, hU, _, H, hH⟩ := hp (f x)
  let := hI
  let π : {z : X × E // f z.1 = p z.2} → X := fun z ↦ z.val.1
  -- Pull back the original evenly covered neighborhood and its sheet coordinate.
  let eU (z : π ⁻¹' (f ⁻¹' U)) : p ⁻¹' U :=
    ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact z.property⟩
  have heU : Continuous eU := by fun_prop
  let K : π ⁻¹' (f ⁻¹' U) ≃ₜ (f ⁻¹' U) × (p ⁻¹' {f x}) :=
    { toFun := fun z ↦ (⟨π z, z.property⟩, (H (eU z)).2)
      invFun := fun w ↦
        ⟨⟨(w.1.val, (H.symm (⟨f w.1.val, w.1.property⟩, w.2)).val), by
          have h := hH (H.symm (⟨f w.1.val, w.1.property⟩, w.2))
          simpa only [H.apply_symm_apply] using h⟩, w.1.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hbase : (H (eU z)).1 = ⟨f (π z), z.property⟩ := by
            apply Subtype.ext
            exact (hH (eU z)).trans z.val.property.symm
          change (H.symm (⟨f (π z), z.property⟩, (H (eU z)).2)).val = z.val.val.2
          rw [← hbase, Prod.mk.eta, H.symm_apply_apply]
      right_inv := by
        intro w
        apply Prod.ext
        · rfl
        · change (H (H.symm (⟨f w.1.val, w.1.property⟩, w.2))).2 = w.2
          rw [H.apply_symm_apply]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  -- The same discrete sheet space trivializes the pullback projection.
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := p ⁻¹' {f x})
  exact ⟨hI, f ⁻¹' U, hxU, hU.preimage f.continuous,
    (hU.preimage f.continuous).preimage (by fun_prop), K, fun _ ↦ rfl⟩

end IsCoveringMap
