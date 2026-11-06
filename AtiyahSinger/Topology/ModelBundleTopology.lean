/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteBundle
public import Mathlib.Topology.VectorBundle.Hom

/-!
# Retype modeled total spaces for finite-rank K theory

Public module ID: M1960.

Only the phantom model changes: every base point and fiber vector is
preserved, and the Unit total topology is induced from the original topology.
Finite-dimensional local frames give the separate finite-rank certificate.
This is a project adapter for the bundle conventions of SG I.9 and III.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace V E)]

/-- Retype the phantom model while preserving the actual point and vector. -/
def unitTotalEquiv : TotalSpace Unit E ≃ TotalSpace V E :=
  { toFun := fun z ↦ ⟨z.proj, z.snd⟩
    invFun := fun z ↦ ⟨z.proj, z.snd⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- The original total topology transported to the Unit phantom model. -/
@[reducible]
def modelTopology : TopologicalSpace (TotalSpace Unit E) :=
  TopologicalSpace.induced (unitTotalEquiv V E) inferInstance

set_option linter.unusedSectionVars false in
/-- Retyping to the original total space is continuous. -/
theorem continuous_unitTotalEquiv :
    letI := modelTopology V E
    Continuous (unitTotalEquiv V E) := by
  /- Continuity is the defining property of the induced topology. Its map is the explicit
  retyping equivalence, so the fiber topology and base are preserved. -/
  exact continuous_induced_dom

set_option linter.unusedSectionVars false in
/-- Retyping back is continuous as well. -/
theorem continuous_unitTotalEquiv_symm :
    letI := modelTopology V E
    Continuous (unitTotalEquiv V E).symm := by
  /- Test continuity into the induced topology by composing with the forward equivalence. The
  resulting composite is identity on the original total space. -/
  let := modelTopology V E
  apply continuous_induced_rng.mpr
  apply continuous_id.congr
  intro z
  exact ((unitTotalEquiv V E).apply_symm_apply z).symm

/-- The actual homeomorphism between the two phantom-model conventions. -/
def unitTotalHomeomorph :
    letI := modelTopology V E
    TotalSpace Unit E ≃ₜ TotalSpace V E :=
  letI := modelTopology V E
  { toEquiv := unitTotalEquiv V E
    continuous_toFun := continuous_unitTotalEquiv V E
    continuous_invFun := continuous_unitTotalEquiv_symm V E }

/-- Retyping a vector retains both its base and value. -/
theorem unitTotalHomeomorph_apply (x : X) (v : E x) :
    letI := modelTopology V E
    unitTotalHomeomorph V E ⟨x, v⟩ = ⟨x, v⟩ := by
  /- The homeomorphism uses the explicit equivalence on dependent pairs. Evaluate that
  definition; none of the continuity certificates can change its vector action. -/
  rfl

set_option linter.unusedSectionVars false in
/-- Continuity of a map into the retyped space is exactly original continuity. -/
theorem continuous_modelTotal_iff (f : Y → TotalSpace Unit E) :
    letI := modelTopology V E
    Continuous f ↔ Continuous (fun y ↦ unitTotalEquiv V E (f y)) := by
  /- The forward direction composes continuous maps. The reverse composes the original
  continuous map with the inverse homeomorphism, recovering f pointwise. -/
  exact continuous_induced_rng

variable [hB : FiberBundle V E] [hV : VectorBundle ℂ V E]
  [hD : FiniteDimensional ℂ V]

include hB hV hD

/-- Finite-dimensional modeled local frames give the standard local finite-rank condition. -/
theorem isFiniteRank_model :
    letI := modelTopology V E
    IsFiniteRank E := by
  /- Take a linear bundle trivialization at each point. Compose its model coordinate with a
  continuous linear coordinate equivalence V to Fin(finrank V) → ℂ, and retype its source
  using the total homeomorphism. The resulting local trivialization is linear on each fiber.
  No global basis of the bundle is chosen. -/
  let := modelTopology V E
  constructor
  intro x
  -- Retain the original local frame and use finite coordinates only on its model fiber.
  let e := trivializationAt V E x
  let c : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  let t : Trivialization (Fin (Module.finrank ℂ V) → ℂ) (π Unit E) :=
    (e.transFiberHomeomorph c.toHomeomorph).compHomeomorph (unitTotalHomeomorph V E)
  refine ⟨Module.finrank ℂ V, t, FiberBundle.mem_baseSet_trivializationAt V E x, ?_⟩
  intro y hy
  -- The retyping map preserves each vector, so the new fiber map is the same linear chart.
  have hlinear : IsLinearMap ℂ (fun v : E y ↦ (e ⟨y, v⟩).2) :=
    e.toPretrivialization.linear ℂ hy
  constructor
  · intro v w
    change c ((e ⟨y, v + w⟩).2) = c ((e ⟨y, v⟩).2) + c ((e ⟨y, w⟩).2)
    rw [hlinear.map_add, map_add]
  · intro a v
    change c ((e ⟨y, a • v⟩).2) = a • c ((e ⟨y, v⟩).2)
    rw [hlinear.map_smul, map_smul]

/-- A small bundle object isomorphic to the original modeled family. -/
def modelFiniteBundle :
    letI := modelTopology V E
    letI := isFiniteRank_model V E
    FiniteBundle X :=
  letI := modelTopology V E
  letI := isFiniteRank_model V E
  smallBundle E

/-- The original family is mapped to its chosen small model by an actual bundle isomorphism. -/
def modelFiniteBundleIso :
    letI := modelTopology V E
    letI := isFiniteRank_model V E
    Iso E (modelFiniteBundle V E).Fiber :=
  letI := modelTopology V E
  letI := isFiniteRank_model V E
  smallBundleIso E

omit hV hD in
/-- Modeled bundle projection remains continuous after retyping. -/
theorem continuous_model_proj :
    letI := modelTopology V E
    Continuous (π Unit E) := by
  /- Compose the retyping homeomorphism with the original continuous bundle projection. Both
  projections return the identical base point. -/
  let := modelTopology V E
  exact (FiberBundle.continuous_proj V E).comp (continuous_unitTotalEquiv V E)

omit hB hV hD in
/-- A section is continuous in exactly the original total-space sense. -/
theorem continuous_model_section_iff (s : ∀ x, E x) :
    letI := modelTopology V E
    Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E)) ↔
      Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace V E)) := by
  /- Apply the continuity equivalence for retyping to the displayed section. The coordinate
  change retains its pointwise fiber values, with no regularity choice. -/
  exact continuous_modelTotal_iff V E (fun x ↦ ⟨x, s x⟩)

end AtiyahSinger.ComplexBundle
