/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum

/-!
# The direct-sum total space as an iterated bundle

Public module ID: M1595.

The total space of `E ⊕ F` is canonically the total space of the pullback of F
to E. The identification is exactly `(x,(e,f)) ↦ ((x,e),f)`, with no choices
of frames or a new bundle carrier. It is used to compare actual Thom operators
in the direct-sum formula. A zero-rank bundle has its original zero section as
the canonical homeomorphism from its base, needed for the Thom unit case.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- Both directions of the original direct-sum/pullback reassociation are continuous. -/
theorem sumTotalPullback_continuity :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨⟨z.proj, z.snd.1⟩, z.snd.2⟩ : TotalSpace Unit ((π Unit E) *ᵖ F))) ∧
      Continuous (fun z : TotalSpace Unit ((π Unit E) *ᵖ F) ↦
        (⟨z.proj.proj, (z.proj.snd, z.snd)⟩ : TotalSpace Unit (E ×ᵇ F))) := by
  /- The pullback topology tests continuity by projection to E and lift to F.
  For the forward map these are the two original direct-sum projections.
  Conversely the direct-sum topology is induced by the pair of total-space
  projections, which after reassociation are the pullback projection and lift.
  These formulas prove both continuities without finite rank or compactness. -/
  constructor
  · -- The two coordinates tested by the pullback topology are the original sum projections.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F (π Unit E)).continuous_iff]
    exact (continuous_sum_fst (E := E) (F := F)).prodMk
      (continuous_sum_snd (E := E) (F := F))
  · -- In the reverse direction the induced sum coordinates are projection and lift.
    apply continuous_induced_rng.mpr
    exact (_root_.Pullback.continuous_proj Unit F (π Unit E)).prodMk
      (_root_.Pullback.continuous_lift Unit F (π Unit E))

/-- The canonical reassociation keeps the base point and the order of the two fiber vectors. -/
def sumTotalPullbackHomeomorph :
    TotalSpace Unit (E ×ᵇ F) ≃ₜ TotalSpace Unit ((π Unit E) *ᵖ F) where
  toFun z := ⟨⟨z.proj, z.snd.1⟩, z.snd.2⟩
  invFun z := ⟨z.proj.proj, (z.proj.snd, z.snd)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := sumTotalPullback_continuity.1
  continuous_invFun := sumTotalPullback_continuity.2

/-- A zero-rank bundle is identified with its base by its actual zero section. -/
def zeroSectionHomeomorph [IsFiniteRank E] [∀ x, Subsingleton (E x)] :
    X ≃ₜ TotalSpace Unit E where
  toFun x := ⟨x, 0⟩
  invFun := π Unit E
  left_inv _ := rfl
  right_inv z := by
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq (Subsingleton.elim _ _)
  continuous_toFun := continuous_zero_section E
  continuous_invFun := continuous_proj

end AtiyahSinger.ComplexBundle
