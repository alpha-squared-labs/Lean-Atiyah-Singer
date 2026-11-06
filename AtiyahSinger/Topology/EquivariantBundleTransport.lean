/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantVectorBundle

/-!
# Transporting a continuous action through a specified bundle isomorphism

Public module ID: M1769.

Conjugation by the actual bundle isomorphism transports the group action,
including joint continuity. This is used on the two open pieces of relative
equivariant bundle extensions. The original base action and fiber maps are
retained; no smoothness of a merely continuous isomorphism is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- The specified isomorphism transports a continuous action and intertwines it exactly. -/
theorem EquivariantStructure.exists_conjugate (σ : EquivariantStructure G E)
    (e : Iso E F) : ∃ τ : EquivariantStructure G F, e.IsEquivariant σ τ := by
  let L (g : G) (x : X) : F x →ₗ[ℂ] F (g • x) :=
    (e.linearEquiv (g • x)).toLinearMap.comp
      ((σ.linearMap g x).comp (e.linearEquiv x).symm.toLinearMap)
  let T := e.totalHomeomorph
  let A (g : G) (z : TotalSpace Unit E) : TotalSpace Unit E :=
    ⟨g • z.proj, σ.linearMap g z.proj z.snd⟩
  have hformula (g : G) (z : TotalSpace Unit F) :
      (⟨g • z.proj, L g z.proj z.snd⟩ : TotalSpace Unit F) = T (A g (T.symm z)) := rfl
  -- Conjugation of the original total action gives both laws without fiber casts.
  have hone (z : TotalSpace Unit E) : A 1 z = z := σ.one_map z.proj z.snd
  have hmul (g h : G) (z : TotalSpace Unit E) : A (g * h) z = A g (A h z) :=
    σ.mul_map g h z.proj z.snd
  let τ : EquivariantStructure G F := {
    linearMap := L
    one_map := by
      intro x v
      rw [hformula 1 ⟨x, v⟩, hone, T.apply_symm_apply]
    mul_map := by
      intro g h x v
      rw [hformula (g * h) ⟨x, v⟩, hmul,
        hformula g ⟨h • x, L h x v⟩, hformula h ⟨x, v⟩, T.symm_apply_apply]
    continuous_action := by
      -- The same continuous inverse, original joint action and forward map are composed.
      exact T.continuous.comp (σ.continuous_action.comp
        (continuous_fst.prodMk (T.symm.continuous.comp continuous_snd))) }
  refine ⟨τ, ?_⟩
  intro g x v
  change e.linearEquiv (g • x) (σ.linearMap g x v) =
    e.linearEquiv (g • x) (σ.linearMap g x ((e.linearEquiv x).symm (e.linearEquiv x v)))
  rw [LinearEquiv.symm_apply_apply]

end AtiyahSinger.ComplexBundle
