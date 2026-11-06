/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundlePullback

/-!
# Equivariance of the canonical pullback composition comparison

Public module ID: M1801.

The original vector-preserving comparison between iterated and composite
pullbacks intertwines the actual transported actions. Its proof keeps the
moving-base equalities by lifting both sides into the original total space.
This supplies the endpoint comparisons in equivariant bundle homotopy
invariance and the zero-section/projection comparisons for cotangent bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X Y Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- Lifting a pulled action into the original total space retains the exact original action. -/
theorem EquivariantStructure.pullback_lift_action (ρ : EquivariantStructure G E)
    (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (g : G) (x : X) (v : E (f x)) :
    (⟨f (g • x), (ρ.pullback f hf).linearMap g x v⟩ : TotalSpace Unit E) =
      ⟨g • f x, ρ.linearMap g (f x) v⟩ := by
  have hcast (a b : Y) (hab : a = b) (L : E (f x) →ₗ[ℂ] E b) :
      (⟨a, (Eq.mpr (congrArg (fun y ↦ E (f x) →ₗ[ℂ] E y) hab) L) v⟩ :
        TotalSpace Unit E) = ⟨b, L v⟩ := by
    subst b
    rfl
  exact hcast (f (g • x)) (g • f x) (hf g x) (ρ.linearMap g (f x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Keep the definitionally identical native pullback fibers visible during transport.
/-- The specified iterated-pullback comparison intertwines the transported original actions. -/
theorem EquivariantStructure.pullbackCompIso_isEquivariant (ρ : EquivariantStructure G E)
    (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (p : C(Z, X)) (hp : ∀ (g : G) (z : Z), p (g • z) = g • p z) :
    (pullbackCompIso (E := E) f p).IsEquivariant ((ρ.pullback f hf).pullback p hp)
      (ρ.pullback (f.comp p) (fun g z ↦ (congrArg f (hp g z)).trans (hf g (p z)))) := by
  intro g z v
  change (pullbackCompIso (E := E) f p).linearEquiv (g • z)
    (((ρ.pullback f hf).pullback p hp).linearMap g z v) =
      (ρ.pullback (f.comp p) _).linearMap g z
        ((pullbackCompIso (E := E) f p).linearEquiv z v)
  rw [pullbackCompIso_apply, pullbackCompIso_apply]
  apply TotalSpace.mk_injective (F := Unit) (f (p (g • z)))
  have h₁ := (ρ.pullback f hf).pullback_lift_action p hp g z v
  have h₂ := congrArg (Pullback.lift (E := E) (f : X → Y)) h₁
  change (⟨f (p (g • z)), ((ρ.pullback f hf).pullback p hp).linearMap g z v⟩ :
      TotalSpace Unit E) = ⟨f (g • p z), (ρ.pullback f hf).linearMap g (p z) v⟩ at h₂
  exact h₂.trans ((ρ.pullback_lift_action f hf g (p z) v).trans
    (ρ.pullback_lift_action (f.comp p) _ g z v).symm)

end AtiyahSinger.ComplexBundle
