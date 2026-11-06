/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantPullbackTransport

/-!
# Equivariance detected after the original pullback lifts

Public module ID: M1800.

A specified map between two pullback bundles is equivariant when its lift is
an equivariant map of the original total spaces. This criterion keeps both
base maps and their actual transported actions. It is used for the native
graded source and target comparisons under the cotangent product splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X Y Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : Y → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An equivariant original total-space lift detects equivariance for the pulled actions. -/
theorem Iso.isEquivariant_of_lift
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (f : C(Z, X)) (p : C(Z, Y))
    (hf : ∀ (g : G) (z : Z), f (g • z) = g • f z)
    (hp : ∀ (g : G) (z : Z), p (g • z) = g • p z)
    (U : Iso (f *ᵖ E) (p *ᵖ F))
    (L : TotalSpace Unit E → TotalSpace Unit F)
    (hL : ∀ (g : G) (w : TotalSpace Unit E),
      L ⟨g • w.proj, ρE.linearMap g w.proj w.snd⟩ =
        ⟨g • (L w).proj, ρF.linearMap g (L w).proj (L w).snd⟩)
    (hU : ∀ (z : Z) (v : E (f z)),
      (⟨p z, U.linearEquiv z v⟩ : TotalSpace Unit F) = L ⟨f z, v⟩) :
    U.IsEquivariant (ρE.pullback f hf) (ρF.pullback p hp) := by
  let : MulAction G (TotalSpace Unit F) := ρF.toMulAction
  intro g z v
  apply TotalSpace.mk_injective (F := Unit) (p (g • z))
  -- Lift both pulled actions to their original total spaces before comparing the map.
  have hleft := hU (g • z) ((ρE.pullback f hf).linearMap g z v)
  have hsource := congrArg L (ρE.pullback_lift_action f hf g z v)
  have hmiddle := hL g ⟨f z, v⟩
  have hright := congrArg (fun w : TotalSpace Unit F ↦ g • w) (hU z v)
  have htarget := ρF.pullback_lift_action p hp g z (U.linearEquiv z v)
  exact hleft.trans (hsource.trans (hmiddle.trans (hright.symm.trans htarget.symm)))

end AtiyahSinger.ComplexBundle
