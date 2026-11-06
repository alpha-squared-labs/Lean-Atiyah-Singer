/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantOpenExtension
public import AtiyahSinger.Topology.EquivariantRestriction

/-!
# Group restriction and controlled open extension

Public module ID: M1797.

Restriction along a continuous homomorphism commutes with the original open
extension. Both groups are compact Hausdorff, and both bases are locally compact
Hausdorff. The proof chooses one ambient extension before restricting its group
action; this preserves the bundles, boundary and compact control on both routes.
This naturality is used by the restricted sphere pole comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Topology

variable {G H X Y : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]

/-- Group restriction preserves open extension on the same controlled support quotient. -/
theorem equivariantSupportTripleKZeroRestrict_openPushforward
    (φ : H →ₜ* G) (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (a : EquivariantSupportTripleKZero G X) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    letI : MulAction H Y := MulAction.compHom Y φ.toMonoidHom
    letI : ContinuousSMul H Y := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ
        (equivariantSupportTripleKZeroOpenPushforward f hf heq a) =
      equivariantSupportTripleKZeroOpenPushforward f hf (fun h x ↦ heq (φ h) x)
        (equivariantSupportTripleKZeroRestrict φ a) := by
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  let : MulAction H Y := MulAction.compHom Y φ.toMonoidHom
  let : ContinuousSMul H Y := MulAction.continuousSMul_compHom φ.continuous
  -- One controlled ambient extension represents the supplied class before group restriction.
  obtain ⟨b, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  obtain ⟨B, hc, hstable⟩ := b.exists_openExtension f hf heq
  have hb := EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _ hstable
  rw [← hb, equivariantSupportTripleKZeroOpenPushforward_class,
    equivariantSupportTripleKZeroRestrict_apply, equivariantSupportTripleKZeroRestrict_apply]
  -- Restricting the original fiber actions commutes with this same bundle pullback.
  change (B.restrict φ).kZeroClass =
    equivariantSupportTripleKZeroOpenPushforward f hf (fun h x ↦ heq (φ h) x)
      ((B.restrict φ).openRestrict f hf (fun h x ↦ heq (φ h) x) hc).kZeroClass
  exact (equivariantSupportTripleKZeroOpenPushforward_class f hf
    (fun h x ↦ heq (φ h) x) (B.restrict φ) hc).symm

end AtiyahSinger.ComplexBundle
