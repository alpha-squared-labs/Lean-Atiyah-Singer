/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantOpenExtension

/-!
# Open extension and pullback along equivariant homeomorphisms

Public module ID: M1795.

The covariant extension along a homeomorphism is the proper pullback along its
inverse. The comparison uses the original controlled triple characterization,
so it also applies to the actual sphere pole charts and their symmetries.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- Proper pullback by a homeomorphism is open extension through its actual inverse. -/
theorem equivariantSupportTripleKZeroPullback_eq_openPushforward_symm
    (e : X ≃ₜ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (hi : ∀ (g : G) (y : Y), e.symm (g • y) = g • e.symm y) :
    equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ he e.isProperMap =
      equivariantSupportTripleKZeroOpenPushforward ⟨e.symm, e.symm.continuous⟩
        e.symm.isOpenEmbedding hi :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let k : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  have hcomp : k.comp f = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  have hpull := equivariantSupportTripleKZeroPullback_comp k f hi he
    e.symm.isProperMap e.isProperMap
  have hid : equivariantSupportTripleKZeroPullback (k.comp f)
      (fun g x ↦ (congrArg k (he g x)).trans (hi g (f x)))
      (e.symm.isProperMap.comp e.isProperMap) =
        AddMonoidHom.id (EquivariantSupportTripleKZero G X) := by
    simpa only [hcomp] using
      (equivariantSupportTripleKZeroPullback_id (G := G) (X := X))
  -- A restriction through the onto open map is the very same proper pullback triple.
  apply (existsUnique_equivariantSupportTripleKZeroOpenPushforward k
    e.symm.isOpenEmbedding hi).unique
  · intro a ha
    have hclass := equivariantSupportTripleKZeroPullback_apply k hi e.symm.isProperMap a
    change equivariantSupportTripleKZeroPullback f he e.isProperMap
      (a.openRestrict k e.symm.isOpenEmbedding hi ha).kZeroClass = a.kZeroClass
    rw [show (a.openRestrict k e.symm.isOpenEmbedding hi ha).kZeroClass =
      equivariantSupportTripleKZeroPullback k hi e.symm.isProperMap a.kZeroClass
        from hclass.symm]
    have h := DFunLike.congr_fun (hpull.symm.trans hid) a.kZeroClass
    exact h
  · exact equivariantSupportTripleKZeroOpenPushforward_class _ _ _

end AtiyahSinger.ComplexBundle
