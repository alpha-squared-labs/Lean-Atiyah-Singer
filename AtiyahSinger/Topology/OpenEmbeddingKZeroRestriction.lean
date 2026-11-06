/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OpenEmbeddingKZero

/-!
# Restriction of extension along open embeddings

Public module ID: M1971.

Proper restriction to the same open embedding recovers its original class;
restriction to a disjoint image vanishes. Both facts follow from the actual
one-point collapse defining extension. These are the diagonal identities
needed to reconstruct classes from finitely many clopen components.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
  [LocallyCompactSpace Z] [T2Space Z]

/-- Proper restriction to an open embedding is a left inverse of its open extension. -/
theorem compactSupportKZeroPullback_openPushforward_self
    (f : X → Y) (hf : IsOpenEmbedding f) (hp : IsProperMap f)
    (a : CompactSupportKZero X) :
    compactSupportKZeroPullback ⟨f, hf.continuous⟩ hp
      (compactSupportKZeroOpenPushforward f hf a) = a := by
  let := hf.isOpen_range.locallyCompactSpace
  let e := hf.isEmbedding.toHomeomorph
  let i : C(Set.range f, X) := ⟨e.symm, e.symm.continuous⟩
  let c : C(OnePoint Y, OnePoint (Set.range f)) :=
    ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  let F := properOnePointMap ⟨f, hf.continuous⟩ hp
  let I := properOnePointMap i e.symm.isProperMap
  -- A finite point survives the collapse, and the actual inverse image recovers it.
  have heq : I.comp (c.comp F) = ContinuousMap.id (OnePoint X) := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      change OnePoint.map i (onePointCollapse (Set.range f) (f x)) = (x : OnePoint X)
      rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
      exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  apply Subtype.ext
  change complexKZeroPullback F (complexKZeroPullback c (complexKZeroPullback I a.val)) =
    a.val
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, heq]
  change kZeroMap (RingHom.id C(OnePoint X, ℂ)) a.val = a.val
  rw [kZeroMap_id]
  rfl

/-- Proper restriction to a disjoint image annihilates an open extension. -/
theorem compactSupportKZeroPullback_openPushforward_of_disjoint
    (f : X → Y) (hf : IsOpenEmbedding f) (g : C(Z, Y)) (hg : IsProperMap g)
    (hd : Disjoint (Set.range f) (Set.range g)) (a : CompactSupportKZero X) :
    compactSupportKZeroPullback g hg (compactSupportKZeroOpenPushforward f hf a) = 0 := by
  let := hf.isOpen_range.locallyCompactSpace
  let e := hf.isEmbedding.toHomeomorph
  let i : C(Set.range f, X) := ⟨e.symm, e.symm.continuous⟩
  let c : C(OnePoint Y, OnePoint (Set.range f)) :=
    ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  let G := properOnePointMap g hg
  let I := properOnePointMap i e.symm.isProperMap
  -- Every point of the disjoint image is collapsed to infinity.
  have heq : I.comp (c.comp G) = ContinuousMap.const (OnePoint Z) (∞ : OnePoint X) := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe z =>
      have hnot : g z ∉ Set.range f :=
        fun h ↦ Set.disjoint_left.mp hd h ⟨z, rfl⟩
      change OnePoint.map i (onePointCollapse (Set.range f) (g z)) = ∞
      rw [onePointCollapse_coe_of_notMem _ _ hnot, OnePoint.map_infty]
  apply Subtype.ext
  change complexKZeroPullback G (complexKZeroPullback c (complexKZeroPullback I a.val)) = 0
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, heq]
  -- A reduced class has zero evaluation at infinity, through which the constant map factors.
  have hconst :
      (ContinuousMap.compRightAlgHom ℂ ℂ
        (ContinuousMap.const (OnePoint Z) (∞ : OnePoint X))).toRingHom =
        (ContinuousMap.C : ℂ →+* C(OnePoint Z, ℂ)).comp
          (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint X)).toRingHom := by
    ext f z
    rfl
  change kZeroMap _ a.val = 0
  rw [hconst, kZeroMap_comp, AddMonoidHom.comp_apply]
  rw [show kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint X)).toRingHom a.val = 0
    from a.property, map_zero]

end AtiyahSinger
