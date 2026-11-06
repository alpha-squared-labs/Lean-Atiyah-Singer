/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportModule

/-!
# Restricting the coefficient of the compact-support graph action

Public module ID: M1655.

When the coefficient map factors through an open embedding, extending the
coefficient through that same embedding leaves the graph action unchanged.
The proof keeps the specified product and image collapse, so it also applies
to the inclusion into a one-point compactification. Only the graph is proper.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- A coefficient extended through its actual open inclusion has the same graph action. -/
theorem compactSupportKZeroAction_openPushforward_coefficient (f : C(Y, X))
    (j : C(X, Z)) (hj : IsOpenEmbedding j)
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
    compactSupportKZeroAction (j.comp f) (compactSupportKZeroOpenPushforward j hj a) b =
      compactSupportKZeroAction f a b := by
  let J : X × Y → Z × Y := Prod.map j id
  have hJ : IsOpenEmbedding J := hj.prodMap IsOpenEmbedding.id
  have hp := compactSupportKZeroExternalProduct_openPushforward j hj id IsOpenEmbedding.id a b
  rw [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at hp
  let F := f.prodMk (ContinuousMap.id Y)
  let G := (j.comp f).prodMk (ContinuousMap.id Y)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hG : IsProperMap G :=
    isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
  let := hJ.isOpen_range.locallyCompactSpace
  let e := hJ.isEmbedding.toHomeomorph
  let i : C(Set.range J, X × Y) := ⟨e.symm, e.symm.continuous⟩
  let collapse : C(OnePoint (Z × Y), OnePoint (Set.range J)) :=
    ⟨onePointCollapse (Set.range J), continuous_onePointCollapse _ hJ.isOpen_range⟩
  let q := (properOnePointMap i e.symm.isProperMap).comp collapse
  -- Every finite graph point lies in the specified open image and is recovered there.
  have hq (x : X) (y : Y) : q (J (x, y) : OnePoint (Z × Y)) =
      ((x, y) : OnePoint (X × Y)) := by
    change OnePoint.map i (onePointCollapse (Set.range J) (J (x, y))) = _
    rw [onePointCollapse_coe_of_mem (Set.range J) (J (x, y)) ⟨(x, y), rfl⟩,
      OnePoint.map_some]
    exact congrArg OnePoint.some (hJ.isEmbedding.toHomeomorph_symm_apply (x, y))
  have hsquare : q.comp (properOnePointMap G hG) = properOnePointMap F hF := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe y => exact hq (f y) y
  let c := compactSupportKZeroExternalProduct a b
  have hvalue : (compactSupportKZeroOpenPushforward J hJ c).val =
      complexKZeroPullback q c.val := by
    change complexKZeroPullback collapse
      (complexKZeroPullback (properOnePointMap i e.symm.isProperMap) c.val) = _
    rw [complexKZeroPullback_comp, AddMonoidHom.comp_apply]
  -- Collapse the same extended product before pulling back along the original proper graph.
  change compactSupportKZeroPullback G hG
      (compactSupportKZeroExternalProduct (compactSupportKZeroOpenPushforward j hj a) b) =
    compactSupportKZeroPullback F hF c
  rw [← hp]
  apply Subtype.ext
  change complexKZeroPullback (properOnePointMap G hG)
    (compactSupportKZeroOpenPushforward J hJ c).val = _
  rw [hvalue, ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
  rfl

end AtiyahSinger
