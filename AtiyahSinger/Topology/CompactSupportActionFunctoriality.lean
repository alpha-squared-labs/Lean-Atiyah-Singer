/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportModule

/-!
# Homotopy and open-extension laws for the compact-support graph action

Public module ID: M1649.

The original graph action depends only on the homotopy class of its coefficient
map and commutes with open extension in its compactly supported second factor.
Properness belongs to the graph: the original coefficient maps and open maps
need not be proper. All products and collapses are the existing constructions.

Sources: SG Appendix C.1; Karoubi II.5 and IV.5.22(b). The subspace-collapse
argument is the same one used locally in `SupportTensorAction`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology
open scoped unitInterval

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- A homotopy of coefficient maps preserves the original proper-graph action. -/
theorem compactSupportKZeroAction_eq_of_homotopy {f g : C(Y, X)}
    (H : ContinuousMap.Homotopy f g) :
    compactSupportKZeroAction f = compactSupportKZeroAction g := by
  -- Retaining the second coordinate makes the entire graph homotopy proper.
  let K : ContinuousMap.Homotopy (f.prodMk (ContinuousMap.id Y))
      (g.prodMk (ContinuousMap.id Y)) :=
    { toFun := fun p ↦ (H p, p.2)
      continuous_toFun := H.continuous.prodMk continuous_snd
      map_zero_left := fun y ↦ Prod.ext (H.apply_zero y) rfl
      map_one_left := fun y ↦ Prod.ext (H.apply_one y) rfl }
  have hK : IsProperMap K :=
    isProperMap_of_comp_of_t2 K.continuous continuous_snd isProperMap_snd_of_compactSpace
  have hf := isProperMap_of_comp_of_t2
    (f.continuous.prodMk continuous_id) continuous_snd isProperMap_id
  have hg := isProperMap_of_comp_of_t2
    (g.continuous.prodMk continuous_id) continuous_snd isProperMap_id
  -- Apply proper homotopy invariance to exactly the product defining the action.
  have heq := compactSupportKZeroPullback_eq_of_proper_homotopy hf hg K hK
  apply AddMonoidHom.ext
  intro a
  apply AddMonoidHom.ext
  intro b
  exact DFunLike.congr_fun heq (compactSupportKZeroExternalProduct a b)

private theorem action_open_second (U : Set Y) (hU : IsOpen U) (f : C(Y, X))
    (a : CompactSupportKZero X) :
    letI := hU.locallyCompactSpace
    ∀ b : CompactSupportKZero U,
      compactSupportKZeroAction f a (compactSupportKZeroOpenExtension U hU b) =
        compactSupportKZeroOpenExtension U hU
          (compactSupportKZeroAction
            (f.comp ⟨Subtype.val, continuous_subtype_val⟩) a b) := by
  let := hU.locallyCompactSpace
  intro b
  let S : Set (X × Y) := Prod.snd ⁻¹' U
  have hS : IsOpen S := hU.preimage continuous_snd
  let := hS.locallyCompactSpace
  let e : S ≃ₜ X × U := {
    toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
    invFun z := ⟨(z.1, z.2.val), z.2.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun :=
      continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
    continuous_invFun :=
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _ }
  let qU : C(OnePoint Y, OnePoint U) :=
    ⟨onePointCollapse U, continuous_onePointCollapse U hU⟩
  let qP : C(OnePoint (X × Y), OnePoint (X × U)) :=
    (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap).comp
      ⟨onePointCollapse S, continuous_onePointCollapse S hS⟩
  have hqP (x : X) (y : Y) (hy : y ∈ U) :
      qP ((x, y) : OnePoint (X × Y)) =
        ((x, ⟨y, hy⟩) : X × U) := by
    change OnePoint.map e (onePointCollapse S ((x, y) : OnePoint (X × Y))) = _
    rw [onePointCollapse_coe_of_mem S (x, y) hy, OnePoint.map_some]
    rfl
  have hqPout (x : X) (y : Y) (hy : y ∉ U) :
      qP ((x, y) : OnePoint (X × Y)) = OnePoint.infty := by
    change OnePoint.map e (onePointCollapse S ((x, y) : OnePoint (X × Y))) = _
    rw [onePointCollapse_coe_of_notMem S (x, y) hy, OnePoint.map_infty]
  -- The same collapse in the second factor commutes with the original smash collapse.
  have hsmash : qP.comp onePointProductCollapseMap =
      onePointProductCollapseMap.comp
        ((ContinuousMap.id (OnePoint X)).prodMap qU) := by
    ext z
    rcases z with ⟨x, y⟩
    cases x using OnePoint.rec with
    | infty => rfl
    | coe x =>
      cases y using OnePoint.rec with
      | infty => rfl
      | coe y =>
        by_cases hy : y ∈ U
        · change qP ((x, y) : OnePoint (X × Y)) =
            onePointProductCollapse (x, onePointCollapse U (y : OnePoint Y))
          rw [hqP x y hy, onePointCollapse_coe_of_mem U y hy]
          rfl
        · change qP ((x, y) : OnePoint (X × Y)) =
            onePointProductCollapse (x, onePointCollapse U (y : OnePoint Y))
          rw [hqPout x y hy, onePointCollapse_coe_of_notMem U y hy]
          rfl
  let c : CompactSupportKZero (X × Y) :=
    reducedComplexKZeroPullback OnePoint.infty OnePoint.infty qP rfl
      (compactSupportKZeroExternalProduct a b)
  have hproduct : c = compactSupportKZeroExternalProduct a
      (compactSupportKZeroOpenExtension U hU b) := by
    apply (existsUnique_compactSupportProduct a
      (compactSupportKZeroOpenExtension U hU b)).unique ?_
        (compactSupportKZeroExternalProduct_pullback _ _)
    change complexKZeroPullback onePointProductCollapseMap
      (complexKZeroPullback qP (compactSupportKZeroExternalProduct a b).val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsmash,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply,
      compactSupportKZeroExternalProduct_pullback, complexKZeroExternalProduct_natural]
    have hid : complexKZeroPullback (ContinuousMap.id (OnePoint X)) =
        AddMonoidHom.id (ComplexKZero (OnePoint X)) := kZeroMap_id
    rw [hid, AddMonoidHom.id_apply]
    rfl
  let G : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
  let GU : C(U, X × U) :=
    (f.comp ⟨Subtype.val, continuous_subtype_val⟩).prodMk (ContinuousMap.id U)
  have hG : IsProperMap G :=
    isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
  have hGU : IsProperMap GU :=
    isProperMap_of_comp_of_t2 GU.continuous continuous_snd isProperMap_id
  have hgraph : qP.comp (properOnePointMap G hG) =
      (properOnePointMap GU hGU).comp qU := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe y =>
      by_cases hy : y ∈ U
      · change qP ((f y, y) : OnePoint (X × Y)) =
          OnePoint.map GU (onePointCollapse U (y : OnePoint Y))
        rw [hqP (f y) y hy, onePointCollapse_coe_of_mem U y hy, OnePoint.map_some]
        rfl
      · change qP ((f y, y) : OnePoint (X × Y)) =
          OnePoint.map GU (onePointCollapse U (y : OnePoint Y))
        rw [hqPout (f y) y hy, onePointCollapse_coe_of_notMem U y hy,
          OnePoint.map_infty]
  change compactSupportKZeroPullback G hG
      (compactSupportKZeroExternalProduct a (compactSupportKZeroOpenExtension U hU b)) =
    compactSupportKZeroOpenExtension U hU
      (compactSupportKZeroPullback GU hGU (compactSupportKZeroExternalProduct a b))
  rw [← hproduct]
  apply Subtype.ext
  change complexKZeroPullback (properOnePointMap G hG)
      (complexKZeroPullback qP (compactSupportKZeroExternalProduct a b).val) =
    complexKZeroPullback qU
      (complexKZeroPullback (properOnePointMap GU hGU)
        (compactSupportKZeroExternalProduct a b).val)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hgraph,
    complexKZeroPullback_comp, AddMonoidHom.comp_apply]

/-- The graph action commutes with open extension in its compactly supported factor. -/
theorem compactSupportKZeroAction_openPushforward (f : C(Y, X))
    (j : C(Z, Y)) (hj : IsOpenEmbedding j)
    (a : CompactSupportKZero X) (b : CompactSupportKZero Z) :
    compactSupportKZeroAction f a (compactSupportKZeroOpenPushforward j hj b) =
      compactSupportKZeroOpenPushforward j hj (compactSupportKZeroAction (f.comp j) a b) := by
  let := hj.isOpen_range.locallyCompactSpace
  let e := hj.isEmbedding.toHomeomorph
  let i : C(Set.range j, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(Set.range j, Z) := ⟨e.symm, e.symm.continuous⟩
  -- The inverse image identification uses the same j and its actual range.
  have hmap : (f.comp j).comp q = f.comp i := by
    ext z
    exact congrArg f (congrArg Subtype.val (e.apply_symm_apply z))
  have htransport := compactSupportKZeroPullback_action (f.comp j) q e.symm.isProperMap a b
  rw [hmap] at htransport
  change compactSupportKZeroAction f a
      (compactSupportKZeroOpenExtension (Set.range j) hj.isOpen_range
        (compactSupportKZeroHomeomorph e b)) =
    compactSupportKZeroOpenExtension (Set.range j) hj.isOpen_range
      (compactSupportKZeroHomeomorph e (compactSupportKZeroAction (f.comp j) a b))
  -- Collapse the same open second factor before or after taking its proper graph.
  rw [action_open_second]
  exact congrArg (compactSupportKZeroOpenExtension (Set.range j) hj.isOpen_range)
    htransport.symm

end AtiyahSinger
