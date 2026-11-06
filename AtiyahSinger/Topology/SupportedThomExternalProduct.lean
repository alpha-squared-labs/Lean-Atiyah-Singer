/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportSplitPair
public import AtiyahSinger.Topology.SupportedThomModule
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# External coefficients for the actual supported Thom operator

Public module ID: M2214.

The pullback along the second projection has total space `X × Total(E)`.
Its original supported Thom operator commutes with the external product.
The compact parameter calculation uses the original graph module action;
extension into the one-point compactification treats arbitrary locally compact
Hausdorff parameters. The infinity fiber has a proper retraction, so this
extension detects equality rather than merely forgetting a possible boundary.

This is the supported external-product naturality in SG Appendix C.1/C.13
and Karoubi IV.1. The left coefficient retains its order, and the same
metric and original Thom representative are used throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- The total space of the second-projection pullback retains the original pair of points. -/
def pullbackSndTotalHomeomorph (X : Type*) [TopologicalSpace X] :
    TotalSpace Unit (((ContinuousMap.snd : C(X × B, B)) : X × B → B) *ᵖ E) ≃ₜ
      X × TotalSpace Unit E where
  toFun z := (z.proj.1, ⟨z.proj.2, z.snd⟩)
  invFun z := ⟨(z.1, z.2.proj), z.2.snd⟩
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨x, b, v⟩; rfl
  continuous_toFun :=
    ((Pullback.continuous_proj Unit E (ContinuousMap.snd : C(X × B, B))).fst).prodMk
      (Pullback.continuous_lift Unit E (ContinuousMap.snd : C(X × B, B)))
  continuous_invFun := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E
      (ContinuousMap.snd : C(X × B, B))).continuous_iff]
    exact (continuous_fst.prodMk
      ((continuous_proj (E := E)).comp continuous_snd)).prodMk continuous_snd

namespace ContinuousHermitianMetric

attribute [local instance] isFiniteRank_pullback t2Space_totalSpace locallyCompactSpace_totalSpace

private theorem action_fst_pullback_snd
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
    complexKZeroCompactSupportAction (ContinuousMap.fst : C(X × Y, X))
      ((compactSupportKZeroCompactEquiv X) a)
      (compactSupportKZeroPullback (ContinuousMap.snd : C(X × Y, Y))
        isProperMap_snd_of_compactSpace b) = compactSupportKZeroExternalProduct a b := by
  let p : C(X × Y, Y) := ContinuousMap.snd
  have hp : IsProperMap p := isProperMap_snd_of_compactSpace
  let g : C(X × Y, X × (X × Y)) :=
    (ContinuousMap.fst : C(X × Y, X)).prodMk (ContinuousMap.id (X × Y))
  have hg : IsProperMap g :=
    isProperMap_of_comp_of_t2 g.continuous continuous_snd isProperMap_id
  let q := (ContinuousMap.id X).prodMap p
  have hq : IsProperMap q := isProperMap_id.prodMap hp
  have hprod := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) isProperMap_id p hp a b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprod
  change compactSupportKZeroPullback g hg
    (compactSupportKZeroExternalProduct
      ((compactSupportKZeroCompactEquiv X).symm ((compactSupportKZeroCompactEquiv X) a))
      (compactSupportKZeroPullback p hp b)) = _
  rw [AddEquiv.symm_apply_apply, ← hprod]
  change compactSupportKZeroPullback g hg
    (compactSupportKZeroPullback q hq (compactSupportKZeroExternalProduct a b)) = _
  rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  have hid : q.comp g = ContinuousMap.id (X × Y) := rfl
  simp only [hid, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Normalize the compact-parameter pullback and common right coefficient action.
private theorem supportedThomHom_externalProduct_compact
    {X B : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
    {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (a : CompactSupportKZero X)
    (b : CompactSupportKZero B) :
    compactSupportKZeroHomeomorph (pullbackSndTotalHomeomorph E X)
      ((h.pullback (ContinuousMap.snd : C(X × B, B))).supportedThomHom
        (compactSupportKZeroExternalProduct a b)) =
      compactSupportKZeroExternalProduct a (h.supportedThomHom b) := by
  let p : C(X × B, B) := ContinuousMap.snd
  let f : C(X × B, X) := ContinuousMap.fst
  let H := h.pullback p
  let F := (p : X × B → B) *ᵖ E
  let e := pullbackSndTotalHomeomorph E X
  let i : C(X × TotalSpace Unit E, TotalSpace Unit F) := ⟨e.symm, e.symm.continuous⟩
  let πF : C(TotalSpace Unit F, X × B) := ⟨π Unit F, continuous_proj⟩
  have hnatural := DFunLike.congr_fun
    (h.supportedThomHom_pullback p isProperMap_snd_of_compactSpace) b
  have hmodule := H.supportedThomHom_complexKZeroCompactSupportAction f
    ((compactSupportKZeroCompactEquiv X) a)
    (compactSupportKZeroPullback p isProperMap_snd_of_compactSpace b)
  rw [action_fst_pullback_snd] at hmodule
  -- The same graph action transports through the inverse total-space homeomorphism.
  change compactSupportKZeroPullback i e.symm.isProperMap
    (H.supportedThomHom (compactSupportKZeroExternalProduct a b)) = _
  rw [hmodule]
  change compactSupportKZeroPullback i e.symm.isProperMap
    (compactSupportKZeroAction (f.comp πF)
      ((compactSupportKZeroCompactEquiv X).symm ((compactSupportKZeroCompactEquiv X) a))
      (H.supportedThomHom (compactSupportKZeroPullback p
        isProperMap_snd_of_compactSpace b))) = _
  rw [AddEquiv.symm_apply_apply]
  rw [compactSupportKZeroPullback_action]
  change compactSupportKZeroAction (ContinuousMap.fst : C(X × TotalSpace Unit E, X)) a
    (compactSupportKZeroPullback i e.symm.isProperMap
      (H.supportedThomHom (compactSupportKZeroPullback p
        isProperMap_snd_of_compactSpace b))) = _
  change H.supportedThomHom (compactSupportKZeroPullback p
    isProperMap_snd_of_compactSpace b) =
    compactSupportKZeroPullback (pullbackTotalMap E p)
      ((pullbackTotalMap_properties E p).1 isProperMap_snd_of_compactSpace)
      (h.supportedThomHom b) at hnatural
  rw [hnatural]
  have hcomp := DFunLike.congr_fun (compactSupportKZeroPullback_comp i
    (pullbackTotalMap E p) e.symm.isProperMap
    ((pullbackTotalMap_properties E p).1 isProperMap_snd_of_compactSpace))
    (h.supportedThomHom b)
  rw [AddMonoidHom.comp_apply] at hcomp
  rw [← hcomp]
  have hmap : (pullbackTotalMap E p).comp i =
      (ContinuousMap.snd : C(X × TotalSpace Unit E, TotalSpace Unit E)) := rfl
  have hresult := action_fst_pullback_snd a (h.supportedThomHom b)
  change compactSupportKZeroAction (ContinuousMap.fst : C(X × TotalSpace Unit E, X))
    ((compactSupportKZeroCompactEquiv X).symm ((compactSupportKZeroCompactEquiv X) a))
    (compactSupportKZeroPullback ContinuousMap.snd isProperMap_snd_of_compactSpace
      (h.supportedThomHom b)) = _ at hresult
  rw [AddEquiv.symm_apply_apply] at hresult
  simpa only [hmap] using hresult

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the one-point extension and infinity-fiber equality detection.
/-- Supported Thom multiplication commutes with external coefficients on any LCH parameter. -/
theorem supportedThomHom_externalProduct
    {X B : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
    {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (a : CompactSupportKZero X)
    (b : CompactSupportKZero B) :
    compactSupportKZeroHomeomorph (pullbackSndTotalHomeomorph E X)
      ((h.pullback (ContinuousMap.snd : C(X × B, B))).supportedThomHom
        (compactSupportKZeroExternalProduct a b)) =
      compactSupportKZeroExternalProduct a (h.supportedThomHom b) := by
  classical
  let Xbar := OnePoint X
  let T := TotalSpace Unit E
  let pX : C(X × B, B) := ContinuousMap.snd
  let pB : C(Xbar × B, B) := ContinuousMap.snd
  let EX := (pX : X × B → B) *ᵖ E
  let EB := (pB : Xbar × B → B) *ᵖ E
  let hX := h.pullback pX
  let hB := h.pullback pB
  let eX := pullbackSndTotalHomeomorph E X
  let eB := pullbackSndTotalHomeomorph E Xbar
  let inc : C(X, Xbar) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  have hinc : IsOpenEmbedding inc := OnePoint.isOpenEmbedding_coe
  let f : C(X × B, Xbar × B) := inc.prodMap (ContinuousMap.id B)
  have hf : IsOpenEmbedding f := hinc.prodMap IsOpenEmbedding.id
  let j : X × T → Xbar × T := Prod.map inc id
  have hj : IsOpenEmbedding j := hinc.prodMap IsOpenEmbedding.id
  let R := (f : X × B → Xbar × B) *ᵖ EB
  let d : Iso R EX := pullbackCompIso (E := E) pB f
  let q := pullbackTotalMap EB f
  have hq : IsOpenEmbedding q := (pullbackTotalMap_properties EB f).2 hf
  -- The only new points are the infinity fiber; its projection is a proper retraction.
  let N : Set (Xbar × T) := (Set.range j)ᶜ
  have hN : IsClosed N := hj.isOpen_range.isClosed_compl
  let := hN.locallyCompactSpace
  have hinfty (v : T) : (OnePoint.infty, v) ∈ N := by
    rintro ⟨z, hz⟩
    have hp := congrArg Prod.fst hz
    cases hp
  have hpoint (z : N) : z.val.1 = OnePoint.infty := by
    rcases z with ⟨⟨x, v⟩, hz⟩
    cases x using OnePoint.rec with
    | infty => rfl
    | coe x => exact (hz ⟨(x, v), rfl⟩).elim
  let r : C(Xbar × T, N) :=
    ⟨fun z ↦ ⟨(OnePoint.infty, z.2), hinfty z.2⟩,
      (continuous_const.prodMk continuous_snd).subtype_mk _⟩
  have hr (z : N) : r z.val = z := by
    apply Subtype.ext
    exact Prod.ext (hpoint z).symm rfl
  have hproper : IsProperMap r :=
    isProperMap_of_comp_of_t2 r.continuous
      (continuous_snd.comp continuous_subtype_val)
      (show IsProperMap ((fun z : N ↦ z.val.2) ∘ r) from
        isProperMap_snd_of_compactSpace)
  have hdetect : Function.Injective (compactSupportKZeroOpenPushforward j hj) :=
    compactSupportKZeroOpenPushforward_injective_of_retraction j hj r hproper hr
  -- Every route in the extension square retains the same parameter and original fiber vector.
  have hsquare (u : CompactSupportKZero (TotalSpace Unit R)) :
      compactSupportKZeroOpenPushforward j hj
          (compactSupportKZeroHomeomorph eX
            (compactSupportKZeroHomeomorph d.totalHomeomorph u)) =
        compactSupportKZeroHomeomorph eB (compactSupportKZeroOpenPushforward q hq u) := by
    have hmaps : (j ∘ eX) ∘ d.totalHomeomorph = eB ∘ q := by
      funext z
      change (inc z.proj.1, (⟨z.proj.2, d.linearEquiv z.proj z.snd⟩ : T)) =
        (inc z.proj.1, (⟨z.proj.2, z.snd⟩ : T))
      rw [show d.linearEquiv z.proj z.snd = z.snd from
        pullbackCompIso_apply (E := E) pB f z.proj z.snd]
    rw [← compactSupportKZeroOpenPushforward_homeomorph eX,
      ← compactSupportKZeroOpenPushforward_homeomorph d.totalHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph eB]
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
    simp only [hmaps]
    rfl
  let c := compactSupportKZeroExternalProduct a b
  have hmetric := DFunLike.congr_fun ((hB.pullback f).supportedThomHom_iso hX d) c
  have hextend := DFunLike.congr_fun (hB.supportedThomHom_openPushforward f hf) c
  have hproduct := compactSupportKZeroExternalProduct_openPushforward inc hinc
    id IsOpenEmbedding.id a b
  rw [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at hproduct
  -- Compactification is used only after equality detection has been proved for this open map.
  apply hdetect
  calc
    compactSupportKZeroOpenPushforward j hj
        (compactSupportKZeroHomeomorph eX (hX.supportedThomHom c)) =
        compactSupportKZeroHomeomorph eB
          (compactSupportKZeroOpenPushforward q hq ((hB.pullback f).supportedThomHom c)) := by
      rw [← hmetric]
      exact hsquare _
    _ = compactSupportKZeroHomeomorph eB
        (hB.supportedThomHom (compactSupportKZeroOpenPushforward f hf c)) := by
      exact congrArg (compactSupportKZeroHomeomorph eB) hextend
    _ = compactSupportKZeroHomeomorph eB
        (hB.supportedThomHom (compactSupportKZeroExternalProduct
          (compactSupportKZeroOpenPushforward inc hinc a) b)) := by
      exact congrArg (fun u ↦ compactSupportKZeroHomeomorph eB (hB.supportedThomHom u))
        hproduct
    _ = compactSupportKZeroExternalProduct (compactSupportKZeroOpenPushforward inc hinc a)
        (h.supportedThomHom b) := supportedThomHom_externalProduct_compact h _ b
    _ = compactSupportKZeroOpenPushforward j hj
        (compactSupportKZeroExternalProduct a (h.supportedThomHom b)) := by
      simpa only [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] using
        (compactSupportKZeroExternalProduct_openPushforward inc hinc id IsOpenEmbedding.id
          a (h.supportedThomHom b)).symm

end ContinuousHermitianMetric

end AtiyahSinger.ComplexBundle
