/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportedThomExternalProduct

/-!
# The compact-support coefficient of a pulled-back Thom class

Public module ID: M2218.

For an arbitrary continuous map into a compact base, the supported Thom image
is the pullback of the external product of that coefficient with the original
compact-base Thom class along the full paired total-space map. That paired map is a closed
embedding, although neither the base map nor either projection need be proper.

The proof combines external-product compatibility with proper naturality along
the graph. The pullback-composition isomorphism retains the same fiber vector.
This is the graph formulation of the supported Thom construction in SG C.1/C.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

attribute [local instance] isFiniteRank_pullback t2Space_totalSpace locallyCompactSpace_totalSpace

/-- The full pullback pair is a closed embedding, without properness of its base map. -/
theorem pullbackTotalSpaceEmbedding_isClosedEmbedding
    {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [T2Space B]
    (E : B → Type*) [TopologicalSpace (TotalSpace Unit E)]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [IsFiniteRank E]
    (f : C(X, B)) :
    IsClosedEmbedding (pullbackTotalSpaceEmbedding (F := Unit) (E := E) f) := by
  let j : TotalSpace Unit ((f : X → B) *ᵖ E) → X × TotalSpace Unit E :=
    pullbackTotalSpaceEmbedding f
  have hemb : IsEmbedding j := by
    refine ⟨inducing_pullbackTotalSpaceEmbedding Unit E f, ?_⟩
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    have hxy : x = y := congrArg Prod.fst h
    subst y
    have hvw : v = w := TotalSpace.mk_injective (f x) (congrArg Prod.snd h)
    subst w
    rfl
  have hrange : Set.range j = {p : X × TotalSpace Unit E | f p.1 = p.2.proj} := by
    ext ⟨x, y, v⟩
    constructor
    · rintro ⟨⟨a, w⟩, h⟩
      have ha : a = x := congrArg Prod.fst h
      have hb : f a = y := congrArg (fun p : X × TotalSpace Unit E ↦ p.2.proj) h
      change f x = y
      simpa only [ha] using hb
    · intro h
      change f x = y at h
      subst y
      exact ⟨⟨x, v⟩, rfl⟩
  refine ⟨hemb, ?_⟩
  rw [hrange]
  exact isClosed_eq (f.continuous.comp continuous_fst)
    ((continuous_proj (E := E)).comp continuous_snd)

namespace ContinuousHermitianMetric

private theorem pullback_graph_external_unit
    {X B : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (f : C(X, B)) (a : CompactSupportKZero X) :
    let g := (ContinuousMap.id X).prodMk f
    let hg : IsProperMap g :=
      isProperMap_of_comp_of_t2 g.continuous continuous_fst isProperMap_id
    compactSupportKZeroPullback g hg (compactSupportKZeroExternalProduct a
      ((compactSupportKZeroCompactEquiv B).symm
        (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1)))) = a := by
  dsimp only
  let g := (ContinuousMap.id X).prodMk f
  have hg : IsProperMap g :=
    isProperMap_of_comp_of_t2 g.continuous continuous_fst isProperMap_id
  let s : C(X × B, B × X) :=
    ⟨(Homeomorph.prodComm B X).symm, (Homeomorph.prodComm B X).symm.continuous⟩
  have hs : IsProperMap s := (Homeomorph.prodComm B X).symm.isProperMap
  let oneB := (compactSupportKZeroCompactEquiv B).symm
    (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1))
  have hswap := compactSupportKZeroExternalProduct_swap oneB a
  change compactSupportKZeroPullback s hs (compactSupportKZeroExternalProduct oneB a) =
    compactSupportKZeroExternalProduct a oneB at hswap
  rw [← hswap, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  exact complexKZeroCompactSupportAction_one f a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Normalize the proper paired base-change map on the whole supported product.
/-- Arbitrary nonproper base change uses the proper paired map on the whole supported product. -/
theorem supportedThomHom_eq_pairedPullback
    {X B : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (f : C(X, B)) (a : CompactSupportKZero X) :
    (h.pullback f).supportedThomHom a =
      compactSupportKZeroPullback
        ⟨pullbackTotalSpaceEmbedding (F := Unit) (E := E) f,
          (inducing_pullbackTotalSpaceEmbedding Unit E f).continuous⟩
        (pullbackTotalSpaceEmbedding_isClosedEmbedding E f).isProperMap
        (compactSupportKZeroExternalProduct a
          (h.supportedThomHom ((compactSupportKZeroCompactEquiv B).symm
            (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1))))) := by
  let p : C(X × B, B) := ContinuousMap.snd
  let g : C(X, X × B) := (ContinuousMap.id X).prodMk f
  have hg : IsProperMap g :=
    isProperMap_of_comp_of_t2 g.continuous continuous_fst isProperMap_id
  let F := (p : X × B → B) *ᵖ E
  let R := (g : X → X × B) *ᵖ F
  let Ef := (f : X → B) *ᵖ E
  let H := h.pullback p
  let d : Iso R Ef := pullbackCompIso (E := E) p g
  let e := pullbackSndTotalHomeomorph E X
  let q := pullbackTotalMap F g
  have hq : IsProperMap q := (pullbackTotalMap_properties F g).1 hg
  let i : C(TotalSpace Unit Ef, TotalSpace Unit R) :=
    ⟨d.totalHomeomorph.symm, d.totalHomeomorph.symm.continuous⟩
  let eMap : C(TotalSpace Unit F, X × TotalSpace Unit E) := ⟨e, e.continuous⟩
  let paired : C(TotalSpace Unit Ef, X × TotalSpace Unit E) :=
    ⟨pullbackTotalSpaceEmbedding f, (inducing_pullbackTotalSpaceEmbedding Unit E f).continuous⟩
  have hpaired : IsProperMap paired :=
    (pullbackTotalSpaceEmbedding_isClosedEmbedding E f).isProperMap
  let oneB := (compactSupportKZeroCompactEquiv B).symm
    (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1))
  let c := compactSupportKZeroExternalProduct a oneB
  let target := compactSupportKZeroExternalProduct a (h.supportedThomHom oneB)
  -- The compact-base unit cancels only after restriction to the original graph.
  have hunit : compactSupportKZeroPullback g hg c = a := pullback_graph_external_unit f a
  have hnatural := DFunLike.congr_fun (H.supportedThomHom_pullback g hg) c
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hunit] at hnatural
  have hiso := DFunLike.congr_fun
    ((H.pullback g).supportedThomHom_iso (h.pullback f) d) a
  rw [AddMonoidHom.comp_apply] at hiso
  have hex := supportedThomHom_externalProduct h a oneB
  have hexInv := congrArg (compactSupportKZeroHomeomorph e.symm) hex
  rw [← AddMonoidHom.comp_apply, compactSupportKZeroHomeomorph_symm,
    AddMonoidHom.id_apply] at hexInv
  change H.supportedThomHom c = compactSupportKZeroPullback eMap e.isProperMap target at hexInv
  -- The chosen composition isomorphism and its inverse preserve the actual fiber vector.
  have hmaps : eMap.comp (q.comp i) = paired := by
    apply ContinuousMap.ext
    intro z
    change (z.proj, (⟨f z.proj, (d.linearEquiv z.proj).symm z.snd⟩ : TotalSpace Unit E)) =
      (z.proj, (⟨f z.proj, z.snd⟩ : TotalSpace Unit E))
    have hv := pullbackCompIso_apply (E := E) p g z.proj
      ((d.linearEquiv z.proj).symm z.snd)
    have hi : (d.linearEquiv z.proj).symm z.snd = z.snd :=
      hv.symm.trans ((d.linearEquiv z.proj).apply_symm_apply z.snd)
    rw [hi]
  rw [← hiso, hnatural, hexInv]
  change compactSupportKZeroPullback i d.totalHomeomorph.symm.isProperMap
    (compactSupportKZeroPullback q hq (compactSupportKZeroPullback eMap e.isProperMap target)) =
    compactSupportKZeroPullback paired hpaired target
  rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  simp only [hmaps]

end ContinuousHermitianMetric

end AtiyahSinger.ComplexBundle
