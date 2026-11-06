/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportKZeroComparison

/-!
# Proper functoriality of geometric support classes

Public module ID: M2197.

D07/K02. Pullback on the presented group descends the actual bundle pullback;
it is not chosen as an arbitrary abstract homomorphism. Properness controls the
inverse image of every compact support. Basic presentation functoriality needs
no local compactness. The comparison with compactification K retains LCH bases.
Sources: SG I.9.26; KA II.4.1–4.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


set_option backward.isDefEq.respectTransparency.types false in
/-- The actual identity-pullback square, reused for the presented and stable quotients. -/
private theorem SupportBundleTriple.isIsomorphic_pullback_id (a : SupportBundleTriple X) :
    (a.pullback (ContinuousMap.id X) isProperMap_id).IsIsomorphic a := by
  -- The identity-pullback isomorphisms preserve each underlying fiber vector.
  obtain ⟨u, hu⟩ := exists_pullback_id_iso (E := a.source.Fiber)
  obtain ⟨w, hw⟩ := exists_pullback_id_iso (E := a.target.Fiber)
  -- Both controls and all underlying vectors remain unchanged.
  refine ⟨a.datum.control, a.datum.isCompact_control, Set.Subset.refl _,
    Set.Subset.refl _, u, w, ?_⟩
  intro x v
  have hl := (a.datum.pullback (ContinuousMap.id X) isProperMap_id).enlarge_apply
    a.datum.control a.datum.isCompact_control (Set.Subset.refl _) x v
  have hp := RelativeTriple.pullback_apply a.datum.boundary (ContinuousMap.id X) x v
  have hr := a.datum.enlarge_apply a.datum.control a.datum.isCompact_control
    (Set.Subset.refl _) x v

  exact (hw x _).trans (((hl.trans hp).trans hr.symm).trans
    (congrArg ((a.datum.enlarge a.datum.control a.datum.isCompact_control
      (Set.Subset.refl _)).boundary.linearEquiv x) (hu x v).symm))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual composition square, reused for both original support quotients. -/
private theorem SupportBundleTriple.isIsomorphic_pullback_comp (a : SupportBundleTriple X)
    (f : C(Y, X)) (g : C(Z, Y)) (hf : IsProperMap f) (hg : IsProperMap g) :
    ((a.pullback f hf).pullback g hg).IsIsomorphic
      (a.pullback (f.comp g) (hf.comp hg)) := by
  obtain ⟨u, hu⟩ := exists_pullback_comp_iso (E := a.source.Fiber) f g
  obtain ⟨w, hw⟩ := exists_pullback_comp_iso (E := a.target.Fiber) f g
  let K := (f.comp g) ⁻¹' a.datum.control
  have hK : IsCompact K := (hf.comp hg).isCompact_preimage a.datum.isCompact_control
  -- The iterated and composite inverse images are the same specified compact set.
  refine ⟨K, hK, Set.Subset.refl _, Set.Subset.refl _,
    u, w, ?_⟩
  intro x v
  have hl := ((a.datum.pullback f hf).pullback g hg).enlarge_apply K hK
    (Set.Subset.refl _) x v
  have hp := RelativeTriple.pullback_apply (a.datum.boundary.pullback f) g x v
  have hq := RelativeTriple.pullback_apply a.datum.boundary f
    ⟨g x, x.property⟩ v
  have hr := (a.datum.pullback (f.comp g) (hf.comp hg)).enlarge_apply K hK
    (Set.Subset.refl _) x v
  have hc := RelativeTriple.pullback_apply a.datum.boundary (f.comp g) x v
  -- Both original boundary chains evaluate on the same vector over f(g(x)).
  exact (hw x _).trans (((hl.trans (hp.trans hq)).trans (hr.trans hc).symm).trans
    (congrArg (((a.datum.pullback (f.comp g) (hf.comp hg)).enlarge K hK
      (Set.Subset.refl _)).boundary.linearEquiv x) (hu x v).symm))

attribute [local instance] sumTopology isFiniteRank_sum

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback respects the direct-sum relation of the presented group. -/
theorem SupportBundleTriple.kZeroClass_pullback_sum (a b : SupportBundleTriple X)
    (f : C(Y, X)) (hf : IsProperMap f) :
    ((a.sum b).pullback f hf).kZeroClass =
      (a.pullback f hf).kZeroClass + (b.pullback f hf).kZeroClass := by
  /- The canonical pullback/direct-sum bundle comparisons preserve the two vector coordinates
  and the boundary square outside the inverse image of the union control. Apply isomorphism
  invariance and the defining sum relation. -/
  have compare (J K : FiniteBundle X) :
      ∃ e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber,
        ∀ y w, e.linearEquiv y w = w := by
    let e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber :=
      { linearEquiv y := LinearEquiv.refl ℂ (J.Fiber (f y) × K.Fiber (f y))
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply Continuous.prodMk
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
              (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
              (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber f).continuous_iff]
          apply ((Pullback.continuous_proj Unit J.Fiber f).comp continuous_sum_fst).prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit J.Fiber f).comp continuous_sum_fst).prodMk
            ((Pullback.continuous_lift Unit K.Fiber f).comp continuous_sum_snd) }
    exact ⟨e, fun _ _ ↦ rfl⟩
  obtain ⟨u, hu⟩ := compare a.source b.source
  obtain ⟨v, hv⟩ := compare a.target b.target
  let R := a.datum.control ∪ b.datum.control
  have hR : IsCompact R := a.datum.isCompact_control.union b.datum.isCompact_control
  let K := f ⁻¹' R
  have hK : IsCompact K := hf.isCompact_preimage hR
  have hi : ((a.sum b).pullback f hf).IsIsomorphic
      ((a.pullback f hf).sum (b.pullback f hf)) := by
    refine ⟨K, hK, Set.Subset.refl _, Set.Subset.refl _, u, v, ?_⟩
    intro y w
    let x : (Rᶜ : Set X) := ⟨f y, y.property⟩
    have hl := ((a.datum.sum b.datum).pullback f hf).enlarge_apply K hK
      (Set.Subset.refl _) y w
    have hp := RelativeTriple.pullback_apply (a.datum.sum b.datum).boundary f y w
    have hs := RelativeTriple.sum_apply
      (a.datum.enlarge R hR Set.subset_union_left).boundary
      (b.datum.enlarge R hR Set.subset_union_right).boundary x w
    have ha := a.datum.enlarge_apply R hR Set.subset_union_left x w.1
    have hb := b.datum.enlarge_apply R hR Set.subset_union_right x w.2
    have hleft := hl.trans (hp.trans (hs.trans (congrArg₂ Prod.mk ha hb)))
    have hr := ((a.datum.pullback f hf).sum (b.datum.pullback f hf)).enlarge_apply
      K hK (Set.Subset.refl _) y w
    have ht := RelativeTriple.sum_apply
      ((a.datum.pullback f hf).enlarge K hK Set.subset_union_left).boundary
      ((b.datum.pullback f hf).enlarge K hK Set.subset_union_right).boundary y w
    have hpa := (a.datum.pullback f hf).enlarge_apply K hK Set.subset_union_left y w.1
    have hpb := (b.datum.pullback f hf).enlarge_apply K hK Set.subset_union_right y w.2
    have hqa := RelativeTriple.pullback_apply a.datum.boundary f
      ⟨y.val, fun hy ↦ y.property (Or.inl hy)⟩ w.1
    have hqb := RelativeTriple.pullback_apply b.datum.boundary f
      ⟨y.val, fun hy ↦ y.property (Or.inr hy)⟩ w.2
    have hright := hr.trans (ht.trans (congrArg₂ Prod.mk (hpa.trans hqa) (hpb.trans hqb)))
    change v.linearEquiv y _ = _
    erw [hu, hv]
    exact hleft.trans hright.symm
  -- The original geometric comparison supplies precisely the relation needed for descent.
  exact (SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _ hi).trans
    (SupportBundleTriple.kZeroClass_sum _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of an identity triple has zero class. -/
theorem supportBundleTriple_kZeroClass_pullback_identity (E : FiniteBundle X)
    (f : C(Y, X)) (hf : IsProperMap f) :
    ((SupportBundleTriple.identity E).pullback f hf).kZeroClass = 0 := by
  /- The pulled-back global identity is identity on the pulled-back bundle. Its control is the
  inverse image of the empty set, hence empty; identify its class with the identity
  relation. -/
  have h : ((SupportBundleTriple.identity E).pullback f hf).IsIsomorphic
      (SupportBundleTriple.identity (E.pullback f)) := by
    -- Empty control and the two actual identity maps give the original square.
    refine ⟨∅, isCompact_empty, by simp [SupportBundleTriple.pullback,
      SupportBundleTriple.identity, CompactSupportTriple.pullback, CompactSupportTriple.ofIso],
      Set.Subset.refl _, Iso.refl _, Iso.refl _, ?_⟩
    intro x v
    have hl := ((CompactSupportTriple.ofIso (Iso.refl E.Fiber)).pullback f hf).enlarge_apply
      ∅ isCompact_empty (by simp [CompactSupportTriple.pullback, CompactSupportTriple.ofIso]) x v
    have hp := RelativeTriple.pullback_apply ((Iso.refl E.Fiber).restrict (∅ : Set X)ᶜ)
      f ⟨x.val, by simp⟩ v
    have hr := (CompactSupportTriple.ofIso (Iso.refl (E.pullback f).Fiber)).enlarge_apply
      ∅ isCompact_empty (Set.Subset.refl _) x v
    exact (hl.trans hp).trans hr.symm
  exact (SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _ h).trans
    (SupportBundleTriple.kZeroClass_identity _)

/-- Descend actual triple pullback through the defining group relations. -/
def supportTripleKZeroPullback (f : C(Y, X)) (hf : IsProperMap f) :
    SupportTripleKZero X →+ SupportTripleKZero Y :=
  (supportTripleKZero_universal_property X (fun a ↦ (a.pullback f hf).kZeroClass)
    (fun a b h ↦ (a.pullback f hf).kZeroClass_eq_of_isIsomorphic
      (b.pullback f hf) (h.pullback f hf))
    (fun a b ↦ a.kZeroClass_pullback_sum b f hf)
    (fun E ↦ supportBundleTriple_kZeroClass_pullback_identity E f hf)).choose

/-- The presented-group pullback has the actual triple pullback as generator value. -/
theorem supportTripleKZeroPullback_apply (f : C(Y, X)) (hf : IsProperMap f)
    (a : SupportBundleTriple X) :
    supportTripleKZeroPullback f hf a.kZeroClass = (a.pullback f hf).kZeroClass := by
  /- Extract the generator equation from the same universal-property witness that defines the
  homomorphism. -/
  exact (supportTripleKZero_universal_property X (fun a ↦ (a.pullback f hf).kZeroClass)
    (fun a b h ↦ (a.pullback f hf).kZeroClass_eq_of_isIsomorphic
      (b.pullback f hf) (h.pullback f hf))
    (fun a b ↦ a.kZeroClass_pullback_sum b f hf)
    (fun E ↦ supportBundleTriple_kZeroClass_pullback_identity E f hf)).choose_spec.1 a

/-- Identity proper pullback acts identically on the triple group. -/
theorem supportTripleKZeroPullback_id :
    supportTripleKZeroPullback (ContinuousMap.id X) isProperMap_id =
      AddMonoidHom.id (SupportTripleKZero X) := by
  /- Check the two homomorphisms on every triple generator. Pullback along identity has the
  vector-preserving identity bundle comparisons and unchanged control, so the classes agree.
  Uniqueness in the presentation extends equality to the group. -/
  -- The original presentation generators suffice to identify these additive maps.
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (supportTripleKZeroRelations X) z
  have heq : (supportTripleKZeroPullback (ContinuousMap.id X) isProperMap_id).comp
      (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) =
      (AddMonoidHom.id (SupportTripleKZero X)).comp
        (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change supportTripleKZeroPullback (ContinuousMap.id X) isProperMap_id a.kZeroClass =
      a.kZeroClass
    exact (supportTripleKZeroPullback_apply (ContinuousMap.id X) isProperMap_id a).trans
      (SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _ a.isIsomorphic_pullback_id)
  exact DFunLike.congr_fun heq w

/-- Triple-group proper pullback composes contravariantly. -/
theorem supportTripleKZeroPullback_comp (f : C(Y, X)) (g : C(Z, Y))
    (hf : IsProperMap f) (hg : IsProperMap g) :
    supportTripleKZeroPullback (f.comp g) (hf.comp hg) =
      (supportTripleKZeroPullback g hg).comp (supportTripleKZeroPullback f hf) := by
  /- On each generator use the actual iterated-pullback isomorphisms. The two compact controls
  are equal inverse images and the boundary maps agree on vectors. The presentation
  universal property gives equality of homomorphisms. -/
  -- Compare the same triple generators, using the vector-preserving composition square.
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (supportTripleKZeroRelations X) z
  have heq : (supportTripleKZeroPullback (f.comp g) (hf.comp hg)).comp
      (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) =
      ((supportTripleKZeroPullback g hg).comp (supportTripleKZeroPullback f hf)).comp
        (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change supportTripleKZeroPullback (f.comp g) (hf.comp hg) a.kZeroClass =
      supportTripleKZeroPullback g hg (supportTripleKZeroPullback f hf a.kZeroClass)
    rw [supportTripleKZeroPullback_apply, supportTripleKZeroPullback_apply,
      supportTripleKZeroPullback_apply]
    exact (SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _
      (a.isIsomorphic_pullback_comp f g hf hg)).symm
  exact DFunLike.congr_fun heq w

/-- Pull back the actual stable quotient by pulling back representatives. -/
def stableSupportTripleClassPullback (f : C(Y, X)) (hf : IsProperMap f) :
    StableSupportTripleClass X → StableSupportTripleClass Y :=
  Quotient.map (fun a ↦ a.pullback f hf) (fun _ _ h ↦ h.pullback f hf)

/-- Stable quotient pullback retains its original representative. -/
theorem stableSupportTripleClassPullback_apply (f : C(Y, X)) (hf : IsProperMap f)
    (a : SupportBundleTriple X) :
    stableSupportTripleClassPullback f hf a.stableClass = (a.pullback f hf).stableClass := by
  /- Evaluate the quotient map on a quotient constructor. Its specified representative function
  is the actual proper pullback of triples. -/
  rfl

/-- Identity acts identically on stable geometric support classes. -/
theorem stableSupportTripleClassPullback_id (a : StableSupportTripleClass X) :
    stableSupportTripleClassPullback (ContinuousMap.id X) isProperMap_id a = a := by
  /- Choose a triple representative. The identity-pullback bundle comparisons give an
  isomorphism at infinity, hence a stable isomorphism and equality in the actual quotient. -/
  induction a using Quotient.inductionOn with
  | _ a =>
    apply (SupportBundleTriple.stableClass_eq_iff _ _).mpr
    exact SupportBundleTriple.isStablyIsomorphic_of_isIsomorphic _ _
      a.isIsomorphic_pullback_id

/-- Stable quotient pullback composes using the same inverse-image controls. -/
theorem stableSupportTripleClassPullback_comp (f : C(Y, X)) (g : C(Z, Y))
    (hf : IsProperMap f) (hg : IsProperMap g) (a : StableSupportTripleClass X) :
    stableSupportTripleClassPullback (f.comp g) (hf.comp hg) a =
      stableSupportTripleClassPullback g hg (stableSupportTripleClassPullback f hf a) := by
  /- On a representative the iterated-pullback bundle comparisons identify the two exterior
  maps on the same inverse-image compact control. Stable quotient effectiveness gives
  equality. -/
  induction a using Quotient.inductionOn with
  | _ a =>
    apply (SupportBundleTriple.stableClass_eq_iff _ _).mpr
    exact SupportBundleTriple.isStablyIsomorphic_of_isIsomorphic _ _
      (a.isIsomorphic_pullback_comp f g hf hg).symm

/-- The stable-to-group comparison commutes with actual proper pullback. -/
theorem stableSupportTripleClassToKZero_pullback (f : C(Y, X)) (hf : IsProperMap f)
    (a : StableSupportTripleClass X) :
    stableSupportTripleClassToKZero Y (stableSupportTripleClassPullback f hf a) =
      supportTripleKZeroPullback f hf (stableSupportTripleClassToKZero X a) := by
  /- Reduce to a representative triple. Both routes are its actual pulled-back generator by the
  quotient and presentation generator formulas. -/
  induction a using Quotient.inductionOn with
  | _ a => exact (supportTripleKZeroPullback_apply f hf a).symm

/-- Transport triple-group classes by actual pullback along the inverse homeomorphism. -/
def supportTripleKZeroHomeomorph (e : X ≃ₜ Y) : SupportTripleKZero X →+ SupportTripleKZero Y :=
  supportTripleKZeroPullback ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap

/-- The specified homeomorphism transport is bijective. -/
theorem supportTripleKZeroHomeomorph_bijective (e : X ≃ₜ Y) :
    Function.Bijective (supportTripleKZeroHomeomorph e) := by
  /- Transport along the inverse homeomorphism reverses this map. Proper pullback identity and
  composition give both inverse identities, hence bijectivity. -/
  let f : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  let g : C(X, Y) := ⟨e, e.continuous⟩
  have hfg : f.comp g = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  have hgf : g.comp f = ContinuousMap.id Y := by
    ext y
    exact e.apply_symm_apply y
  -- The inverse homeomorphism induces the inverse additive map, on these same classes.
  have hleft : Function.LeftInverse (supportTripleKZeroPullback g e.isProperMap)
      (supportTripleKZeroPullback f e.symm.isProperMap) := by
    intro x
    have h := DFunLike.congr_fun
      (supportTripleKZeroPullback_comp f g e.symm.isProperMap e.isProperMap) x
    have hid : supportTripleKZeroPullback (f.comp g)
        (e.symm.isProperMap.comp e.isProperMap) = AddMonoidHom.id (SupportTripleKZero X) := by
      simpa only [hfg] using (supportTripleKZeroPullback_id (X := X))
    exact h.symm.trans (DFunLike.congr_fun hid x)
  have hright : Function.RightInverse (supportTripleKZeroPullback g e.isProperMap)
      (supportTripleKZeroPullback f e.symm.isProperMap) := by
    intro y
    have h := DFunLike.congr_fun
      (supportTripleKZeroPullback_comp g f e.isProperMap e.symm.isProperMap) y
    have hid : supportTripleKZeroPullback (g.comp f)
        (e.isProperMap.comp e.symm.isProperMap) = AddMonoidHom.id (SupportTripleKZero Y) := by
      simpa only [hgf] using (supportTripleKZeroPullback_id (X := Y))
    exact h.symm.trans (DFunLike.congr_fun hid y)
  exact ⟨hleft.injective, hright.surjective⟩

/-- The transport equivalence keeps its specified pullback as forward map. -/
def supportTripleKZeroHomeomorphEquiv (e : X ≃ₜ Y) :
    SupportTripleKZero X ≃+ SupportTripleKZero Y :=
  AddEquiv.ofBijective _ (supportTripleKZeroHomeomorph_bijective e)

/-- Homeomorphism transport carries the original triple to its inverse pullback. -/
theorem supportTripleKZeroHomeomorph_apply (e : X ≃ₜ Y) (a : SupportBundleTriple X) :
    supportTripleKZeroHomeomorph e a.kZeroClass =
      (a.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap).kZeroClass := by
  /- Unfold the specified homeomorphism map and evaluate the proper pullback on its generator.
  No additional choice enters the forward map. -/
  exact supportTripleKZeroPullback_apply ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap a

variable [hLX : LocallyCompactSpace X] [hTX : T2Space X]
  [hLY : LocallyCompactSpace Y] [hTY : T2Space Y]
include hLX hTX hLY hTY

/-- The specified compactification comparison commutes with proper pullback. -/
theorem supportTripleKZeroToCompactSupport_pullback (f : C(Y, X)) (hf : IsProperMap f) :
    (supportTripleKZeroToCompactSupport (X := Y)).comp (supportTripleKZeroPullback f hf) =
      (compactSupportKZeroPullback f hf).comp (supportTripleKZeroToCompactSupport (X := X)) := by
  /- On every generator, both comparison formulas reduce the equality to proper naturality of
  the constructed compact-window difference. Extend from generators by the presentation
  universal property. -/
  apply AddMonoidHom.ext
  intro z
  -- Every original support-group class is represented by one actual support triple.
  obtain ⟨a, rfl⟩ := supportBundleTriple_kZeroClass_surjective z
  change supportTripleKZeroToCompactSupport (supportTripleKZeroPullback f hf a.kZeroClass) =
    compactSupportKZeroPullback f hf (supportTripleKZeroToCompactSupport a.kZeroClass)
  rw [supportTripleKZeroPullback_apply, supportTripleKZeroToCompactSupport_apply,
    supportTripleKZeroToCompactSupport_apply]
  -- Both routes now use the same pulled-back bundles, boundary and inverse-image control.
  exact a.compactSupportClass_pullback f hf

end AtiyahSinger.ComplexBundle
