/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedTwistedProduct
public import AtiyahSinger.Topology.SupportedThomPairedPullback

/-!
# Associated Thom classes with noncompact supported coefficients

Public module ID: M1553.

A specified base-preserving identification of an associated fiber space with
a complex bundle extends to the original principal pullback quotient. If its
associated class is the actual compact-base Thom class, the original twisted
product is exactly the supported Thom image on any LCH pullback base.

The proof retains the paired quotient map and every fiber vector. Only the
full paired maps and homeomorphisms are used for compact-support pullback;
the map from the noncompact parameter to the compact base is unrestricted.
This is the associated-bundle form of SG Appendix C.1 and III.13 (13.16).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology

attribute [local instance] isFiniteRank_pullback t2Space_totalSpace locallyCompactSpace_totalSpace

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [hP : IsPrincipalBundle G projection]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [T2Space B]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_associatedBundlePullback_totalHomeomorph
    (e : AssociatedBundle G P Y ≃ₜ TotalSpace Unit E)
    (he : ∀ z, (e z).proj = associatedBundleProjection (F := Y) hP z)
    (f : C(X, B)) :
    ∃ eF : AssociatedBundle G (PrincipalBundlePullback f projection) Y ≃ₜ
        TotalSpace Unit ((f : X → B) *ᵖ E),
      ∀ z, pullbackTotalSpaceEmbedding (F := Unit) (E := E) f (eF z) =
        ((associatedBundlePullbackProdMap (G := G) (Y := Y) f z).1,
          e (associatedBundlePullbackProdMap (G := G) (Y := Y) f z).2) := by
  let W := AssociatedBundlePullback (G := G) (F := Y) (projection := projection) f
  let Ef := (f : X → B) *ᵖ E
  let j : TotalSpace Unit Ef → X × TotalSpace Unit E := pullbackTotalSpaceEmbedding f
  have hj : IsClosedEmbedding j := pullbackTotalSpaceEmbedding_isClosedEmbedding E f
  let m (z : W) : TotalSpace Unit Ef :=
    ⟨z.val.1, cast (congrArg E ((he z.val.2).trans z.property.symm)) (e z.val.2).snd⟩
  have hm (z : W) : j (m z) = (z.val.1, e z.val.2) := by
    apply Prod.ext
    · rfl
    · exact TotalSpace.mk_cast (F := Unit) (E := E)
        ((he z.val.2).trans z.property.symm) (e z.val.2).snd
  have hcontinuous : Continuous m := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    exact (continuous_subtype_val.fst.prodMk
      (e.continuous.comp continuous_subtype_val.snd)).congr (fun z ↦ (hm z).symm)
  have hcomp : IsEmbedding (j ∘ m) := by
    have h := ((Homeomorph.refl X).prodCongr e).isEmbedding.comp
      (IsEmbedding.subtypeVal (p := fun z : X × AssociatedBundle G P Y ↦
        f z.1 = associatedBundleProjection (F := Y) hP z.2))
    convert h using 1
    funext z
    exact hm z
  have hemb : IsEmbedding m := IsEmbedding.of_comp hcontinuous hj.continuous hcomp
  have hsurj : Function.Surjective m := by
    intro z
    let w := e.symm (⟨f z.proj, z.snd⟩ : TotalSpace Unit E)
    have hw : f z.proj = associatedBundleProjection (F := Y) hP w := by
      have h := he w
      change (e (e.symm (⟨f z.proj, z.snd⟩ : TotalSpace Unit E))).proj = _ at h
      simpa only [e.apply_symm_apply] using h
    refine ⟨⟨(z.proj, w), hw⟩, ?_⟩
    apply hj.injective
    rw [hm]
    change (z.proj, e (e.symm (⟨f z.proj, z.snd⟩ : TotalSpace Unit E))) = _
    rw [e.apply_symm_apply]
    rfl
  let d := IsHomeomorph.homeomorph m
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hemb, hsurj⟩)
  let eP := associatedBundlePullbackHomeomorph (G := G) (F := Y)
    (projection := projection) f
  refine ⟨eP.trans d, ?_⟩
  intro z
  exact hm (eP z)

variable [CompactSpace B] [LocallyCompactSpace X] [T2Space X]
  [LocallyCompactSpace Y] [T2Space Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- The original associated quotient, paired map and chosen class are unchanged.
/-- A specified associated Thom class gives the actual supported Thom map with any coefficient. -/
theorem exists_associatedSupportTwistedProduct_thomHomeomorph
    (h : ContinuousHermitianMetric E)
    (e : AssociatedBundle G P Y ≃ₜ TotalSpace Unit E)
    (he : ∀ z, (e z).proj = associatedBundleProjection (F := Y) hP z)
    (v : EquivariantSupportTripleKZero G Y)
    (hv : letI := associatedBundle_t2Space (Y := Y) hP
      letI := associatedBundle_locallyCompactSpace (Y := Y) hP
      associatedSupportKZero hP v = compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap
        (h.supportedThomHom ((compactSupportKZeroCompactEquiv B).symm
          (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1)))))
    (f : C(X, B)) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    ∃ eF : AssociatedBundle G (PrincipalBundlePullback f projection) Y ≃ₜ
        TotalSpace Unit ((f : X → B) *ᵖ E),
      (∀ z, pullbackTotalSpaceEmbedding (F := Unit) (E := E) f (eF z) =
        ((associatedBundlePullbackProdMap (G := G) (Y := Y) f z).1,
          e (associatedBundlePullbackProdMap (G := G) (Y := Y) f z).2)) ∧
      ∀ a : CompactSupportKZero X,
        associatedSupportTwistedProduct (G := G) (Y := Y) f a v =
          compactSupportKZeroPullback ⟨eF, eF.continuous⟩ eF.isProperMap
            ((h.pullback f).supportedThomHom a) := by
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  let := associatedBundle_locallyCompactSpace (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  obtain ⟨eF, heF⟩ := exists_associatedBundlePullback_totalHomeomorph e he f
  refine ⟨eF, heF, ?_⟩
  intro a
  let W := AssociatedBundle G (PrincipalBundlePullback f projection) Y
  let Z := AssociatedBundle G P Y
  let Ef := (f : X → B) *ᵖ E
  let p : C(W, X × Z) := associatedBundlePullbackProdMap (G := G) (Y := Y) f
  have hp : IsProperMap p := (associatedBundlePullbackProdMap_isClosedEmbedding f).isProperMap
  let q : C(X × Z, X × TotalSpace Unit E) :=
    (ContinuousMap.id X).prodMap ⟨e, e.continuous⟩
  have hq : IsProperMap q := isProperMap_id.prodMap e.isProperMap
  let i : C(W, TotalSpace Unit Ef) := ⟨eF, eF.continuous⟩
  let paired : C(TotalSpace Unit Ef, X × TotalSpace Unit E) :=
    ⟨pullbackTotalSpaceEmbedding f, (inducing_pullbackTotalSpaceEmbedding Unit E f).continuous⟩
  have hpaired : IsProperMap paired :=
    (pullbackTotalSpaceEmbedding_isClosedEmbedding E f).isProperMap
  let c := h.supportedThomHom ((compactSupportKZeroCompactEquiv B).symm
    (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1)))
  have hproduct := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) isProperMap_id ⟨e, e.continuous⟩ e.isProperMap a c
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroPullback p hp
    (compactSupportKZeroExternalProduct a (associatedSupportKZero hP v)) = _
  rw [hv, ← hproduct, (h.supportedThomHom_eq_pairedPullback f a)]
  change compactSupportKZeroPullback p hp
    (compactSupportKZeroPullback q hq (compactSupportKZeroExternalProduct a c)) =
    compactSupportKZeroPullback i eF.isProperMap
      (compactSupportKZeroPullback paired hpaired (compactSupportKZeroExternalProduct a c))
  have hmaps : q.comp p = paired.comp i := ContinuousMap.ext (fun z ↦ (heF z).symm)
  calc
    compactSupportKZeroPullback p hp
        (compactSupportKZeroPullback q hq (compactSupportKZeroExternalProduct a c)) =
        compactSupportKZeroPullback (q.comp p) (hq.comp hp)
          (compactSupportKZeroExternalProduct a c) :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp p q hp hq) _).symm
    _ = compactSupportKZeroPullback (paired.comp i) (hpaired.comp eF.isProperMap)
        (compactSupportKZeroExternalProduct a c) := by simp only [hmaps]
    _ = _ := DFunLike.congr_fun
      (compactSupportKZeroPullback_comp i paired eF.isProperMap hpaired) _

end AtiyahSinger
