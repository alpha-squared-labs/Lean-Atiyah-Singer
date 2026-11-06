/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenExtension

/-!
# Compact-support cohomology on directed open unions

Public module ID: M1659.

Every compact control is contained in one member of a directed open cover.
The original compact-image excision comparison then places each class in
that member, using the existing extension by zero. Equality is detected at
one larger compact control and consequently at a later open member.

This is the compact-support form of the directed-union argument in Hatcher,
Algebraic Topology, Section 3.3. Only the ambient Hausdorff condition is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

private theorem exists_compact_openImage
    (U : Set X) (K : Compacts X) (hK : (K : Set X) ⊆ U) :
    ∃ L : Compacts U,
      openEmbeddingCompactImage (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) L = K := by
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hRange : (K : Set X) ⊆ Set.range f := by
    intro x hx
    exact ⟨⟨x, hK hx⟩, rfl⟩
  let L : Compacts U :=
    ⟨f ⁻¹' (K : Set X), IsInducing.subtypeVal.isCompact_preimage' K.isCompact hRange⟩
  refine ⟨L, ?_⟩
  apply Compacts.ext
  exact Set.image_preimage_eq_of_subset hRange

variable [T2Space X]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_openExtension_of_representative
    (U : Set X) (hU : IsOpen U) (K : Compacts X) (hK : (K : Set X) ⊆ U)
    (p : ℕ) (a : relativeSingularCohomology R ((K : Set X)ᶜ) p) :
    ∃ b : compactSupportCohomology R U p,
      compactSupportCohomologyOpenExtension R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) hU.isOpenEmbedding_subtypeVal p b =
          compactSupportCohomologyClass R X K p a := by
  obtain ⟨L, hL⟩ := exists_compact_openImage U K hK
  subst K
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let J := openEmbeddingCohomologySupportPullback R f hU.isOpenEmbedding_subtypeVal L p
  let := isIso_openEmbeddingCohomologySupportPullback R f hU.isOpenEmbedding_subtypeVal L p
  refine ⟨compactSupportCohomologyClass R U L p (J a), ?_⟩
  rw [compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyClass R X (openEmbeddingCompactImage f L) p
    ((asIso J).inv ((asIso J).hom a)) = _
  rw [Iso.hom_inv_id_apply]

/-- Every original compact-support class comes by actual extension from one directed open member. -/
theorem compactSupportCohomology_exists_openExtension_of_directedCover
    {ι : Type u} [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)
    (p : ℕ) (a : compactSupportCohomology R X p) :
    ∃ (i : ι) (b : compactSupportCohomology R (U i) p),
      compactSupportCohomologyOpenExtension R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
        (hU i).isOpenEmbedding_subtypeVal p b = a := by
  -- Capture the original compact support in one cover member.
  obtain ⟨K, c, hc⟩ := compactSupportCohomology_exists_representative R X p a
  obtain ⟨i, hi⟩ := K.isCompact.elim_directed_cover U hU
    (by rw [hcover]; exact Set.subset_univ _) hdir
  obtain ⟨b, hb⟩ := exists_openExtension_of_representative R (U i) (hU i) K hi p c
  exact ⟨i, b, hb.trans hc⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem openExtension_eq_zero_of_support_relation
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (K : Compacts U) (P : Compacts X)
    (hKP : openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K ≤ P)
    (hPV : (P : Set X) ⊆ V) (p : ℕ)
    (c : relativeSingularCohomology R ((K : Set U)ᶜ) p)
    (d : relativeSingularCohomology R
      ((openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K : Set X)ᶜ) p)
    (hc : openEmbeddingCohomologySupportPullback R (ContinuousMap.subtypeVal U)
      hU.isOpenEmbedding_subtypeVal K p d = c)
    (hzero : (compactSupportCohomologyFunctor R X p).map (homOfLE hKP)
      d = 0) :
    compactSupportCohomologyOpenExtension R (ContinuousMap.inclusion hUV)
      (IsOpenEmbedding.inclusion hUV (hU.preimage continuous_subtype_val)) p
        (compactSupportCohomologyClass R U K p c) = 0 := by
  /- Lift the actual larger ambient compact control into V. Naturality of
  the same excision pullbacks transfers its zero relation to V before
  applying the original compact-support injection. -/
  obtain ⟨Q, hQ⟩ := exists_compact_openImage V P hPV
  subst P
  let f := ContinuousMap.subtypeVal U
  let g := ContinuousMap.subtypeVal V
  let j := ContinuousMap.inclusion hUV
  have hj : IsOpenEmbedding j :=
    IsOpenEmbedding.inclusion hUV (hU.preimage continuous_subtype_val)
  let L := openEmbeddingCompactImage j K
  let KX := openEmbeddingCompactImage f K
  have hLQ : L ≤ Q := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hKP (show f x ∈ (KX : Set X) from ⟨x, hx, rfl⟩)
    have hyx : y = j x := Subtype.ext heq
    exact hyx ▸ hy
  have hgL : Set.MapsTo g ((L : Set V)ᶜ) ((KX : Set X)ᶜ) := by
    intro z hz
    rintro ⟨x, hx, heq⟩
    apply hz
    exact ⟨x, hx, Subtype.ext heq⟩
  let qf := openEmbeddingCohomologySupportPullback R f hU.isOpenEmbedding_subtypeVal K p
  let qj := openEmbeddingCohomologySupportPullback R j hj K p
  let qg := relativeSingularCohomologyPullback R g hgL p
  let qQ := openEmbeddingCohomologySupportPullback R g hV.isOpenEmbedding_subtypeVal Q p
  let := isIso_openEmbeddingCohomologySupportPullback R j hj K p
  have hcomp : qg ≫ qj = qf := by
    dsimp only [qg, qj, qf, openEmbeddingCohomologySupportPullback]
    rw [← relativeSingularCohomologyPullback_comp]
    rfl
  have hinv : (asIso qj).inv c = qg d := by
    apply (ConcreteCategory.bijective_of_isIso qj).injective
    change (asIso qj).hom ((asIso qj).inv c) = qj (qg d)
    rw [Iso.inv_hom_id_apply]
    have h := congrArg (fun k ↦ k d) hcomp
    change qj (qg d) = qf d at h
    exact (h.trans hc).symm
  let rV := (compactSupportCohomologyFunctor R V p).map (homOfLE hLQ)
  let rX := (compactSupportCohomologyFunctor R X p).map (homOfLE hKP)
  have hsquare : rX ≫ qQ = qg ≫ rV :=
    relativeSingularCohomologyPullback_restriction R g
      (Set.compl_subset_compl.mpr hLQ) (Set.compl_subset_compl.mpr hKP) _ hgL p
  have hrelation : rV ((asIso qj).inv c) = 0 := by
    rw [hinv]
    have h := congrArg (fun k ↦ k d) hsquare
    change qQ (rX d) = rV (qg d) at h
    have hz : rX d = 0 := hzero
    rw [hz, map_zero] at h
    exact h.symm
  rw [compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyClass R V L p ((asIso qj).inv c) = 0
  have hleg := congrArg (fun k ↦ k ((asIso qj).inv c))
    (colimit.w (compactSupportCohomologyFunctor R V p) (homOfLE hLQ))
  change compactSupportCohomologyClass R V Q p (rV ((asIso qj).inv c)) = _ at hleg
  rw [hrelation, map_zero] at hleg
  exact hleg.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A class that vanishes after ambient extension already vanishes at a later open member. -/
theorem compactSupportCohomology_exists_openExtension_eq_zero_of_directedCover
    {ι : Type u} [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)
    (p : ℕ) (i : ι) (a : compactSupportCohomology R (U i) p)
    (hzero : compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal (U i))
      (hU i).isOpenEmbedding_subtypeVal p a = 0) :
    ∃ (j : ι) (hij : U i ⊆ U j),
      compactSupportCohomologyOpenExtension R (ContinuousMap.inclusion hij)
        (IsOpenEmbedding.inclusion hij ((hU i).preimage continuous_subtype_val)) p a = 0 := by
  /- Detect the given zero in the original compact-support colimit. Its
  witnessing compact enlargement lies in a later open member, where
  the same excision square witnesses zero before ambient extension. -/
  obtain ⟨K, c, rfl⟩ := compactSupportCohomology_exists_representative R (U i) p a
  let f := ContinuousMap.subtypeVal (U i)
  let KX := openEmbeddingCompactImage f K
  let q := openEmbeddingCohomologySupportPullback R f (hU i).isOpenEmbedding_subtypeVal K p
  let := isIso_openEmbeddingCohomologySupportPullback R f
    (hU i).isOpenEmbedding_subtypeVal K p
  let d := (asIso q).inv c
  rw [compactSupportCohomologyOpenExtension_representative] at hzero
  change compactSupportCohomologyClass R X KX p d = 0 at hzero
  have hclasses : compactSupportCohomologyClass R X KX p d =
      compactSupportCohomologyClass R X KX p 0 := by
    simpa only [map_zero] using hzero
  obtain ⟨P, hKP, _, hP⟩ := (compactSupportCohomologyClass_eq_iff R X d 0).mp hclasses
  rw [map_zero] at hP
  obtain ⟨k, hk⟩ := P.isCompact.elim_directed_cover U hU
    (by rw [hcover]; exact Set.subset_univ _) hdir
  obtain ⟨j, hij, hkj⟩ := hdir i k
  refine ⟨j, hij, ?_⟩
  exact openExtension_eq_zero_of_support_relation R (U i) (U j) (hU i) (hU j)
    hij K P hKP (hk.trans hkj) p c d (Iso.inv_hom_id_apply (asIso q) c) hP

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Equal ambient extensions become equal after inclusion into one later directed open member. -/
theorem compactSupportCohomology_exists_openExtension_eq_of_directedCover
    {ι : Type u} [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)
    (p : ℕ) (i j : ι) (a : compactSupportCohomology R (U i) p)
    (b : compactSupportCohomology R (U j) p)
    (hab : compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal (U i))
      (hU i).isOpenEmbedding_subtypeVal p a =
        compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal (U j))
          (hU j).isOpenEmbedding_subtypeVal p b) :
    ∃ (k : ι) (hik : U i ⊆ U k) (hjk : U j ⊆ U k),
      compactSupportCohomologyOpenExtension R (ContinuousMap.inclusion hik)
        (IsOpenEmbedding.inclusion hik ((hU i).preimage continuous_subtype_val)) p a =
      compactSupportCohomologyOpenExtension R (ContinuousMap.inclusion hjk)
        (IsOpenEmbedding.inclusion hjk ((hU j).preimage continuous_subtype_val)) p b := by
  /- Put both classes in one stage, apply the preceding zero-detection
  result to their difference, and use the specified extension composition
  to retain the original two inclusion maps. -/
  let ext (i : ι) := compactSupportCohomologyOpenExtension R
    (ContinuousMap.subtypeVal (U i)) (hU i).isOpenEmbedding_subtypeVal p
  let inc (i j : ι) (hij : U i ⊆ U j) := compactSupportCohomologyOpenExtension R
    (ContinuousMap.inclusion hij)
      (IsOpenEmbedding.inclusion hij ((hU i).preimage continuous_subtype_val)) p
  have hcomp (i j : ι) (hij : U i ⊆ U j) : inc i j hij ≫ ext j = ext i := by
    simpa only [ContinuousMap.subtypeVal_comp_inclusion] using
      (compactSupportCohomologyOpenExtension_comp R (ContinuousMap.inclusion hij)
        (IsOpenEmbedding.inclusion hij ((hU i).preimage continuous_subtype_val))
        (ContinuousMap.subtypeVal (U j)) (hU j).isOpenEmbedding_subtypeVal p).symm
  obtain ⟨k, hik, hjk⟩ := hdir i j
  have hzero : ext k (inc i k hik a - inc j k hjk b) = 0 := by
    rw [map_sub]
    have hi := congrArg (fun f ↦ f a) (hcomp i k hik)
    have hj := congrArg (fun f ↦ f b) (hcomp j k hjk)
    change ext k (inc i k hik a) = ext i a at hi
    change ext k (inc j k hjk b) = ext j b at hj
    rw [hi, hj, hab, sub_self]
  obtain ⟨l, hkl, hl⟩ :=
    compactSupportCohomology_exists_openExtension_eq_zero_of_directedCover R U hU
      hdir hcover p k (inc i k hik a - inc j k hjk b) hzero
  refine ⟨l, hik.trans hkl, hjk.trans hkl, ?_⟩
  change inc k l hkl (inc i k hik a - inc j k hjk b) = 0 at hl
  rw [map_sub, sub_eq_zero] at hl
  have hinc (i k l : ι) (hik : U i ⊆ U k) (hkl : U k ⊆ U l) :
      inc i k hik ≫ inc k l hkl = inc i l (hik.trans hkl) := by
    simpa only [ContinuousMap.inclusion_comp_inclusion] using
      (compactSupportCohomologyOpenExtension_comp R (ContinuousMap.inclusion hik)
        (IsOpenEmbedding.inclusion hik ((hU i).preimage continuous_subtype_val))
        (ContinuousMap.inclusion hkl)
        (IsOpenEmbedding.inclusion hkl ((hU k).preimage continuous_subtype_val)) p).symm
  have hi := congrArg (fun f ↦ f a) (hinc i k l hik hkl)
  have hj := congrArg (fun f ↦ f b) (hinc j k l hjk hkl)
  exact hi.symm.trans (hl.trans hj)

end AtiyahSinger
