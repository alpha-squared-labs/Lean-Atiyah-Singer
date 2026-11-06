/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyComparison
public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.OnePointCohomology
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Compact supports and compact-base slice compactification

Public module ID: M1686.

The original open inclusion of `X × Y` in `X × OnePoint Y` retains the whole
boundary `X × {∞}`. Cofinal contractible neighborhoods at infinity in `Y`
make the original compact-support comparison bijective when `X` is compact.
The boundary projection is an actual retraction, so its relative cohomology
embeds in ordinary cohomology. These two facts provide the detection needed
for the compact-base action on supported characteristic classes.

Source: singular excision and homotopy invariance, applied to the actual
compact-support colimit; no general comparison with quotient cohomology is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits OnePoint TopologicalSpace Topology
open scoped unitInterval

universe u

variable (R : Type) [CommRing R]
variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace Y] [T2Space X] [T2Space Y]

/-- The actual finite inclusion into the compact-base slice compactification. -/
def compactSupportSliceInclusion : C(X × Y, X × OnePoint Y) :=
  ⟨fun p ↦ (p.1, (p.2 : OnePoint Y)), continuous_fst.prodMk
    (OnePoint.continuous_coe.comp continuous_snd)⟩

omit [LocallyCompactSpace Y] [T2Space X] [T2Space Y] in
/-- The slice inclusion is an open embedding of the original product space. -/
theorem isOpenEmbedding_compactSupportSliceInclusion :
    IsOpenEmbedding (compactSupportSliceInclusion X Y) :=
  IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe

/-- The original compact-support colimit compared with the full slice boundary. -/
def compactSupportCohomologyToSlice (n : ℕ) :
    compactSupportCohomology R (X × Y) n ⟶
      relativeSingularCohomology R ((Set.range (compactSupportSliceInclusion X Y))ᶜ) n :=
  compactSupportCohomologyToCompactification R (compactSupportSliceInclusion X Y)
    (isOpenEmbedding_compactSupportSliceInclusion X Y) n

omit [LocallyCompactSpace Y] [T2Space X] [T2Space Y] in
/-- The slice boundary retracts from the ambient product, retaining the first coordinate. -/
theorem relativeSingularCohomologyToOrdinary_slice_injective (n : ℕ) :
    Function.Injective (relativeSingularCohomologyToOrdinary R
      ((Set.range (compactSupportSliceInclusion X Y))ᶜ) n) := by
  let A : Set (X × OnePoint Y) := (Set.range (compactSupportSliceInclusion X Y))ᶜ
  have hinf (x : X) : (x, (∞ : OnePoint Y)) ∈ A := by
    rintro ⟨⟨x', y⟩, h⟩
    exact OnePoint.coe_ne_infty y (congrArg Prod.snd h)
  have hsecond (z : A) : z.val.2 = ∞ := by
    cases h : z.val.2 using OnePoint.rec with
    | infty => rfl
    | coe y =>
      exact False.elim (z.property ⟨(z.val.1, y), Prod.ext rfl h.symm⟩)
  let r : C(X × OnePoint Y, A) :=
    ⟨fun z ↦ ⟨(z.1, ∞), hinf z.1⟩,
      (continuous_fst.prodMk continuous_const).subtype_mk _⟩
  apply relativeSingularCohomologyToOrdinary_injective_of_retraction R A r
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact Prod.ext rfl (hsecond z).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cofinal contractible complements in the second factor give the original slice comparison. -/
theorem compactSupportCohomologyToSlice_bijective [CompactSpace X]
    (h : ∀ K : Compacts Y, ∃ L : Compacts Y, K ≤ L ∧
      ContractibleSpace ((((↑) : Y → OnePoint Y) '' (L : Set Y))ᶜ : Set (OnePoint Y)))
    (n : ℕ) : Function.Bijective (compactSupportCohomologyToSlice R X Y n) := by
  let j := compactSupportSliceInclusion X Y
  apply compactSupportCohomologyToCompactification_bijective R j
    (isOpenEmbedding_compactSupportSliceInclusion X Y)
  intro K
  obtain ⟨L, hKL, hL⟩ := h (K.map Prod.snd continuous_snd)
  let P : Compacts (X × Y) := ⟨Set.univ ×ˢ (L : Set Y), isCompact_univ.prod L.isCompact⟩
  refine ⟨P, ?_, ?_⟩
  · intro z hz
    exact ⟨Set.mem_univ _, hKL ⟨z, hz, rfl⟩⟩
  · intro k
    let A : Set (X × OnePoint Y) := (Set.range j)ᶜ
    let B : Set (X × OnePoint Y) := (openEmbeddingCompactImage j P : Set _)ᶜ
    let N : Set (OnePoint Y) := (((↑) : Y → OnePoint Y) '' (L : Set Y))ᶜ
    let : ContractibleSpace N := hL
    have hinf (x : X) : (x, (∞ : OnePoint Y)) ∈ A := by
      rintro ⟨⟨x', y⟩, heq⟩
      exact OnePoint.coe_ne_infty y (congrArg Prod.snd heq)
    have hsecond (z : A) : z.val.2 = ∞ := by
      cases heq : z.val.2 using OnePoint.rec with
      | infty => rfl
      | coe y =>
        exact False.elim (z.property ⟨(z.val.1, y), Prod.ext rfl heq.symm⟩)
    have hB (z : X × OnePoint Y) : z ∈ B ↔ z.2 ∈ N := by
      constructor
      · intro hz ⟨y, hy, heq⟩
        exact hz ⟨(z.1, y), ⟨Set.mem_univ _, hy⟩, Prod.ext rfl heq⟩
      · intro hz ⟨p, hp, heq⟩
        exact hz ⟨p.2, hp.2, congrArg Prod.snd heq⟩
    let pinf : N := ⟨∞, OnePoint.infty_notMem_image_coe⟩
    let i : C(A, B) := compactificationComplementInclusion j P
    let r : C(B, A) :=
      ⟨fun z ↦ ⟨(z.val.1, ∞), hinf z.val.1⟩,
        ((continuous_fst.comp continuous_subtype_val).prodMk
          continuous_const).subtype_mk _⟩
    have hri : r.comp i = ContinuousMap.id A := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact Prod.ext rfl (hsecond z).symm
    -- Contract the actual neighborhood to its specified infinity, then keep the first coordinate.
    obtain ⟨p, ⟨H₀⟩⟩ := id_nullhomotopic N
    let H : (ContinuousMap.id N).Homotopy (ContinuousMap.const N pinf) :=
      H₀.trans (H₀.symm.compContinuousMap (ContinuousMap.const N pinf))
    let s : C(B, N) := ⟨fun z ↦ ⟨z.val.2, (hB z.val).mp z.property⟩,
      (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
    have hir : (i.comp r).Homotopic (ContinuousMap.id B) := by
      refine ⟨{
        toFun := fun p ↦
          ⟨(p.2.val.1, (H.symm (p.1, s p.2)).val), (hB _).mpr (H.symm _).property⟩
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }⟩
      · exact ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp (H.symm.continuous.comp
            (continuous_fst.prodMk (s.continuous.comp continuous_snd))))).subtype_mk _
      · intro z
        apply Subtype.ext
        exact Prod.ext rfl (congrArg Subtype.val (H.symm.map_zero_left (s z)))
      · intro z
        apply Subtype.ext
        exact Prod.ext rfl (congrArg Subtype.val (H.symm.map_one_left (s z)))
    exact isIso_singularCohomologyPullback_of_homotopyInverse R i r
      (hri ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id A)) hir k

variable [CompactSpace X]

/-- Collapse the complete slice boundary using the original finite-product collapse. -/
def compactSupportSliceCollapse : C(X × OnePoint Y, OnePoint (X × Y)) :=
  onePointProductCollapseMap.comp
    ⟨fun z ↦ ((z.1 : OnePoint X), z.2),
      (OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd⟩

/-- The slice collapse sends precisely its full boundary to the original point at infinity. -/
theorem compactSupportSliceCollapse_mapsTo :
    Set.MapsTo (compactSupportSliceCollapse X Y)
      ((Set.range (compactSupportSliceInclusion X Y))ᶜ)
      ({∞} : Set (OnePoint (X × Y))) := by
  intro z hz
  cases heq : z.2 using OnePoint.rec with
  | infty => simp [compactSupportSliceCollapse, onePointProductCollapseMap,
      onePointProductCollapse, heq]
  | coe y => exact False.elim (hz ⟨(z.1, y), Prod.ext rfl heq.symm⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback of the original one-point comparison is the actual slice comparison. -/
theorem compactSupportCohomologyToSlice_onePoint (n : ℕ)
    (a : compactSupportCohomology R (X × Y) n) :
    relativeSingularCohomologyPullback R (compactSupportSliceCollapse X Y)
        (compactSupportSliceCollapse_mapsTo X Y) n
        (compactSupportCohomologyToOnePoint R (X × Y) n a) =
      compactSupportCohomologyToSlice R X Y n a := by
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R (X × Y) n a
  let j := compactSupportSliceInclusion X Y
  let q := compactSupportSliceCollapse X Y
  let A : Set (X × OnePoint Y) := (Set.range j)ᶜ
  let B : Set (X × OnePoint Y) := (openEmbeddingCompactImage j K : Set _)ᶜ
  let C : Set (OnePoint (X × Y)) := (((↑) : X × Y → OnePoint (X × Y)) '' (K : Set _))ᶜ
  have hA : A ⊆ B := by
    rintro z hz ⟨p, _, rfl⟩
    exact hz ⟨p, rfl⟩
  have hC : ({∞} : Set (OnePoint (X × Y))) ⊆ C := by
    rintro z rfl
    exact OnePoint.infty_notMem_image_coe
  have hq : Set.MapsTo q B C := by
    intro z hz hmem
    obtain ⟨p, hp, heq⟩ := hmem
    cases hy : z.2 using OnePoint.rec with
    | infty =>
      have hqz : q z = ∞ := by
        simp [q, compactSupportSliceCollapse, onePointProductCollapseMap,
          onePointProductCollapse, hy]
      exact OnePoint.coe_ne_infty p (heq.trans hqz)
    | coe y =>
      have hqz : q z = ((z.1, y) : OnePoint (X × Y)) := by
        simp [q, compactSupportSliceCollapse, onePointProductCollapseMap,
          onePointProductCollapse, hy]
      have hpz : p = (z.1, y) := OnePoint.coe_injective (heq.trans hqz)
      subst p
      exact hz ⟨(z.1, y), hp, Prod.ext rfl hy.symm⟩
  let PJ := openEmbeddingCohomologySupportPullback R j
    (isOpenEmbedding_compactSupportSliceInclusion X Y) K n
  let PK := onePointCohomologySupportPullback R (X × Y) K n
  let F := relativeSingularCohomologyPullback R q hq n
  let : IsIso PJ := isIso_openEmbeddingCohomologySupportPullback R j
    (isOpenEmbedding_compactSupportSliceInclusion X Y) K n
  let : IsIso PK := isIso_onePointCohomologySupportPullback R (X × Y) K n
  -- The collapse is the same finite inclusion on the given original representative.
  have hsquare : F ≫ PJ = PK := by
    dsimp only [F, PJ, PK, openEmbeddingCohomologySupportPullback,
      onePointCohomologySupportPullback]
    rw [← relativeSingularCohomologyPullback_comp]
    rfl
  have hα : F ((asIso PK).inv α) = (asIso PJ).inv α := by
    apply (ConcreteCategory.isIso_iff_bijective PJ).mp inferInstance |>.injective
    have heq := congrArg (fun g ↦ g ((asIso PK).inv α)) hsquare
    exact heq.trans ((asIso PK).inv_hom_id_apply α) |>.trans
      ((asIso PJ).inv_hom_id_apply α).symm
  have hrestrict := relativeSingularCohomologyPullback_restriction R q hA hC
    (compactSupportSliceCollapse_mapsTo X Y) hq n
  change _ = compactSupportCohomologyToCompactification R j
    (isOpenEmbedding_compactSupportSliceInclusion X Y) n _
  rw [compactSupportCohomologyToOnePoint_representative,
    compactSupportCohomologyToCompactification_representative]
  change relativeSingularCohomologyPullback R q _ n
    (relativeSingularCohomologyRestriction R {∞} C hC n ((asIso PK).inv α)) =
      relativeSingularCohomologyRestriction R A B hA n ((asIso PJ).inv α)
  have heq := congrArg (fun g ↦ g ((asIso PK).inv α)) hrestrict
  change _ = relativeSingularCohomologyRestriction R A B hA n (F ((asIso PK).inv α)) at heq
  exact heq.trans (congrArg (relativeSingularCohomologyRestriction R A B hA n) hα)

/-- The actual collapse detects point-relative classes when both colimit comparisons apply. -/
theorem relativeSingularCohomologyPullback_sliceCollapse_injective
    (h : ∀ K : Compacts Y, ∃ L : Compacts Y, K ≤ L ∧
      ContractibleSpace ((((↑) : Y → OnePoint Y) '' (L : Set Y))ᶜ : Set (OnePoint Y)))
    (n : ℕ) (hpoint : Function.Surjective (compactSupportCohomologyToOnePoint R (X × Y) n)) :
    Function.Injective (relativeSingularCohomologyPullback R (compactSupportSliceCollapse X Y)
      (compactSupportSliceCollapse_mapsTo X Y) n) := by
  intro a b hab
  obtain ⟨α, rfl⟩ := hpoint a
  obtain ⟨β, rfl⟩ := hpoint b
  rw [compactSupportCohomologyToSlice_onePoint, compactSupportCohomologyToSlice_onePoint] at hab
  exact congrArg (compactSupportCohomologyToOnePoint R (X × Y) n)
    ((compactSupportCohomologyToSlice_bijective R X Y h n).injective hab)

end AtiyahSinger
