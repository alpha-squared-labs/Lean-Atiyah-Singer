/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Compact Hausdorff spaces under closed attachment

Public module ID: M1639.

The categorical pushout of two compact Hausdorff spaces is compact Hausdorff
when one attaching map is a closed embedding. The attaching map on the other
side is an arbitrary continuous map and need not be injective.

We first prove the closed-relation criterion for quotients of compact spaces.
For attachment, mathlib's explicit relation for a pushout along an injection
identifies the entire equivalence relation, whose closedness is then proved.
The explicit quotient is compared with the original `TopCat` pushout by its
universal property. No separation property of the quotient is an input.

This standard adjunction-space theorem supplies the topological attachment
step needed to build compact Hausdorff realizations of finite simplicial data.
FiniteSimplicialRealizationHausdorff applies this attachment result to those realizations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology

universe u

namespace Topology.IsQuotientMap

/-- A quotient of a compact space is Hausdorff when its full fiber relation is closed. -/
theorem t2Space_of_isClosed_relation {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    {q : X → Y} (hq : IsQuotientMap q)
    (hR : IsClosed {p : X × X | q p.1 = q p.2}) : T2Space Y := by
  -- Closedness of the relation makes saturation a closed operation: project
  -- a closed subset of a product whose other factor is compact.
  have hclosed : IsClosedMap q := by
    intro s hs
    apply hq.isCoinducing.isClosed_preimage.mp
    have hsaturation : q ⁻¹' (q '' s) =
        Prod.snd '' ((s ×ˢ univ) ∩ {p : X × X | q p.1 = q p.2}) := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨(x, y), ⟨⟨hx, mem_univ y⟩, hxy⟩, rfl⟩
      · rintro ⟨⟨x, z⟩, ⟨⟨hx, _⟩, hxz⟩, rfl⟩
        exact ⟨x, hx, hxz⟩
    rw [hsaturation]
    exact isClosedMap_snd_of_compactSpace _ ((hs.prod isClosed_univ).inter hR)
  -- Every fiber is a closed subset of the compact source. Thus the quotient
  -- is proper, and its square is closed as well.
  have hproper : IsProperMap q := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨hq.continuous, hclosed, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hq.surjective y
    exact (hR.preimage (continuous_id.prodMk continuous_const)).isCompact
  -- The image of the fiber relation under the square quotient is precisely
  -- the diagonal of the target, so the Hausdorff diagonal criterion applies.
  have hdiagonal : Prod.map q q '' {p : X × X | q p.1 = q p.2} = diagonal Y := by
    ext ⟨y, z⟩
    constructor
    · rintro ⟨⟨x, w⟩, hxw, hpair⟩
      change y = z
      exact (congrArg Prod.fst hpair).symm.trans
        (hxw.trans (congrArg Prod.snd hpair))
    · intro hyz
      change y = z at hyz
      subst z
      obtain ⟨x, rfl⟩ := hq.surjective y
      exact ⟨(x, x), rfl, rfl⟩
  apply t2_iff_isClosed_diagonal.mpr
  rw [← hdiagonal]
  exact (hproper.prodMap hproper).isClosedMap _ hR

end Topology.IsQuotientMap

namespace TopCat

variable {S X Y : TopCat.{u}}

/-- A pushout of two compact spaces is compact, without separation or embedding assumptions. -/
theorem compactSpace_pushout (f : S ⟶ X) (g : S ⟶ Y)
    [CompactSpace X] [CompactSpace Y] : CompactSpace (pushout f g : TopCat.{u}) := by
  let p : X ⊕ Y → (pushout f g : TopCat.{u}) :=
    Sum.elim (pushout.inl f g) (pushout.inr f g)
  have hp : Continuous p := by
    exact (pushout.inl f g).hom.continuous.sumElim (pushout.inr f g).hom.continuous
  have hsurj : Function.Surjective p := by
    intro z
    obtain ⟨x, hx⟩ | ⟨y, hy⟩ := Types.eq_or_eq_of_isPushout
      ((IsPushout.of_hasPushout f g).map (forget TopCat)) z
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr y, hy⟩
  exact hsurj.compactSpace hp

/-- Attaching a compact Hausdorff space along a closed subspace to a compact Hausdorff space
preserves Hausdorffness, for the original categorical pushout in `TopCat`. -/
theorem t2Space_pushout_of_isClosedEmbedding (f : S ⟶ X) (g : S ⟶ Y)
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (hf : IsClosedEmbedding f) : T2Space (pushout f g : TopCat.{u}) := by
  let : CompactSpace S := hf.compactSpace
  let f₀ : (S : Type u) ⟶ (X : Type u) := (forget TopCat).map f
  let g₀ : (S : Type u) ⟶ (Y : Type u) := (forget TopCat).map g
  let : Mono f₀ := (CategoryTheory.mono_iff_injective f₀).mpr hf.injective
  let Q := Quot (Types.Pushout.Rel f₀ g₀)
  -- Along an injection the equivalence relation has exactly four kinds of
  -- pairs: equality, two attached boundary points, and the two cross pairs.
  -- Their domains are compact, so their images in the Hausdorff sum are closed.
  let boundaryPairs : Set (S × S) := {p | g p.1 = g p.2}
  let boundaryImage : Set ((X ⊕ Y) × (X ⊕ Y)) :=
    (fun p : S × S ↦ (Sum.inl (f p.1), Sum.inl (f p.2))) '' boundaryPairs
  let crossImage : Set ((X ⊕ Y) × (X ⊕ Y)) :=
    range (fun s : S ↦ (Sum.inl (f s), Sum.inr (g s)))
  let reverseImage : Set ((X ⊕ Y) × (X ⊕ Y)) :=
    range (fun s : S ↦ (Sum.inr (g s), Sum.inl (f s)))
  have hboundary : IsClosed boundaryImage := by
    have h : IsClosed boundaryPairs :=
      isClosed_eq (g.hom.continuous.comp continuous_fst)
        (g.hom.continuous.comp continuous_snd)
    exact (h.isCompact.image (by fun_prop)).isClosed
  have hcross : IsClosed crossImage := (isCompact_range (by fun_prop)).isClosed
  have hreverse : IsClosed reverseImage := (isCompact_range (by fun_prop)).isClosed
  have hrelation : {p : (X ⊕ Y) × (X ⊕ Y) | Types.Pushout.Rel' f₀ g₀ p.1 p.2} =
      diagonal (X ⊕ Y) ∪ boundaryImage ∪ crossImage ∪ reverseImage := by
    ext ⟨a, b⟩
    constructor
    · intro h
      cases h with
      | refl a => exact Or.inl (Or.inl (Or.inl rfl))
      | inl_inl s t hst => exact Or.inl (Or.inl (Or.inr ⟨(s, t), hst, rfl⟩))
      | inl_inr s => exact Or.inl (Or.inr ⟨s, rfl⟩)
      | inr_inl s => exact Or.inr ⟨s, rfl⟩
    · rintro (((h | ⟨⟨s, t⟩, hst, hpair⟩) | ⟨s, hpair⟩) | ⟨s, hpair⟩)
      · change a = b at h
        subst b
        exact Types.Pushout.Rel'.refl _
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        exact Types.Pushout.Rel'.inl_inl _ _ hst
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        exact Types.Pushout.Rel'.inl_inr _
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        exact Types.Pushout.Rel'.inr_inl _
  have hQ : T2Space Q := by
    apply isQuotientMap_quot_mk.t2Space_of_isClosed_relation
    have heq : {p : (X ⊕ Y) × (X ⊕ Y) |
        (Quot.mk _ p.1 : Q) = Quot.mk _ p.2} =
        {p | Types.Pushout.Rel' f₀ g₀ p.1 p.2} := by
      ext p
      exact Types.Pushout.quot_mk_eq_iff f₀ g₀ p.1 p.2
    rw [heq, hrelation]
    exact ((isClosed_diagonal.union hboundary).union hcross).union hreverse
  -- The explicit quotient satisfies the continuous pushout universal
  -- property, so its topology agrees with the existing categorical pushout.
  let left : X ⟶ TopCat.of Q :=
    TopCat.ofHom ⟨fun x ↦ Quot.mk _ (Sum.inl x), by fun_prop⟩
  let right : Y ⟶ TopCat.of Q :=
    TopCat.ofHom ⟨fun y ↦ Quot.mk _ (Sum.inr y), by fun_prop⟩
  have condition : f ≫ left = g ≫ right := by
    ext s
    exact Quot.sound (Types.Pushout.Rel.inl_inr s)
  let c : PushoutCocone f g := PushoutCocone.mk left right condition
  have hc : IsColimit c := by
    refine PushoutCocone.IsColimit.mk condition (fun s ↦ ?_) ?_ ?_ ?_
    · let l : X ⊕ Y → s.pt := Sum.elim s.inl s.inr
      have hl : ∀ a b, Types.Pushout.Rel f₀ g₀ a b → l a = l b := by
        rintro _ _ ⟨t⟩
        exact congrArg (fun k : S ⟶ s.pt ↦ k t) s.condition
      exact TopCat.ofHom ⟨Quot.lift l hl,
        continuous_quot_lift hl (s.inl.hom.continuous.sumElim s.inr.hom.continuous)⟩
    · intro s
      rfl
    · intro s
      rfl
    · intro s m hleft hright
      ext q
      obtain ⟨x | y⟩ := q
      · exact congrArg (fun k : X ⟶ s.pt ↦ k x) hleft
      · exact congrArg (fun k : Y ⟶ s.pt ↦ k y) hright
  let : T2Space c.pt := hQ
  exact (homeoOfIso (hc.coconePointUniqueUpToIso (pushoutIsPushout f g))).t2Space

end TopCat
