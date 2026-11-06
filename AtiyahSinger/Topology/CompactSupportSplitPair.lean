/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportKMinusOneExactness
public import AtiyahSinger.Topology.OpenEmbeddingKZero

/-!
# Open extension for a proper retract pair

Public module ID: M1687.

A proper retraction splits restriction in the original supported automorphism
group. The existing exact sequence then makes the boundary vanish, and extension
from the open complement is injective. This is the split-pair case used to pass
compact-base Bott periodicity to the one-point compactification of an LCH space.
No injectivity assertion is made for an arbitrary open embedding.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle Topology

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- A proper retraction of the closed subspace makes open extension injective. -/
theorem compactSupportKZeroOpenExtension_injective_of_retraction
    (A : Set X) (hA : IsClosed A) (r : C(X, A)) (hproper : IsProperMap r)
    (hr : ∀ a : A, r a.val = a) :
    letI := hA.isOpen_compl.locallyCompactSpace
    Function.Injective (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl) := by
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsProperMap i := hA.isClosedEmbedding_subtypeVal.isProperMap
  -- The same retraction provides a right inverse to restriction in supported K-minus-one.
  have hsurj : Function.Surjective (compactSupportBundleKMinusOneClosedRestriction A hA) := by
    intro a
    refine ⟨compactSupportBundleKMinusOnePullback r hproper a, ?_⟩
    change compactSupportBundleKMinusOnePullback i hi
      (compactSupportBundleKMinusOnePullback r hproper a) = a
    rw [← AddMonoidHom.comp_apply, ← compactSupportBundleKMinusOnePullback_comp]
    have hid : r.comp i = ContinuousMap.id A := by
      apply ContinuousMap.ext
      exact hr
    simp only [hid, compactSupportBundleKMinusOnePullback_id, AddMonoidHom.id_apply]
  -- Exactness forces the specified boundary to vanish on every supported class.
  have hzero (a : CompactSupportBundleKMinusOne A) :
      compactSupportBundleKMinusOneBoundary A hA a = 0 := by
    have ha : a ∈ (compactSupportBundleKMinusOneClosedRestriction A hA).range :=
      hsurj a
    rw [range_compactSupportBundleKMinusOneClosedRestriction A hA] at ha
    exact ha
  -- The next exactness term identifies the entire kernel of the actual open extension.
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hmem : a ∈ (compactSupportBundleKMinusOneBoundary A hA).range := by
    rw [range_compactSupportBundleKMinusOneBoundary A hA]
    exact ha
  obtain ⟨b, hb⟩ := hmem
  exact hb.symm.trans (hzero b)

/-- Extension along an open embedding is injective when its closed complement properly retracts. -/
theorem compactSupportKZeroOpenPushforward_injective_of_retraction
    {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (f : Y → X) (hf : IsOpenEmbedding f)
    (r : C(X, ↥((Set.range f)ᶜ))) (hproper : IsProperMap r)
    (hr : ∀ a : ↥((Set.range f)ᶜ), r a.val = a) :
    Function.Injective (compactSupportKZeroOpenPushforward f hf) := by
  let := hf.isOpen_range.locallyCompactSpace
  have hclosed : IsClosed (Set.range f)ᶜ := hf.isOpen_range.isClosed_compl
  have hinj := compactSupportKZeroOpenExtension_injective_of_retraction
    (Set.range f)ᶜ hclosed r hproper hr
  have hU : Function.Injective
      (compactSupportKZeroOpenExtension (Set.range f) hf.isOpen_range) := by
    have transport (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (h : U = V) :
        (letI := hU.locallyCompactSpace;
          Function.Injective (compactSupportKZeroOpenExtension U hU)) →
        (letI := hV.locallyCompactSpace;
          Function.Injective (compactSupportKZeroOpenExtension V hV)) := by
      subst V
      exact fun h ↦ h
    exact transport _ _ hclosed.isOpen_compl hf.isOpen_range (compl_compl _) hinj
  exact hU.comp (compactSupportKZeroHomeomorph_bijective hf.isEmbedding.toHomeomorph).injective

/-- The original open pushforward fills the kernel of restriction to its closed complement. -/
theorem mem_range_compactSupportKZeroOpenPushforward_iff
    {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (f : Y → X) (hf : IsOpenEmbedding f) (a : CompactSupportKZero X) :
    let hA : IsClosed (Set.range f)ᶜ := hf.isOpen_range.isClosed_compl
    letI := hA.locallyCompactSpace
    a ∈ (compactSupportKZeroOpenPushforward f hf).range ↔
      compactSupportKZeroPullback
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥((Set.range f)ᶜ), X))
        hA.isClosedEmbedding_subtypeVal.isProperMap a = 0 := by
  let := hf.isOpen_range.locallyCompactSpace
  have hA : IsClosed (Set.range f)ᶜ := hf.isOpen_range.isClosed_compl
  let := hA.locallyCompactSpace
  have hexact := range_compactSupportKZeroOpenExtension (Set.range f)ᶜ hA
  have hU : (compactSupportKZeroOpenExtension (Set.range f) hf.isOpen_range).range =
      (compactSupportKZeroPullback
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥((Set.range f)ᶜ), X))
        hA.isClosedEmbedding_subtypeVal.isProperMap).ker := by
    have transport (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (h : U = V) :
        (letI := hU.locallyCompactSpace;
          (compactSupportKZeroOpenExtension U hU).range) =
        (letI := hV.locallyCompactSpace;
          (compactSupportKZeroOpenExtension V hV).range) := by
      subst V
      rfl
    exact (transport _ _ hf.isOpen_range hA.isOpen_compl (compl_compl _).symm).trans hexact
  -- The original image homeomorphism is surjective and changes no ambient extension map.
  change (∃ b, compactSupportKZeroOpenPushforward f hf b = a) ↔ _
  rw [← AddMonoidHom.mem_ker, ← hU]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨compactSupportKZeroHomeomorph hf.isEmbedding.toHomeomorph b, rfl⟩
  · rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ :=
      (compactSupportKZeroHomeomorph_bijective hf.isEmbedding.toHomeomorph).surjective b
    exact ⟨c, hb⟩

end AtiyahSinger
