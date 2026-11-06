/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.Regular

/-!
# Injective neighborhoods of noncompact embedded subspaces

Public module ID: M1313.

A continuous map that is locally injective along a subspace, and restricts to a closed embedding
on that subspace, is injective on an open neighborhood of the whole subspace when the target is
regular and paracompact. This is the noncompact shrinking step for tubular coordinates.

The construction uses a locally finite target cover. For each member of the cover, remove points
whose image lies in its closure but which lie outside the corresponding local injectivity domain.
These closed bad sets form a locally finite family. Their union misses the prescribed subspace,
and deleting it enforces that any two points with the same image lie in a common injectivity domain.
No compactness of the subspace and no constant choice of radius are assumed.

This is a supplementary topological argument for the standard tubular neighborhood construction.
It does not by itself construct a smooth local addition or a normal-bundle parametrization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology

/-- A continuous map that embeds a subspace as a closed set and is locally injective along it
is injective on an open neighborhood of that subspace in a regular paracompact target. -/
theorem exists_isOpen_superset_injOn_of_isClosedEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [RegularSpace Y] [ParacompactSpace Y] {f : X → Y} {s : Set X}
    (hf : Continuous f) (he : IsClosedEmbedding (fun x : s ↦ f x))
    (hloc : ∀ x ∈ s, ∃ u : Set X, IsOpen u ∧ x ∈ u ∧ InjOn f u) :
    ∃ u : Set X, IsOpen u ∧ s ⊆ u ∧ InjOn f u := by
  classical
  -- The embedding makes each local injectivity domain visible as a relative target neighborhood.
  -- Shrink that target neighborhood once, before making the cover locally finite.
  have hlocal : ∀ a : s, ∃ (u : Set X) (v : Set Y),
      IsOpen u ∧ (a : X) ∈ u ∧ InjOn f u ∧ IsOpen v ∧ f a ∈ v ∧
        ∀ b : s, f b ∈ closure v → (b : X) ∈ u := by
    intro a
    obtain ⟨u, hu, hau, hfu⟩ := hloc a a.property
    obtain ⟨w, hw, hwu⟩ := he.isInducing.isOpen_iff.mp (hu.preimage continuous_subtype_val)
    have haw : f a ∈ w := by
      have ha : a ∈ (Subtype.val : s → X) ⁻¹' u := hau
      rwa [← hwu] at ha
    obtain ⟨v, ⟨hav, hv⟩, hvw⟩ :=
      (hasBasis_opens_closure (f a)).mem_iff.mp (hw.mem_nhds haw)
    refine ⟨u, v, hu, hau, hfu, hv, hav, ?_⟩
    intro b hb
    have hb' : b ∈ (fun x : s ↦ f x) ⁻¹' w := hvw hb
    rw [hwu] at hb'
    exact hb'
  choose u v hu hau hfu hv hav huv using hlocal
  have hcover : range (fun x : s ↦ f x) ⊆ ⋃ a, v a := by
    rintro y ⟨a, rfl⟩
    exact mem_iUnion_of_mem a (hav a)
  obtain ⟨w, hw, hsw, hwfin, hwv⟩ :=
    precise_refinement_set he.isClosed_range v hv hcover
  -- Delete the locally finite closed family of points that would use a wrong inverse branch.
  let bad : s → Set X := fun a ↦ f ⁻¹' closure (w a) \ u a
  have hbadfin : LocallyFinite bad :=
    (hwfin.closure.preimage_continuous hf).subset (fun a ↦ sdiff_subset)
  have hbadclosed : ∀ a, IsClosed (bad a) := fun a ↦
    (isClosed_closure.preimage hf).sdiff (hu a)
  let U : Set X := f ⁻¹' (⋃ a, w a) ∩ (⋃ a, bad a)ᶜ
  have hU : IsOpen U :=
    ((isOpen_iUnion hw).preimage hf).inter (hbadfin.isClosed_iUnion hbadclosed).isOpen_compl
  have hsU : s ⊆ U := by
    intro x hx
    refine ⟨hsw ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    intro hxbad
    obtain ⟨a, ha⟩ := mem_iUnion.mp hxbad
    exact ha.2 (huv a ⟨x, hx⟩ ((closure_mono (hwv a)) ha.1))
  -- Equal images force both points into any selected local injectivity domain over that image.
  refine ⟨U, hU, hsU, ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, hxa⟩ := mem_iUnion.mp hx.1
  have hxu : x ∈ u a := by
    by_contra hxnu
    exact hx.2 (mem_iUnion_of_mem a ⟨subset_closure hxa, hxnu⟩)
  have hyu : y ∈ u a := by
    by_contra hynu
    have hya : f y ∈ closure (w a) := hxy ▸ subset_closure hxa
    exact hy.2 (mem_iUnion_of_mem a ⟨hya, hynu⟩)
  exact hfu a hxu hyu hxy

end AtiyahSinger
