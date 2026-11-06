/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopyPullback
public import AtiyahSinger.Topology.RelativeTriple
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Triples invertible outside a specified compact set

Public module ID: M1688.

D07/K02/P01. A control set records where invertibility may fail; it is not claimed
to be the minimal support. Equivalence by boundary homotopy uses one compact set
for the entire interval. No global bound on locally varying bundle ranks is imposed.
Sources: SG I.9.26, pp.66–67; Karoubi II.4.1–4.3 and the relative triple model.
Stable quotient and comparison with one-point compactification remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- A pair of bundles with an actual isomorphism outside a compact control set. -/
structure CompactSupportTriple (E F : X → Type*) [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℂ (E x)] [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)] where
  /-- A chosen compact set outside which the boundary isomorphism is specified. -/
  control : Set X
  /-- Compactness of the one chosen control set. -/
  isCompact_control : IsCompact control
  /-- The actual isomorphism on the complement of the control set. -/
  boundary : RelativeTriple E F controlᶜ

/-- Enlarge the compact control set, restricting the same isomorphism at infinity. -/
@[reducible]
def CompactSupportTriple.enlarge (a : CompactSupportTriple E F)
    (K : Set X) (hK : IsCompact K) (h : a.control ⊆ K) : CompactSupportTriple E F where
  control := K
  isCompact_control := hK
  boundary := a.boundary.restrictTo (Set.compl_subset_compl.mpr h)

/-- Enlargement keeps the original boundary values wherever they remain defined. -/
theorem CompactSupportTriple.enlarge_apply (a : CompactSupportTriple E F)
    (K : Set X) (hK : IsCompact K) (h : a.control ⊆ K) (x : (Kᶜ : Set X)) (v : E x) :
    (a.enlarge K hK h).boundary.linearEquiv x v =
      a.boundary.linearEquiv ⟨x, fun hx ↦ x.property (h hx)⟩ v := by
  /- Use the formula for restriction along a subset. Complement inclusion
  transports the same base point, and both comparison maps preserve its fiber vector. -/
  exact Iso.restrictTo_apply a.boundary (Set.compl_subset_compl.mpr h) x v

/-- A global isomorphism has an empty compact control set. -/
def CompactSupportTriple.ofIso (e : Iso E F) : CompactSupportTriple E F where
  control := ∅
  isCompact_control := isCompact_empty
  boundary := e.restrict (∅ : Set X)ᶜ

/-- Invert the isomorphism at infinity, leaving its domain fixed. -/
def CompactSupportTriple.inverse (a : CompactSupportTriple E F) : CompactSupportTriple F E where
  control := a.control
  isCompact_control := a.isCompact_control
  boundary := a.boundary.symm

/-- Compose at infinity after passing to a common compact control set. -/
def CompactSupportTriple.compose (a : CompactSupportTriple E F)
    (b : CompactSupportTriple F G) : CompactSupportTriple E G where
  control := a.control ∪ b.control
  isCompact_control := a.isCompact_control.union b.isCompact_control
  boundary := ((a.enlarge _ (a.isCompact_control.union b.isCompact_control)
      Set.subset_union_left).boundary).trans
      (b.enlarge _ (a.isCompact_control.union b.isCompact_control)
        Set.subset_union_right).boundary

variable {H : X → Type*} [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]

attribute [local instance] sumTopology

/-- Direct sum at infinity uses the union of the two compact control sets. -/
def CompactSupportTriple.sum (a : CompactSupportTriple E F)
    (b : CompactSupportTriple G H) : CompactSupportTriple (E ×ᵇ G) (F ×ᵇ H) where
  control := a.control ∪ b.control
  isCompact_control := a.isCompact_control.union b.isCompact_control
  boundary := RelativeTriple.sum
      (a.enlarge _ (a.isCompact_control.union b.isCompact_control)
        Set.subset_union_left).boundary
      (b.enlarge _ (a.isCompact_control.union b.isCompact_control)
        Set.subset_union_right).boundary

/-- Homotopy at infinity requires a single compact control set for all times. -/
def CompactSupportTriple.Homotopic (a b : CompactSupportTriple E F) : Prop :=
  ∃ K : Set X, ∃ hK : IsCompact K, ∃ ha : a.control ⊆ K, ∃ hb : b.control ⊆ K,
    Nonempty (IsoHomotopy (a.enlarge K hK ha).boundary (b.enlarge K hK hb).boundary)

/-- Each triple is homotopic to itself with its original compact control. -/
theorem CompactSupportTriple.homotopic_refl (a : CompactSupportTriple E F) : a.Homotopic a := by
  /- Use its original compact control set and the constant cylinder isomorphism
  on the complement. Enlargement to the same set keeps the boundary map fixed. -/
  exact ⟨a.control, a.isCompact_control, Set.Subset.refl _, Set.Subset.refl _,
    IsoHomotopy.nonempty_refl _⟩

/-- Reversing a homotopy uses the same uniform compact control. -/
theorem CompactSupportTriple.Homotopic.symm {a b : CompactSupportTriple E F}
    (h : a.Homotopic b) : b.Homotopic a := by
  /- Retain the compact set and exchange the two inclusion witnesses. Reverse
  the homotopy on its complement; no additional noncompact region enters the support. -/
  obtain ⟨K, hK, ha, hb, ⟨H⟩⟩ := h
  exact ⟨K, hK, hb, ha, H.nonempty_symm⟩

/-- Concatenating homotopies uses the union of their compact controls. -/
theorem CompactSupportTriple.Homotopic.trans {a b c : CompactSupportTriple E F}
    (h : a.Homotopic b) (k : b.Homotopic c) : a.Homotopic c := by
  /- Take the union of the two compact sets. Restrict both homotopies to its
  complement, where their shared endpoint is the same restriction of b. Concatenate
  there to get a homotopy with one compact control set throughout the interval. -/
  -- Base change and the original restriction comparisons preserve every boundary vector.
  have hrestrict {S T : Set X} (hTS : T ⊆ S)
      {e₀ e₁ : RelativeTriple E F S} (H : IsoHomotopy e₀ e₁) :
      Nonempty (IsoHomotopy (e₀.restrictTo hTS) (e₁.restrictTo hTS)) := by
    obtain ⟨H', _⟩ := H.exists_pullback ⟨Set.inclusion hTS, continuous_inclusion hTS⟩
    obtain ⟨U⟩ := IsoHomotopy.nonempty_refl (restrictSubsetIso (E := E) S T hTS).symm
    obtain ⟨V⟩ := IsoHomotopy.nonempty_refl (restrictSubsetIso (E := F) S T hTS)
    obtain ⟨HV⟩ := H'.nonempty_comp V
    exact U.nonempty_comp HV
  have heq (d : CompactSupportTriple E F) (S T : Set X)
      (hS : IsCompact S) (hT : IsCompact T) (hd : d.control ⊆ S) (hST : S ⊆ T) :
      ((d.enlarge S hS hd).boundary.restrictTo (Set.compl_subset_compl.mpr hST)) =
        (d.enlarge T hT (hd.trans hST)).boundary := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    exact (Iso.restrictTo_apply (E := E) (F := F) (d.enlarge S hS hd).boundary
      (Set.compl_subset_compl.mpr hST) x v).trans
      ((d.enlarge_apply S hS hd
        (Set.inclusion (Set.compl_subset_compl.mpr hST) x) v).trans
        (d.enlarge_apply T hT (hd.trans hST) x v).symm)
  -- A single union controls both paths; their common endpoint is the same map of b.
  obtain ⟨K, hK, ha, hb, ⟨H⟩⟩ := h
  obtain ⟨L, hL, hb', hc, ⟨J⟩⟩ := k
  have hU : IsCompact (K ∪ L) := hK.union hL
  obtain ⟨H'⟩ := hrestrict (Set.compl_subset_compl.mpr Set.subset_union_left) H
  obtain ⟨J'⟩ := hrestrict (Set.compl_subset_compl.mpr Set.subset_union_right) J
  rw [heq a K (K ∪ L) hK hU ha Set.subset_union_left,
    heq b K (K ∪ L) hK hU hb Set.subset_union_left] at H'
  rw [heq b L (K ∪ L) hL hU hb' Set.subset_union_right,
    heq c L (K ∪ L) hL hU hc Set.subset_union_right] at J'
  exact ⟨K ∪ L, hU, ha.trans Set.subset_union_left,
    hc.trans Set.subset_union_right, H'.nonempty_trans J'⟩

/-- Changing only the chosen compact control does not change the homotopy class. -/
theorem CompactSupportTriple.homotopic_enlarge (a : CompactSupportTriple E F)
    (K : Set X) (hK : IsCompact K) (h : a.control ⊆ K) : a.Homotopic (a.enlarge K hK h) := by
  /- Use K as the common control. The two endpoint boundary maps are the same
  further restriction of a, so a constant homotopy supplies the required witness. -/
  have hboundary : ((a.enlarge K hK h).enlarge K hK (Set.Subset.refl _)).boundary =
      (a.enlarge K hK h).boundary := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    exact (a.enlarge K hK h).enlarge_apply K hK (Set.Subset.refl _) x v
  refine ⟨K, hK, h, Set.Subset.refl _, ?_⟩
  rw [hboundary]
  exact IsoHomotopy.nonempty_refl _

variable {Y : Type*} [TopologicalSpace Y]

/-- Proper pullback has the compact inverse image as its control set. -/
def CompactSupportTriple.pullback (a : CompactSupportTriple E F)
    (f : C(Y, X)) (hf : IsProperMap f) :
    CompactSupportTriple ((f : Y → X) *ᵖ E) ((f : Y → X) *ᵖ F) where
  control := f ⁻¹' a.control
  isCompact_control := hf.isCompact_preimage a.isCompact_control
  boundary := a.boundary.pullback f

/-- Proper pullback preserves uniformly controlled boundary homotopies. -/
theorem CompactSupportTriple.Homotopic.pullback {a b : CompactSupportTriple E F}
    (h : a.Homotopic b) (f : C(Y, X)) (hf : IsProperMap f) :
    (a.pullback f hf).Homotopic (b.pullback f hf) := by
  /- Pull the common compact control back by f; properness makes it compact.
  Pull the cylinder isomorphism back by the product of identity time and f.
  Its endpoints are the pulled-back boundary maps on the same complement. -/
  obtain ⟨K, hK, ha, hb, ⟨H⟩⟩ := h
  have hL : IsCompact (f ⁻¹' K) := hf.isCompact_preimage hK
  let i : C((Kᶜ : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  let j : C(((f ⁻¹' K)ᶜ : Set Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(((f ⁻¹' K)ᶜ : Set Y), (Kᶜ : Set X)) :=
    ⟨fun y ↦ ⟨f y, y.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  -- Compare the two routes to the same original fiber; no vector is changed.
  let U : Iso (Restrict ((f : Y → X) *ᵖ E) (f ⁻¹' K)ᶜ)
      ((q : ((f ⁻¹' K)ᶜ : Set Y) → (Kᶜ : Set X)) *ᵖ (Restrict E Kᶜ)) :=
    (pullbackCompIso (E := E) f j).trans (pullbackCompIso (E := E) i q).symm
  let V : Iso (Restrict ((f : Y → X) *ᵖ F) (f ⁻¹' K)ᶜ)
      ((q : ((f ⁻¹' K)ᶜ : Set Y) → (Kᶜ : Set X)) *ᵖ (Restrict F Kᶜ)) :=
    (pullbackCompIso (E := F) f j).trans (pullbackCompIso (E := F) i q).symm
  have hu (y : ((f ⁻¹' K)ᶜ : Set Y)) (v : E (f y)) : U.linearEquiv y v = v := by
    change ((pullbackCompIso (E := E) i q).linearEquiv y).symm
      ((pullbackCompIso (E := E) f j).linearEquiv y v) = v
    apply ((pullbackCompIso (E := E) i q).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hv (y : ((f ⁻¹' K)ᶜ : Set Y)) (v : F (f y)) : V.symm.linearEquiv y v = v := by
    change ((pullbackCompIso (E := F) f j).linearEquiv y).symm
      ((pullbackCompIso (E := F) i q).linearEquiv y v) = v
    apply ((pullbackCompIso (E := F) f j).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have heq (d : CompactSupportTriple E F) (hd : d.control ⊆ K) :
      U.trans ((Iso.pullback q (d.enlarge K hK hd).boundary).trans V.symm) =
        ((d.pullback f hf).enlarge (f ⁻¹' K) hL (Set.preimage_mono hd)).boundary := by
    apply Iso.ext
    intro y
    apply LinearEquiv.ext
    intro v
    change V.symm.linearEquiv y
      ((d.enlarge K hK hd).boundary.linearEquiv (q y) (U.linearEquiv y v)) = _
    have hvalue := (hv y ((d.enlarge K hK hd).boundary.linearEquiv (q y)
      (U.linearEquiv y v))).trans
      (congrArg ((d.enlarge K hK hd).boundary.linearEquiv (q y)) (hu y v))
    exact hvalue.trans ((d.enlarge_apply K hK hd (q y) v).trans
      (((d.pullback f hf).enlarge_apply (f ⁻¹' K) hL
        (Set.preimage_mono hd) y v).trans
          (RelativeTriple.pullback_apply d.boundary f
            ⟨y.val, fun hy ↦ y.property (hd hy)⟩ v)).symm)
  -- The entire cylinder pulls back, then the fixed comparisons identify its endpoints.
  obtain ⟨H', _⟩ := H.exists_pullback q
  obtain ⟨HU⟩ := IsoHomotopy.nonempty_refl U
  obtain ⟨HV⟩ := IsoHomotopy.nonempty_refl V.symm
  obtain ⟨H'V⟩ := H'.nonempty_comp HV
  obtain ⟨J⟩ := HU.nonempty_comp H'V
  rw [heq a ha, heq b hb] at J
  exact ⟨f ⁻¹' K, hL, Set.preimage_mono ha, Set.preimage_mono hb, ⟨J⟩⟩

/-- For a compact base every infinity triple may use the whole space as control. -/
theorem CompactSupportTriple.homotopic_enlarge_univ [CompactSpace X]
    (a : CompactSupportTriple E F) :
    a.Homotopic (a.enlarge Set.univ isCompact_univ (Set.subset_univ _)) := by
  /- Apply the enlargement statement with the compact set X. The complement
  is empty, so this records why boundary information at infinity disappears on a compact base. -/
  exact a.homotopic_enlarge Set.univ isCompact_univ (Set.subset_univ _)

end AtiyahSinger.ComplexBundle
