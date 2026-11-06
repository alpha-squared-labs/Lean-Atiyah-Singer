/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTriple
public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import AtiyahSinger.Topology.SupportBundleTriple

/-!
# Restrict support triples to compact neighborhoods

Public module ID: M2201.

D07/K02. The boundary of a compact window L is L minus its ambient interior.
Restriction retains the original boundary isomorphism on this closed subspace.
The complement identifies with the actual open interior by the identity on points.
This explicit localization implements SG I.9.26 using the compact-pair model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X]

attribute [local instance] sumTopology isFiniteRank_sum


/-- Choose a compact neighborhood using the locally compact existence theorem. -/
def supportNeighborhood [LocallyCompactSpace X] (K : Set X) (hK : IsCompact K) : Set X :=
  (exists_compact_superset hK).choose

/-- The chosen neighborhood is compact. -/
theorem isCompact_supportNeighborhood [LocallyCompactSpace X] (K : Set X) (hK : IsCompact K) :
    IsCompact (supportNeighborhood K hK) := by
  /- Take the compactness component of the same mathlib existence witness used to choose the
  neighborhood. -/
  exact (exists_compact_superset hK).choose_spec.1

/-- The original compact control lies in the interior of its chosen neighborhood. -/
theorem subset_interior_supportNeighborhood [LocallyCompactSpace X]
    (K : Set X) (hK : IsCompact K) : K ⊆ interior (supportNeighborhood K hK) := by
  /- Take the interior-inclusion component of the same existence witness. Mere inclusion in the
  closed window would not suffice for the boundary map. -/
  exact (exists_compact_superset hK).choose_spec.2

/-- The window boundary consists of its points outside the ambient interior. -/
def supportWindowBoundary (L : Set X) : Set L :=
  {x | (x : X) ∉ interior L}

/-- The window boundary is closed in the window. -/
theorem isClosed_supportWindowBoundary (L : Set X) : IsClosed (supportWindowBoundary L) := by
  /- It is the inverse image of the closed complement of the ambient interior under the
  continuous subtype inclusion. -/
  exact isOpen_interior.isClosed_compl.preimage continuous_subtype_val

/-- A window boundary lies outside every control contained in its interior. -/
theorem supportWindowBoundary_subset (K L : Set X) (h : K ⊆ interior L) :
    supportWindowBoundary L ⊆ (Subtype.val : L → X) ⁻¹' Kᶜ := by
  /- A boundary point cannot belong to K, because that would put it in the ambient interior by
  h, contradicting its defining boundary property. -/
  intro x hx hxK
  exact hx (h hxK)

/-- Identify the open part of a window with the same ambient interior points. -/
def supportWindowInteriorHomeomorph (L : Set X) :
    ((supportWindowBoundary L)ᶜ : Set L) ≃ₜ (interior L : Set X) where
  toFun x := ⟨x.val.val, not_not.mp x.property⟩
  invFun x := ⟨⟨x.val, interior_subset x.property⟩, fun hx ↦ hx x.property⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The window homeomorphism preserves every underlying point. -/
theorem supportWindowInteriorHomeomorph_apply (L : Set X)
    (x : ((supportWindowBoundary L)ᶜ : Set L)) :
    (supportWindowInteriorHomeomorph L x : X) = x.val.val := by
  /- The forward function discards only the two old subtype proofs and supplies the ambient
  interior proof; its point is unchanged. -/
  rfl

/-- The inverse window homeomorphism also preserves the underlying point. -/
theorem supportWindowInteriorHomeomorph_symm_apply (L : Set X) (x : interior L) :
    ((supportWindowInteriorHomeomorph L).symm x).val.val = x.val := by
  /- The inverse inserts the window membership and boundary-complement proofs without changing
  the original point. -/
  rfl

/-- Restrict the actual exterior isomorphism to the window boundary. -/
def SupportBundleTriple.windowBoundary (a : SupportBundleTriple X) (L : Set X)
    (h : a.datum.control ⊆ interior L) :
    RelativeTriple (a.source.restrict L).Fiber (a.target.restrict L).Fiber
      (supportWindowBoundary L) :=
  (a.datum.boundary.pullback ⟨Subtype.val, continuous_subtype_val⟩).restrict
    (supportWindowBoundary_subset a.datum.control L h)

/-- The window boundary map has exactly the original fiber action. -/
theorem SupportBundleTriple.windowBoundary_apply (a : SupportBundleTriple X) (L : Set X)
    (h : a.datum.control ⊆ interior L) (x : supportWindowBoundary L)
    (v : a.source.Fiber x.val.val) :
    (a.windowBoundary L h).linearEquiv x v =
      a.datum.boundary.linearEquiv
        ⟨x.val.val, supportWindowBoundary_subset a.datum.control L h x.property⟩ v := by
  /- Both the inverse-image pullback and the subsequent subset restriction are defined using
  the original fiber map. Their coordinate formulas give the same vector under the original
  boundary isomorphism. -/
  let f : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  exact (Iso.restrictTo_apply (a.datum.boundary.pullback f)
    (supportWindowBoundary_subset a.datum.control L h) x v).trans
    (RelativeTriple.pullback_apply a.datum.boundary f
      ⟨x.val, supportWindowBoundary_subset a.datum.control L h x.property⟩ v)

/-- The compact-pair triple keeps both restricted bundles and the actual boundary map. -/
def SupportBundleTriple.windowTriple (a : SupportBundleTriple X) (L : Set X)
    (h : a.datum.control ⊆ interior L) : BundleTriple (supportWindowBoundary L) :=
  BundleTriple.ofBoundary (a.source.restrict L) (a.target.restrict L) (a.windowBoundary L h)

/-- Enlarging control changes no window boundary data on a common window. -/
theorem SupportBundleTriple.windowTriple_enlarge (a : SupportBundleTriple X)
    (K : Set X) (hK : IsCompact K) (ha : a.datum.control ⊆ K)
    (L : Set X) (h : K ⊆ interior L) :
    ((a.enlarge K hK ha).windowTriple L h).IsIsomorphic
      (a.windowTriple L (ha.trans h)) := by
  /- Both window triples have the same source and target restrictions. On the boundary they
  evaluate the same original exterior map; use identity bundle comparisons. -/
  refine ⟨Iso.refl _, Iso.refl _, ?_⟩
  intro x v

  exact ((a.enlarge K hK ha).windowBoundary_apply L h x v).trans
    ((a.datum.enlarge_apply K hK ha
      ⟨x.val.val, supportWindowBoundary_subset K L h x.property⟩ v).trans
      (a.windowBoundary_apply L (ha.trans h) x v).symm)

/-- Restriction to a common window commutes with direct sum up to the canonical square. -/
theorem SupportBundleTriple.windowTriple_sum (a b : SupportBundleTriple X)
    (L : Set X) (h : (a.sum b).datum.control ⊆ interior L) :
    ((a.sum b).windowTriple L h).IsIsomorphic
      ((a.windowTriple L (Set.Subset.trans Set.subset_union_left h)).sum
        (b.windowTriple L (Set.Subset.trans Set.subset_union_right h))) := by
  /- Use the vector-preserving restriction/direct-sum isomorphisms on source and target. On the
  boundary both routes act on each coordinate by the same original map, so the square
  commutes. -/
  obtain ⟨u, hu⟩ := exists_restrict_sum_iso
    (E := a.source.Fiber) (F := b.source.Fiber) L
  obtain ⟨w, hw⟩ := exists_restrict_sum_iso
    (E := a.target.Fiber) (F := b.target.Fiber) L
  refine ⟨u, w, ?_⟩
  intro x v
  let K := a.datum.control ∪ b.datum.control
  have hK : IsCompact K := a.datum.isCompact_control.union b.datum.isCompact_control
  let y : (Kᶜ : Set X) :=
    ⟨x.val.val, supportWindowBoundary_subset K L h x.property⟩
  -- The sum boundary uses one union control and the original two fiber actions.
  have hl := (a.sum b).windowBoundary_apply L h x v
  have hs := RelativeTriple.sum_apply
    (a.datum.enlarge K hK Set.subset_union_left).boundary
    (b.datum.enlarge K hK Set.subset_union_right).boundary y v
  have ha := a.datum.enlarge_apply K hK Set.subset_union_left y v.1
  have hb := b.datum.enlarge_apply K hK Set.subset_union_right y v.2
  have hleft := hl.trans (hs.trans (congrArg₂ Prod.mk ha hb))
  -- Restricting the two original triples separately gives these same components.
  have hr := RelativeTriple.sum_apply
    (a.windowBoundary L (Set.Subset.trans Set.subset_union_left h))
    (b.windowBoundary L (Set.Subset.trans Set.subset_union_right h)) x v
  have hwa := a.windowBoundary_apply L (Set.Subset.trans Set.subset_union_left h) x v.1
  have hwb := b.windowBoundary_apply L (Set.Subset.trans Set.subset_union_right h) x v.2
  have hright := hr.trans (congrArg₂ Prod.mk hwa hwb)
  exact (hw x.val _).trans ((hleft.trans hright.symm).trans
    (congrArg ((RelativeTriple.sum
      (a.windowBoundary L (Set.Subset.trans Set.subset_union_left h))
      (b.windowBoundary L (Set.Subset.trans Set.subset_union_right h))).linearEquiv x)
      (hu x.val v).symm))

/-- A window restriction of an identity triple is an identity triple up to isomorphism. -/
theorem supportBundleTriple_windowTriple_identity (E : FiniteBundle X) (L : Set X) :
    ((SupportBundleTriple.identity E).windowTriple L (Set.empty_subset _)).IsIsomorphic
      (BundleTriple.identity (supportWindowBoundary L) (E.restrict L)) := by
  /- The original global identity restricts to identity on every window boundary. The two
  source and target bundles are the same restrictions, giving the identity square. -/
  refine ⟨Iso.refl _, Iso.refl _, ?_⟩
  intro x v
  exact (SupportBundleTriple.identity E).windowBoundary_apply L (Set.empty_subset _) x v

end AtiyahSinger.ComplexBundle
