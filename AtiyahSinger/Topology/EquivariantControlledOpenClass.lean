/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantOpenHomotopy

/-!
# The original common-open class from controlled comparison data

Public module ID: M1772.

An actual equivariant boundary square identifies an ambient triple with the
specified open pushforward. A homotopy whose complete control stays in that
open image identifies the two classes already on the common source. These
statements use the original controlled restriction and do not assert that
open pushforward is injective.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]
  [CompactSpace G] [T2Space G] [LocallyCompactSpace X] [T2Space X]

attribute [local instance] isFiniteRank_pullback

omit [T2Space G] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A uniformly controlled equivariant homotopy preserves the class on the common open source. -/
theorem CompactSupportTriple.EquivariantHomotopy.kZeroClass_openRestrict_eq
    (E F : FiniteBundle Y) (ρE : EquivariantStructure G E.Fiber)
    (ρF : EquivariantStructure G F.Fiber)
    (a b : CompactSupportTriple E.Fiber F.Fiber)
    (ha : a.IsEquivariant ρE ρF) (hb : b.IsEquivariant ρE ρF)
    (H : a.EquivariantHomotopy ρE ρF b)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : H.control ⊆ Set.range f) :
    ((EquivariantSupportBundleTriple.ofBoundary E F a ρE ρF ha).openRestrict
      f hf heq (H.left_control.trans hc)).kZeroClass =
    ((EquivariantSupportBundleTriple.ofBoundary E F b ρE ρF hb).openRestrict
      f hf heq (H.right_control.trans hc)).kZeroClass := by
  -- Pull back the actual cylinder, including its entire compact control.
  obtain ⟨J, _hJcontrol⟩ := H.exists_openRestrict f hf heq hc
  exact equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (E.pullback f) (F.pullback f) (ρE.pullback f heq) (ρF.pullback f heq)
    (a.openRestrict f hf (H.left_control.trans hc))
    (b.openRestrict f hf (H.right_control.trans hc))
    (ha.openRestrict f hf heq (H.left_control.trans hc))
    (hb.openRestrict f hf heq (H.right_control.trans hc)) ⟨J⟩

variable [LocallyCompactSpace Y] [T2Space Y]

omit [CompactSpace G] [T2Space G] [LocallyCompactSpace X] [T2Space X]
  [LocallyCompactSpace Y] [T2Space Y] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A specified global fiber square preserves the class after controlled open restriction. -/
theorem EquivariantSupportBundleTriple.kZeroClass_openRestrict_eq_of_boundary
    (a b : EquivariantSupportBundleTriple G Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (C : Set Y) (hC : IsCompact C)
    (hCi : ∀ (g : G) (y : Y), g • y ∈ C ↔ y ∈ C)
    (haC : a.1.datum.control ⊆ C) (hbC : b.1.datum.control ⊆ C)
    (hCrange : C ⊆ Set.range f)
    (e : Iso a.1.source.Fiber b.1.source.Fiber)
    (j : Iso a.1.target.Fiber b.1.target.Fiber)
    (he : e.IsEquivariant a.2.sourceAction b.2.sourceAction)
    (hj : j.IsEquivariant a.2.targetAction b.2.targetAction)
    (hboundary : ∀ (y : Y) (hy : y ∉ C) (v : a.1.source.Fiber y),
      j.linearEquiv y
          (a.1.datum.boundary.linearEquiv ⟨y, fun h ↦ hy (haC h)⟩ v) =
        b.1.datum.boundary.linearEquiv ⟨y, fun h ↦ hy (hbC h)⟩ (e.linearEquiv y v)) :
    (a.openRestrict f hf heq (haC.trans hCrange)).kZeroClass =
      (b.openRestrict f hf heq (hbC.trans hCrange)).kZeroClass := by
  let A := a.openRestrict f hf heq (haC.trans hCrange)
  let B := b.openRestrict f hf heq (hbC.trans hCrange)
  let D := f ⁻¹' C
  have hD : IsCompact D := hf.isEmbedding.isInducing.isCompact_preimage' hC hCrange
  have hDi (g : G) (x : X) : g • x ∈ D ↔ x ∈ D := by
    change f (g • x) ∈ C ↔ f x ∈ C
    rw [heq]
    exact hCi g (f x)
  have hAD : A.1.datum.control ⊆ D := fun _ hx ↦ haC hx
  have hBD : B.1.datum.control ⊆ D := fun _ hx ↦ hbC hx
  -- Pull back the same global maps; the common control is the exact inverse image.
  apply equivariantSupportTripleKZero_generator_relations.1 A B
  refine ⟨D, hD, hDi, hAD, hBD, e.pullback f, j.pullback f,
    (a.2.sourceAction.pullback_maps b.2.sourceAction f heq).2 e he,
    (a.2.targetAction.pullback_maps b.2.targetAction f heq).2 j hj, ?_⟩
  intro x v
  rw [A.1.datum.enlarge_apply, B.1.datum.enlarge_apply]
  change j.linearEquiv (f x.val)
      ((a.1.datum.boundary.pullback f).linearEquiv
        ⟨x.val, fun h ↦ x.property (haC h)⟩ v) =
    (b.1.datum.boundary.pullback f).linearEquiv
      ⟨x.val, fun h ↦ x.property (hbC h)⟩ (e.linearEquiv (f x.val) v)
  rw [RelativeTriple.pullback_apply, RelativeTriple.pullback_apply]
  exact hboundary (f x.val) x.property v

attribute [local instance] sumTopology isFiniteRank_sum

omit [CompactSpace G] [T2Space G] [LocallyCompactSpace X] [T2Space X]
  [LocallyCompactSpace Y] [T2Space Y] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compare the original sum pullback models and both exact boundary restrictions.
/-- Controlled open restriction preserves the original direct-sum class. -/
theorem EquivariantSupportBundleTriple.kZeroClass_openRestrict_sum
    (A B : EquivariantSupportBundleTriple G Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hA : A.1.datum.control ⊆ Set.range f) (hB : B.1.datum.control ⊆ Set.range f) :
    ((A.sum B).openRestrict f hf heq (Set.union_subset hA hB)).kZeroClass =
      (A.openRestrict f hf heq hA).kZeroClass + (B.openRestrict f hf heq hB).kZeroClass := by
  let a := A.openRestrict f hf heq hA
  let b := B.openRestrict f hf heq hB
  let c := (A.sum B).openRestrict f hf heq (Set.union_subset hA hB)
  let K := c.1.datum.control
  have hK : IsCompact K := c.1.datum.isCompact_control
  let u := sumPullbackIso f A.1.source B.1.source
  let v := sumPullbackIso f A.1.target B.1.target
  have hi : c.IsIsomorphic (a.sum b) := by
    refine ⟨K, hK, c.2.isEquivariant.invariant_control, Set.Subset.rfl,
      Set.Subset.rfl, u, v,
      EquivariantStructure.sumPullbackIso_isEquivariant _ _ _ _ f heq,
      EquivariantStructure.sumPullbackIso_isEquivariant _ _ _ _ f heq, ?_⟩
    intro x s
    let R := A.1.datum.control ∪ B.1.datum.control
    have hR : IsCompact R := A.1.datum.isCompact_control.union B.1.datum.isCompact_control
    let y : (Rᶜ : Set Y) := ⟨f x, x.property⟩
    have hl := c.1.datum.enlarge_apply K hK (Set.Subset.refl _) x s
    have hp := RelativeTriple.pullback_apply (A.1.datum.sum B.1.datum).boundary f x s
    have hs := RelativeTriple.sum_apply
      (A.1.datum.enlarge R hR Set.subset_union_left).boundary
      (B.1.datum.enlarge R hR Set.subset_union_right).boundary y s
    have ha := A.1.datum.enlarge_apply R hR Set.subset_union_left y s.1
    have hb := B.1.datum.enlarge_apply R hR Set.subset_union_right y s.2
    have hleft := hl.trans (hp.trans (hs.trans (congrArg₂ Prod.mk ha hb)))
    have hr := (a.1.datum.sum b.1.datum).enlarge_apply K hK (Set.Subset.refl _) x s
    have ht := RelativeTriple.sum_apply
      (a.1.datum.enlarge K hK Set.subset_union_left).boundary
      (b.1.datum.enlarge K hK Set.subset_union_right).boundary x s
    have hpa := a.1.datum.enlarge_apply K hK Set.subset_union_left x s.1
    have hpb := b.1.datum.enlarge_apply K hK Set.subset_union_right x s.2
    have hqa := RelativeTriple.pullback_apply A.1.datum.boundary f
      ⟨x.val, fun h ↦ x.property (Or.inl h)⟩ s.1
    have hqb := RelativeTriple.pullback_apply B.1.datum.boundary f
      ⟨x.val, fun h ↦ x.property (Or.inr h)⟩ s.2
    have hright := hr.trans (ht.trans (congrArg₂ Prod.mk (hpa.trans hqa) (hpb.trans hqb)))
    exact hleft.trans hright.symm
  exact (equivariantSupportTripleKZero_generator_relations.1 c (a.sum b) hi).trans
    (equivariantSupportTripleKZero_generator_relations.2.1 a b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Retain both original boundary restrictions and their dependent pullback comparisons.
/-- The actual equivariant boundary square gives the specified open-pushforward class. -/
theorem EquivariantSupportBundleTriple.kZeroClass_eq_openPushforward_of_boundary
    (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : b.1.datum.control ⊆ f '' a.1.datum.control)
    (e : Iso a.1.source.Fiber ((f : X → Y) *ᵖ b.1.source.Fiber))
    (j : Iso a.1.target.Fiber ((f : X → Y) *ᵖ b.1.target.Fiber))
    (he : e.IsEquivariant a.2.sourceAction (b.2.sourceAction.pullback f heq))
    (hj : j.IsEquivariant a.2.targetAction (b.2.targetAction.pullback f heq))
    (hboundary : ∀ (x : X) (hx : x ∈ a.1.datum.controlᶜ)
      (hfx : f x ∈ b.1.datum.controlᶜ) (v : a.1.source.Fiber x),
      j.linearEquiv x (a.1.datum.boundary.linearEquiv ⟨x, hx⟩ v) =
        b.1.datum.boundary.linearEquiv ⟨f x, hfx⟩ (e.linearEquiv x v)) :
    b.kZeroClass = equivariantSupportTripleKZeroOpenPushforward f hf heq a.kZeroClass := by
  have hcrange : b.1.datum.control ⊆ Set.range f := hc.trans (Set.image_subset_range _ _)
  let B := b.openRestrict f hf heq hcrange
  have hBA : B.1.datum.control ⊆ a.1.datum.control := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hc hx
    exact (hf.injective hxy) ▸ hy
  -- The same fiber isomorphisms compare the two boundaries on the original source control.
  have hIso : a.IsIsomorphic B := by
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, hBA, e, j, he, hj, ?_⟩
    intro x v
    rw [a.1.datum.enlarge_apply, B.1.datum.enlarge_apply]
    change j.linearEquiv x.val (a.1.datum.boundary.linearEquiv _ v) =
      (b.1.datum.boundary.pullback f).linearEquiv
        ⟨x.val, fun h ↦ x.property (hBA h)⟩ (e.linearEquiv x.val v)
    rw [RelativeTriple.pullback_apply]
    exact hboundary x.val x.property (fun h ↦ x.property (hBA h)) v
  have hclass : a.kZeroClass = B.kZeroClass :=
    equivariantSupportTripleKZero_generator_relations.1 a B hIso
  calc
    b.kZeroClass = equivariantSupportTripleKZeroOpenPushforward f hf heq B.kZeroClass :=
      (equivariantSupportTripleKZeroOpenPushforward_class f hf heq b hcrange).symm
    _ = equivariantSupportTripleKZeroOpenPushforward f hf heq a.kZeroClass := by rw [hclass]

end AtiyahSinger.ComplexBundle
