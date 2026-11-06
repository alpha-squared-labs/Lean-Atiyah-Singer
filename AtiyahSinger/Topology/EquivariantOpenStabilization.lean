/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantControlledOpenClass

/-!
# Restricting the same equivariant stabilization to a common open image

Public module ID: M1798.

A stabilization uses one specified complement on both sides and actual global
bundle isomorphisms. Its displayed boundary formula identifies the class after
controlled open restriction. The identity summand remains the same pulled-back
bundle and action; no cancellation or injectivity of open pushforward is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1800000 in
-- Keep the original stabilizer, both sum models and the dependent boundary restrictions.
/-- The same complement and boundary conjugation preserve the original common-open class. -/
theorem EquivariantSupportBundleTriple.kZeroClass_openRestrict_eq_of_stabilization
    (a b : EquivariantSupportBundleTriple G Y)
    (C : FiniteBundle Y) (σC : EquivariantStructure G C.Fiber)
    (e : Iso (a.1.source.sum C).Fiber b.1.source.Fiber)
    (j : Iso (a.1.target.sum C).Fiber b.1.target.Fiber)
    (he : e.IsEquivariant (a.2.sourceAction.sum σC) b.2.sourceAction)
    (hj : j.IsEquivariant (a.2.targetAction.sum σC) b.2.targetAction)
    (hcontrol : b.1.datum.control = a.1.datum.control)
    (hboundary : ∀ (y : Y) (ha : y ∈ a.1.datum.controlᶜ)
      (hb : y ∈ b.1.datum.controlᶜ) (v : b.1.source.Fiber y),
      b.1.datum.boundary.linearEquiv ⟨y, hb⟩ v =
        j.linearEquiv y
          (a.1.datum.boundary.linearEquiv ⟨y, ha⟩ ((e.linearEquiv y).symm v).1,
            ((e.linearEquiv y).symm v).2))
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : a.1.datum.control ⊆ Set.range f) :
    (b.openRestrict f hf heq (hcontrol ▸ hc)).kZeroClass =
      (a.openRestrict f hf heq hc).kZeroClass := by
  let I := EquivariantSupportBundleTriple.identity C σC
  let S := a.sum I
  have hSC : S.1.datum.control ⊆ a.1.datum.control := by
    change a.1.datum.control ∪ ∅ ⊆ a.1.datum.control
    simp
  have hBC : b.1.datum.control ⊆ a.1.datum.control := hcontrol.subset
  have hIrange : I.1.datum.control ⊆ Set.range f := Set.empty_subset _
  -- Restrict the actual conjugating isomorphisms on the unchanged compact control.
  have hSb : (S.openRestrict f hf heq (hSC.trans hc)).kZeroClass =
      (b.openRestrict f hf heq (hBC.trans hc)).kZeroClass := by
    apply EquivariantSupportBundleTriple.kZeroClass_openRestrict_eq_of_boundary
      S b f hf heq a.1.datum.control a.1.datum.isCompact_control
      a.2.isEquivariant.invariant_control hSC hBC hc e j he hj
    intro y hy v
    have hyS : y ∉ S.1.datum.control := fun h ↦ hy (hSC h)
    let z : (S.1.datum.controlᶜ : Set Y) := ⟨y, hyS⟩
    have hsum : S.1.datum.boundary.linearEquiv z v =
        (a.1.datum.boundary.linearEquiv ⟨y, hy⟩ v.1, v.2) := by
      have h := RelativeTriple.sum_apply
        (a.1.datum.enlarge S.1.datum.control S.1.datum.isCompact_control
          Set.subset_union_left).boundary
        (I.1.datum.enlarge S.1.datum.control S.1.datum.isCompact_control
          Set.subset_union_right).boundary z v
      change S.1.datum.boundary.linearEquiv z v = _ at h
      rw [a.1.datum.enlarge_apply, I.1.datum.enlarge_apply] at h
      exact h
    rw [hsum, hboundary y hy (fun h ↦ hy (hBC h)), LinearEquiv.symm_apply_apply]
  -- The neutral summand is the identity of the same pulled-back complement and action.
  let I' := I.openRestrict f hf heq hIrange
  let J := EquivariantSupportBundleTriple.identity (C.pullback f) (σC.pullback f heq)
  have hI' : I'.kZeroClass = 0 := by
    have hIso : I'.IsIsomorphic J := by
      refine ⟨∅, isCompact_empty, (fun _ _ ↦ Iff.rfl),
        Set.Subset.refl _, Set.Subset.refl _, Iso.refl _, Iso.refl _,
        (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
      intro x v
      rw [I'.1.datum.enlarge_apply, J.1.datum.enlarge_apply]
      change (I.1.datum.boundary.pullback f).linearEquiv ⟨x.val, x.property⟩ v = v
      rw [RelativeTriple.pullback_apply]
      rfl
    exact (equivariantSupportTripleKZero_generator_relations.1 I' J hIso).trans
      (equivariantSupportTripleKZero_generator_relations.2.2 (C.pullback f)
        (σC.pullback f heq))
  calc
    (b.openRestrict f hf heq (hcontrol ▸ hc)).kZeroClass =
        (S.openRestrict f hf heq (hSC.trans hc)).kZeroClass := hSb.symm
    _ = (a.openRestrict f hf heq hc).kZeroClass + I'.kZeroClass :=
      a.kZeroClass_openRestrict_sum I f hf heq hc hIrange
    _ = (a.openRestrict f hf heq hc).kZeroClass := by rw [hI', add_zero]

end AtiyahSinger.ComplexBundle
