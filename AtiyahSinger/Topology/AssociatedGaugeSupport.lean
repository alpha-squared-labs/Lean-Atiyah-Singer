/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedGaugeBundle
public import AtiyahSinger.Topology.AssociatedSupportKZero

/-!
# Associated support descent in a principal gauge

Public module ID: M1537.

The actual gauge transforms both the fiber point and its vector by the same
original action. This identifies the descended support boundary with the
proper pullback of the original ordinary support class. No constant-rank or
trivial-action assumption is used; invariant controls retain the same support.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant isFiniteRank_pullback

variable {G P B Y : Type*} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [CompactSpace B] [T2Space B] [LocallyCompactSpace Y] [T2Space Y]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Descend the two original bundles and their same boundary before passing to virtual classes.
/-- Gauge descent is proper pullback along the original gauge-transformed fiber coordinate. -/
theorem exists_associatedSupportKZero_eq_pullback_of_gauge
    (hP : IsPrincipalBundle G projection) (θ : C(P, G))
    (hθ : ∀ (p : P) (g : G), θ (MulOpposite.op g • p) = θ p * g) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    ∃ (q : C(AssociatedBundle G P Y, Y)) (hq : IsProperMap q),
      (∀ (p : P) (y : Y), q (associatedBundleMk G P Y p y) = θ p • y) ∧
      ∀ v : EquivariantSupportTripleKZero G Y,
        associatedSupportKZero hP v = compactSupportKZeroPullback q hq
          (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget v)) := by
  classical
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let Z := AssociatedBundle G P Y
  let q := associatedGaugeProjection (Y := Y) θ hθ
  have hqmk (p : P) (y : Y) : q (associatedBundleMk G P Y p y) = θ p • y := rfl
  -- The compact base makes this actual fiber projection proper.
  obtain ⟨e, he⟩ := exists_associatedBundle_productHomeomorph_of_gauge (Y := Y) hP θ hθ
  have hqeq : (q : Z → Y) = Prod.snd ∘ e := by
    funext z
    induction z using Quotient.inductionOn with
    | h w => exact (congrArg Prod.snd (he w.1 w.2)).symm
  have hq : IsProperMap q := by
    rw [hqeq]
    exact isProperMap_snd_of_compactSpace.comp e.isProperMap
  refine ⟨q, hq, hqmk, ?_⟩
  intro v
  obtain ⟨a, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective v
  rw [associatedSupportKZero_class, equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply]
  let d := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant
  let b := a.1.datum.pullback q hq
  obtain ⟨u, hu⟩ := exists_associatedEquivariant_iso_gauge hP θ hθ a.1.source.Fiber a.2.sourceAction
  obtain ⟨w, hw⟩ := exists_associatedEquivariant_iso_gauge hP θ hθ a.1.target.Fiber a.2.targetAction
  -- Invariance identifies the same control before comparing the two boundary maps.
  have hd : d.control = b.control := by
    ext z
    induction z using Quotient.inductionOn with
    | h z =>
      exact (associatedControl_mk_mem_iff _ a.2.isEquivariant.invariant_control z.1 z.2).trans
        (a.2.isEquivariant.invariant_control (θ z.1) z.2).symm
  have hinc : d.control ⊆ b.control := hd.subset
  have hboundary : (d.enlarge b.control b.isCompact_control hinc).congr u w = b := by
    change CompactSupportTriple.mk b.control _ _ = CompactSupportTriple.mk b.control _ _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro s
    let p := (Quotient.out z.val).1
    let y := (Quotient.out z.val).2
    have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
    have hy : y ∈ a.1.datum.controlᶜ := by
      have hout : q z.val ∉ a.1.datum.control := z.property
      have heq : q z.val = θ p • y := (congrArg q hz).symm.trans (hqmk p y)
      exact fun h ↦ hout (heq.symm ▸
        (a.2.isEquivariant.invariant_control (θ p) y).mpr h)
    have hformula (p₀ : P) (y₀ : (a.1.datum.controlᶜ : Set Y))
        {z₀ : Z} (hz₀ : associatedBundleMk G P Y p₀ y₀ = z₀)
        (hout : z₀ ∈ d.controlᶜ) (s₀ : a.1.source.Fiber y₀) :
        w.linearEquiv z₀
            (d.boundary.linearEquiv ⟨z₀, hout⟩
              (associatedEquivariantFiberMk hP a.2.sourceAction p₀ y₀ hz₀ s₀)) =
          b.boundary.linearEquiv ⟨z₀, fun h ↦ hout (hd.symm ▸ h)⟩
            (u.linearEquiv z₀
              (associatedEquivariantFiberMk hP a.2.sourceAction p₀ y₀ hz₀ s₀)) := by
      cases hz₀
      have hdval : d.boundary.linearEquiv
          ⟨associatedBundleMk G P Y p₀ y₀, hout⟩
          (associatedEquivariantFiberMk hP a.2.sourceAction p₀ y₀ rfl s₀) =
            associatedEquivariantFiberMk hP a.2.targetAction p₀ y₀ rfl
              (a.1.datum.boundary.linearEquiv y₀ s₀) :=
        associatedSupportBoundary_apply hP a.1.datum a.2.sourceAction
          a.2.targetAction a.2.isEquivariant p₀ y₀ s₀
      calc
        w.linearEquiv (associatedBundleMk G P Y p₀ y₀)
            (d.boundary.linearEquiv ⟨associatedBundleMk G P Y p₀ y₀, hout⟩
              (associatedEquivariantFiberMk hP a.2.sourceAction p₀ y₀ rfl s₀)) =
            a.2.targetAction.linearMap (θ p₀) y₀ (a.1.datum.boundary.linearEquiv y₀ s₀) := by
          rw [hdval, hw]
        _ = b.boundary.linearEquiv
            ⟨associatedBundleMk G P Y p₀ y₀, fun h ↦ hout (hd.symm ▸ h)⟩
              (a.2.sourceAction.linearMap (θ p₀) y₀ s₀) :=
          (a.2.isEquivariant.boundary_intertwines (θ p₀) y₀ s₀).symm.trans
            (RelativeTriple.pullback_apply a.1.datum.boundary q
              ⟨associatedBundleMk G P Y p₀ y₀, fun h ↦ hout (hd.symm ▸ h)⟩
                (a.2.sourceAction.linearMap (θ p₀) y₀ s₀)).symm
        _ = b.boundary.linearEquiv
            ⟨associatedBundleMk G P Y p₀ y₀, fun h ↦ hout (hd.symm ▸ h)⟩
              (u.linearEquiv (associatedBundleMk G P Y p₀ y₀)
                (associatedEquivariantFiberMk hP a.2.sourceAction p₀ y₀ rfl s₀)) :=
          congrArg _ (hu p₀ y₀ s₀).symm
    obtain ⟨s₀, hs₀⟩ := (associatedEquivariantFiberMk_bijective
      hP a.2.sourceAction p y hz).2 (u.symm.linearEquiv z.val s)
    change w.linearEquiv z.val
      ((d.enlarge b.control b.isCompact_control hinc).boundary.linearEquiv z
        (u.symm.linearEquiv z.val s)) = b.boundary.linearEquiv z s
    rw [d.enlarge_apply, ← hs₀]
    exact (hformula p ⟨y, hy⟩ hz (fun h ↦ z.property (hinc h)) s₀).trans
      (congrArg (b.boundary.linearEquiv z)
        ((congrArg (u.linearEquiv z.val) hs₀).trans
          ((u.linearEquiv z.val).apply_symm_apply s)))
  calc
    associatedSupportClass hP a = d.compactSupportClass := rfl
    _ = (d.enlarge b.control b.isCompact_control hinc).compactSupportClass :=
      (d.compactSupportClass_enlarge b.control b.isCompact_control hinc).symm
    _ = ((d.enlarge b.control b.isCompact_control hinc).congr u w).compactSupportClass :=
      ((d.enlarge b.control b.isCompact_control hinc).compactSupportClass_congr u w).symm
    _ = b.compactSupportClass := congrArg _ hboundary
    _ = compactSupportKZeroPullback q hq a.1.datum.compactSupportClass :=
      a.1.datum.compactSupportClass_pullback q hq
    _ = compactSupportKZeroPullback q hq a.1.compactSupportClass := by
      congr 1
      exact compactSupportTriple_compactSupportClass_ofBoundary _ _ _

end AtiyahSinger
