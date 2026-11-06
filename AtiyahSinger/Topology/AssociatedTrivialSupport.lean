/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantDescent
public import AtiyahSinger.Topology.AssociatedSupportKZero
public import AtiyahSinger.Topology.AssociatedTrivialAction

/-!
# Associated support descent for the trivial group

Public module ID: M1555.

The original associated support class is the proper pullback of its ordinary
fiber class when the structure group is trivial. The actual quotient projection
keeps the original fiber coordinate, including locally varying bundle ranks.
This is the topological comparison needed for the zero-dimensional sphere in
SG III.13.6; no fixed-rank representative or analytic index formula is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant isFiniteRank_pullback

variable {G P B Y : Type*} [Group G] [Subsingleton G]
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
/-- Trivial-group support descent is proper pullback along the unchanged fiber coordinate. -/
theorem exists_associatedSupportKZero_eq_pullback_of_subsingleton
    (hP : IsPrincipalBundle G projection) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    ∃ (q : C(AssociatedBundle G P Y, Y)) (hq : IsProperMap q),
      (∀ (p : P) (y : Y), q (associatedBundleMk G P Y p y) = y) ∧
      ∀ v : EquivariantSupportTripleKZero G Y,
        associatedSupportKZero hP v = compactSupportKZeroPullback q hq
          (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget v)) := by
  classical
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let Z := AssociatedBundle G P Y
  have hact (g : G) (y : Y) : g • y = y := by
    rw [Subsingleton.elim g 1, one_smul]
  let q : C(Z, Y) := {
    toFun := Quotient.lift Prod.snd (by
      rintro x y ⟨g, rfl⟩
      exact (hact g⁻¹ x.2).symm)
    continuous_toFun := continuous_quot_lift _ continuous_snd }
  have hqmk (p : P) (y : Y) : q (associatedBundleMk G P Y p y) = y := rfl
  -- The compact base makes this actual fiber projection proper.
  obtain ⟨e, he⟩ := exists_associatedBundle_homeomorph_of_trivial_action hP hact
  have hqeq : (q : Z → Y) = Prod.snd ∘ e := by
    funext z
    induction z using Quotient.inductionOn with
    | h w => exact (congrArg Prod.snd (he w.1 w.2)).symm
  have hq : IsProperMap q := by
    rw [hqeq]
    exact isProperMap_snd_of_compactSpace.comp e.isProperMap
  -- Each descended bundle retains its original fiber, without a rank replacement.
  have bundle (E : Y → Type) [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      (σ : EquivariantStructure G E) :
      ∃ a : Iso (AssociatedEquivariantFiber hP σ) ((q : Z → Y) *ᵖ E),
        ∀ (p : P) (y : Y) (v : E y),
          a.linearEquiv (associatedBundleMk G P Y p y)
            (associatedEquivariantFiberMk hP σ p y rfl v) = v := by
    let L (p : P) (y : Y) : E y ≃ₗ[ℂ] ((q : Z → Y) *ᵖ E)
        (associatedBundleMk G P Y p y) := LinearEquiv.refl ℂ (E y)
    have hc : Continuous (fun z : P × TotalSpace Unit E ↦
        (⟨associatedBundleMk G P Y z.1 z.2.proj, L z.1 z.2.proj z.2.snd⟩ :
          TotalSpace Unit ((q : Z → Y) *ᵖ E))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E q).continuous_iff]
      exact (continuous_quot_mk.comp
        (continuous_fst.prodMk (continuous_proj.comp continuous_snd))).prodMk continuous_snd
    have hcov : letI := σ.toMulAction
        ∀ (p : P) (g : G) (w : TotalSpace Unit E),
          (⟨associatedBundleMk G P Y (MulOpposite.op g • p) (g⁻¹ • w.proj),
            L (MulOpposite.op g • p) (g⁻¹ • w.proj) (σ.linearMap g⁻¹ w.proj w.snd)⟩ :
              TotalSpace Unit ((q : Z → Y) *ᵖ E)) =
            ⟨associatedBundleMk G P Y p w.proj, L p w.proj w.snd⟩ := by
      let := σ.toMulAction
      intro p g w
      have hg : g = 1 := Subsingleton.elim _ _
      subst g
      have hp : MulOpposite.op (1 : G) • p = p := one_smul Gᵐᵒᵖ p
      have hw : (1 : G)⁻¹ • w = w := by rw [inv_one, one_smul]
      have hpair : (MulOpposite.op (1 : G) • p, (1 : G)⁻¹ • w) = (p, w) :=
        Prod.ext hp hw
      exact congrArg (fun z : P × TotalSpace Unit E ↦
        (⟨associatedBundleMk G P Y z.1 z.2.proj, L z.1 z.2.proj z.2.snd⟩ :
          TotalSpace Unit ((q : Z → Y) *ᵖ E))) hpair
    exact exists_associatedEquivariant_iso_of_covariant_equiv hP σ _ L hc hcov
  refine ⟨q, hq, hqmk, ?_⟩
  intro v
  obtain ⟨a, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective v
  rw [associatedSupportKZero_class, equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply]
  let d := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant
  let b := a.1.datum.pullback q hq
  obtain ⟨u, hu⟩ := bundle a.1.source.Fiber a.2.sourceAction
  obtain ⟨w, hw⟩ := bundle a.1.target.Fiber a.2.targetAction
  -- Identify the same control before comparing the two original boundary maps.
  have hd : d.control = b.control := by
    ext z
    induction z using Quotient.inductionOn with
    | h z => exact associatedControl_mk_mem_iff _ a.2.isEquivariant.invariant_control z.1 z.2
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
      have heq : q z.val = y := (congrArg q hz).symm.trans (hqmk p y)
      exact fun h ↦ hout (heq.symm ▸ h)
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
      have hpull : b.boundary.linearEquiv
          ⟨associatedBundleMk G P Y p₀ y₀, fun h ↦ hout (hd.symm ▸ h)⟩ s₀ =
            a.1.datum.boundary.linearEquiv y₀ s₀ :=
        RelativeTriple.pullback_apply a.1.datum.boundary q
          ⟨associatedBundleMk G P Y p₀ y₀, y₀.property⟩ s₀
      exact (congrArg (w.linearEquiv (associatedBundleMk G P Y p₀ y₀)) hdval).trans
        ((hw p₀ y₀ _).trans (hpull.symm.trans
          (congrArg (b.boundary.linearEquiv
            ⟨associatedBundleMk G P Y p₀ y₀, fun h ↦ hout (hd.symm ▸ h)⟩)
              (hu p₀ y₀ s₀).symm)))
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
