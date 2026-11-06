/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealBundleSupport
public import AtiyahSinger.Topology.SupportTripleTransport
public import Mathlib.Topology.PartitionOfUnity

/-!
# Continuous fiber norms and radial support representatives

Public module ID: M2036.

These constructions use the original local real-linear charts, allowing locally
varying finite rank. A partition of unity gives a continuous fiber norm, whose
closed disks over compact base sets are compact in the original total space.
This is the topological radial step of SG III.13, Lemma 13.3; no smooth metric,
constant positive rank, or properness of the fiber contraction is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle ComplexBundle
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [LocallyCompactSpace X]
  (G : Type*) (V : X → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [hV : RealBundle.IsFiniteRank G V]

include hV in
/-- The original finite real bundle admits a continuous fiber norm with compact
closed disks over compact base sets. The grouped certificate describes this
single construction and applies also to zero-rank fibers. -/
theorem exists_continuous_fiber_norm :
    ∃ ν : C(TotalSpace G V, ℝ),
      (∀ z, 0 ≤ ν z) ∧
      (∀ x (v : V x), ν ⟨x, v⟩ = 0 ↔ v = 0) ∧
      (∀ x (v : V x) (t : ℝ), ν ⟨x, t • v⟩ = |t| * ν ⟨x, v⟩) ∧
      (∀ x (u v : V x), ν ⟨x, u + v⟩ ≤ ν ⟨x, u⟩ + ν ⟨x, v⟩) ∧
      (∀ (K : Set X), IsCompact K → ∀ R : ℝ,
        IsCompact {z : TotalSpace G V | z.proj ∈ K ∧ ν z ≤ R}) := by
  classical
  -- Positive partition weights combine the original finite-dimensional chart norms.
  choose r e he hlin using hV.exists_linear_trivialization
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : X ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, he x⟩)
  let N (z : TotalSpace G V) : ℝ :=
    ∑ i ∈ ρ.finsupport z.proj, ρ i z.proj * ‖((e i) z).2‖
  have hactive {i x : X} (hi : i ∈ ρ.finsupport x) : x ∈ (e i).baseSet :=
    hρ i (subset_closure ((ρ.mem_finsupport x).mp hi))
  have hnonneg (z : TotalSpace G V) : 0 ≤ N z :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (ρ.nonneg i z.proj) (norm_nonneg _)
  have hterm (z : TotalSpace G V) (i : X) :
      ρ i z.proj * ‖((e i) z).2‖ ≤ N z := by
    by_cases hi : i ∈ ρ.finsupport z.proj
    · exact Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (ρ.nonneg j z.proj)
          (norm_nonneg (((e j) z).2))) hi
    · have hz : ρ i z.proj = 0 := by
        simpa only [ρ.mem_finsupport, Function.mem_support, not_not] using hi
      simpa only [hz, zero_mul] using hnonneg z
  -- Pull the same partition to the total space; chart norms need continuity only locally.
  let ρV : PartitionOfUnity X (TotalSpace G V) Set.univ := {
    toFun i := (ρ i).comp (projection G V)
    locallyFinite' := ρ.locallyFinite.preimage_continuous (continuous_projection G V)
    nonneg' i z := ρ.nonneg i z.proj
    sum_eq_one' z _ := ρ.sum_eq_one (Set.mem_univ z.proj)
    sum_le_one' z := ρ.sum_le_one z.proj }
  have hρV : ρV.IsSubordinate (fun i ↦ (π G V) ⁻¹' (e i).baseSet) := by
    intro i z hz
    exact hρ i ((tsupport_comp_subset_preimage (ρ i) (continuous_projection G V)) hz)
  have hcont : Continuous N := by
    have hlocal (i : X) : ContinuousOn
        (fun z : TotalSpace G V ↦ ‖((e i) z).2‖) ((π G V) ⁻¹' (e i).baseSet) :=
      (continuous_snd.comp_continuousOn
        ((e i).toOpenPartialHomeomorph.continuousOn.mono fun _ hz ↦
          (e i).mem_source.mpr hz)).norm
    have h := hρV.continuous_finsum_smul
      (fun i ↦ (e i).open_baseSet.preimage (continuous_projection G V)) hlocal
    apply h.congr
    intro z
    have hsum := ρ.sum_finsupport_smul_eq_finsum
      (x₀ := z.proj) (fun i _ ↦ ‖((e i) z).2‖)
    change (∑ᶠ i, ρ i z.proj • ‖((e i) z).2‖) = N z
    simpa only [N, smul_eq_mul] using hsum.symm
  refine ⟨⟨N, hcont⟩, hnonneg, ?_, ?_, ?_, ?_⟩
  · intro x v
    constructor
    · intro hv
      obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ x)
      have hix : x ∈ (e i).baseSet := hρ i (subset_closure (ne_of_gt hi))
      have hn : ‖((e i) ⟨x, v⟩).2‖ = 0 := by
        have ht := hterm ⟨x, v⟩ i
        change N ⟨x, v⟩ = 0 at hv
        rw [hv] at ht
        nlinarith [norm_nonneg (((e i) ⟨x, v⟩).2)]
      have hc : (e i) ⟨x, v⟩ = (e i) ⟨x, 0⟩ := by
        apply Prod.ext
        · exact ((e i).proj_toFun _ ((e i).mem_source.mpr hix)).trans
            ((e i).proj_toFun ⟨x, 0⟩ ((e i).mem_source.mpr hix)).symm
        · exact (norm_eq_zero.mp hn).trans ((hlin i x hix).map_zero).symm
      have hp := (e i).injOn ((e i).mem_source.mpr hix)
        ((e i).mem_source.mpr hix) hc
      exact eq_of_heq (congr_arg_heq (fun z : TotalSpace G V ↦ z.snd) hp)
    · rintro rfl
      change N ⟨x, 0⟩ = 0
      apply Finset.sum_eq_zero
      intro i hi
      rw [(hlin i x (hactive hi)).map_zero, norm_zero, mul_zero]
  · intro x v t
    change N ⟨x, t • v⟩ = |t| * N ⟨x, v⟩
    dsimp only [N]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hlin i x (hactive hi)).map_smul, norm_smul, Real.norm_eq_abs]
    ring
  · intro x u v
    change N ⟨x, u + v⟩ ≤ N ⟨x, u⟩ + N ⟨x, v⟩
    dsimp only [N]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [(hlin i x (hactive hi)).map_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (ρ.nonneg i x)
  · intro K hK R
    -- Near each base point one weight is bounded below, controlling the chart norm.
    have hlocal (x : X) : ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
        ∃ D : Set (TotalSpace G V), IsCompact D ∧
          {z : TotalSpace G V | z.proj ∈ L ∧ N z ≤ R} ⊆ D := by
      obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ x)
      have hix : x ∈ (e i).baseSet := hρ i (subset_closure (ne_of_gt hi))
      let c : ℝ := ρ i x / 2
      have hc : 0 < c := half_pos hi
      let U : Set X := (e i).baseSet ∩ {y | c < ρ i y}
      have hU : IsOpen U := (e i).open_baseSet.inter
        (isOpen_lt continuous_const (ρ i).continuous)
      have hxU : x ∈ U := ⟨hix, by dsimp [c]; linarith⟩
      obtain ⟨L, hL, hxL, hLU⟩ := exists_compact_subset hU hxU
      let B : Set (X × (Fin (r i) → ℝ)) := L ×ˢ Metric.closedBall 0 (R / c)
      have hB : IsCompact B := hL.prod (isCompact_closedBall _ _)
      have hBt : B ⊆ (e i).target := fun y hy ↦ (e i).mem_target.mpr (hLU hy.1).1
      refine ⟨L, hL, hxL, (e i).toPartialEquiv.symm '' B,
        hB.image_of_continuousOn ((e i).toOpenPartialHomeomorph.continuousOn_symm.mono hBt), ?_⟩
      intro z hz
      have hzbase : z.proj ∈ (e i).baseSet := (hLU hz.1).1
      have hcoords : ‖((e i) z).2‖ ≤ R / c := by
        apply (le_div_iff₀ hc).mpr
        have hw : c ≤ ρ i z.proj := le_of_lt (hLU hz.1).2
        calc
          ‖((e i) z).2‖ * c ≤ ρ i z.proj * ‖((e i) z).2‖ := by
            nlinarith [norm_nonneg (((e i) z).2)]
          _ ≤ N z := hterm z i
          _ ≤ R := hz.2
      refine ⟨(e i) z, ?_, (e i).left_inv ((e i).mem_source.mpr hzbase)⟩
      refine ⟨?_, ?_⟩
      · change ((e i).toOpenPartialHomeomorph z).1 ∈ L
        rw [(e i).proj_toFun z ((e i).mem_source.mpr hzbase)]
        exact hz.1
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hcoords
    choose L hL hxL D hD hLD using hlocal
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x ↦ interior (L x))
      (fun _ ↦ isOpen_interior) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxL x⟩)
    have hcover : {z : TotalSpace G V | z.proj ∈ K ∧ N z ≤ R} ⊆ ⋃ x ∈ s, D x := by
      intro z hz
      obtain ⟨x, hxs, hx⟩ := Set.mem_iUnion₂.mp (hs hz.1)
      exact Set.mem_iUnion₂.mpr ⟨x, hxs, hLD x ⟨interior_subset hx, hz.2⟩⟩
    -- The desired disk is closed and lies in a finite union of these original-chart boxes.
    have hclosed : IsClosed {z : TotalSpace G V | z.proj ∈ K ∧ N z ≤ R} :=
      (hK.isClosed.preimage (continuous_projection G V)).inter
        (isClosed_le hcont continuous_const)
    exact (s.isCompact_biUnion fun x _ ↦ hD x).of_isClosed_subset hclosed hcover

attribute [local instance] ComplexBundle.isFiniteRank_pullback

omit [ParacompactSpace X] [LocallyCompactSpace X] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reparametrize a pullback boundary along its actual real fiber. Continuity
is needed only over the compact base control: off it the supplied frame fixes
the boundary independently of the vector. -/
private theorem exists_boundary_reparametrization
    (E F : FiniteBundle X)
    (a : CompactSupportTriple
      ((projection G V : TotalSpace G V → X) *ᵖ E.Fiber)
      ((projection G V : TotalSpace G V → X) *ᵖ F.Fiber))
    (K : Set X) (hK : IsCompact K)
    (hcontrol : ∀ z ∈ a.control, z.proj ∈ K)
    (τ : RelativeTriple E.Fiber F.Fiber Kᶜ)
    (hτ : ∀ (z : TotalSpace G V) (hz : z.proj ∉ K) (ha : z ∈ a.controlᶜ),
      a.boundary.linearEquiv ⟨z, ha⟩ = τ.linearEquiv ⟨z.proj, hz⟩)
    {B : Type*} [TopologicalSpace B] (p : C(B, TotalSpace G V)) (s : B → ℝ)
    (hs : ∀ b, (p b).proj ∈ K → ContinuousAt s b)
    (hsupport : ∀ b, (⟨(p b).proj, s b • (p b).snd⟩ : TotalSpace G V) ∈ a.controlᶜ) :
    ∃ d : Iso ((p : B → TotalSpace G V) *ᵖ
        ((projection G V : TotalSpace G V → X) *ᵖ E.Fiber))
      ((p : B → TotalSpace G V) *ᵖ
        ((projection G V : TotalSpace G V → X) *ᵖ F.Fiber)),
      ∀ b v, d.linearEquiv b v =
        a.boundary.linearEquiv ⟨⟨(p b).proj, s b • (p b).snd⟩, hsupport b⟩ v := by
  classical
  let πV := projection G V
  let PE := (πV : TotalSpace G V → X) *ᵖ E.Fiber
  let PF := (πV : TotalSpace G V → X) *ᵖ F.Fiber
  let W := TotalSpace Unit ((p : B → TotalSpace G V) *ᵖ PE)
  let q (t : B → ℝ) (b : B) : TotalSpace G V := ⟨(p b).proj, t b • (p b).snd⟩
  let action (t : B → ℝ) (ht : ∀ b, q t b ∈ a.controlᶜ) (w : W) :
      TotalSpace Unit ((p : B → TotalSpace G V) *ᵖ PF) :=
    ⟨w.proj, a.boundary.linearEquiv ⟨q t w.proj, ht w.proj⟩ w.snd⟩
  have hb : Continuous (π Unit ((p : B → TotalSpace G V) *ᵖ PE)) :=
    Pullback.continuous_proj Unit PE p
  have he : Continuous (fun w : W ↦
      (⟨(p w.proj).proj, w.snd⟩ : TotalSpace Unit E.Fiber)) :=
    (Pullback.continuous_lift Unit E.Fiber πV).comp (Pullback.continuous_lift Unit PE p)
  -- Whenever the scalar is continuous, both induced pullback topologies preserve continuity.
  have hlocal (t : B → ℝ) (ht : ∀ b, q t b ∈ a.controlᶜ) (w : W)
      (hc : ContinuousAt t w.proj) : ContinuousAt (action t ht) w := by
    have hq : ContinuousAt (q t) w.proj := (continuous_scaling G V).continuousAt.comp
      (hc.prodMk p.continuous.continuousAt)
    have hin : ContinuousAt (fun w : W ↦
        (⟨⟨q t w.proj, ht w.proj⟩, w.snd⟩ :
          TotalSpace Unit (Restrict PE a.controlᶜ))) w := by
      erw [(inducing_pullbackTotalSpaceEmbedding Unit PE
        (Subtype.val : (a.controlᶜ : Set _) → TotalSpace G V)).continuousAt_iff]
      apply ((hq.comp hb.continuousAt).codRestrict _).prodMk
      erw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber πV).continuousAt_iff]
      exact (hq.comp hb.continuousAt).prodMk he.continuousAt
    have hout := a.boundary.continuous_total.continuousAt.comp hin
    have hf := (Pullback.continuous_lift Unit F.Fiber πV).continuousAt.comp
      ((Pullback.continuous_lift Unit PF
        (Subtype.val : (a.controlᶜ : Set _) → TotalSpace G V)).continuousAt.comp hout)
    erw [(inducing_pullbackTotalSpaceEmbedding Unit PF p).continuousAt_iff]
    apply hb.continuousAt.prodMk
    erw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber πV).continuousAt_iff]
    exact (p.continuous.comp hb).continuousAt.prodMk hf
  have hcontinuous : Continuous (action s hsupport) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    by_cases hx : (p w.proj).proj ∈ K
    · exact hlocal s hsupport w (hs w.proj hx)
    · -- Off K the boundary is constant in the real fiber, including at its zero vector.
      let t (b : B) : ℝ := if (p b).proj ∈ K then s b else 0
      have ht (b : B) : q t b ∈ a.controlᶜ := by
        by_cases h : (p b).proj ∈ K
        · simpa only [q, t, ite_eq_left h] using hsupport b
        · intro hz
          exact h (hcontrol (q t b) hz)
      have hneigh : ∀ᶠ b in 𝓝 w.proj, (p b).proj ∉ K :=
        ((continuous_projection G V).comp p.continuous).continuousAt
          (hK.isClosed.isOpen_compl.mem_nhds hx)
      have htcont : ContinuousAt t w.proj := continuousAt_const.congr_of_eventuallyEq (by
        filter_upwards [hneigh] with b hb
        exact ite_eq_right hb)
      apply (hlocal t ht w htcont).congr_of_eventuallyEq
      filter_upwards [hb.continuousAt hneigh] with z hz
      dsimp only [action]
      congr 1
      change a.boundary.linearEquiv ⟨q s z.proj, hsupport z.proj⟩ z.snd =
        a.boundary.linearEquiv ⟨q t z.proj, ht z.proj⟩ z.snd
      rw [hτ (q s z.proj) hz, hτ (q t z.proj) hz]
      rfl
  let f : Hom ((p : B → TotalSpace G V) *ᵖ PE)
      ((p : B → TotalSpace G V) *ᵖ PF) := {
    linearMap b := (a.boundary.linearEquiv ⟨q s b, hsupport b⟩).toLinearMap
    continuous_total := hcontinuous }
  exact ⟨f.toIso (fun b ↦ (a.boundary.linearEquiv ⟨q s b, hsupport b⟩).bijective),
    fun _ _ ↦ rfl⟩

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in

/-- A pullback triple with a fixed exterior base frame has a radially homogeneous
representative supported precisely on the compact part of the zero section.
Its class is compared by a homotopy outside one compact disk. -/
theorem exists_radial_representative
    (E F : FiniteBundle X)
    (a : CompactSupportTriple
      ((projection G V : TotalSpace G V → X) *ᵖ E.Fiber)
      ((projection G V : TotalSpace G V → X) *ᵖ F.Fiber))
    (K : Set X) (hK : IsCompact K)
    (hcontrol : ∀ z ∈ a.control, z.proj ∈ K)
    (τ : RelativeTriple E.Fiber F.Fiber Kᶜ)
    (hτ : ∀ (z : TotalSpace G V) (hz : z.proj ∉ K) (ha : z ∈ a.controlᶜ),
      a.boundary.linearEquiv ⟨z, ha⟩ = τ.linearEquiv ⟨z.proj, hz⟩) :
    ∃ b : CompactSupportTriple
      ((projection G V : TotalSpace G V → X) *ᵖ E.Fiber)
      ((projection G V : TotalSpace G V → X) *ᵖ F.Fiber),
      b.control = zeroSection G V '' K ∧
      (∀ (x : X) (v : V x) (t : ℝ), 0 < t →
        ∀ (hv : (⟨x, v⟩ : TotalSpace G V) ∈ b.controlᶜ)
          (htv : (⟨x, t • v⟩ : TotalSpace G V) ∈ b.controlᶜ),
          b.boundary.linearEquiv ⟨⟨x, t • v⟩, htv⟩ =
            b.boundary.linearEquiv ⟨⟨x, v⟩, hv⟩) ∧
      (∀ (z : TotalSpace G V) (hz : z.proj ∉ K) (hb : z ∈ b.controlᶜ),
        b.boundary.linearEquiv ⟨z, hb⟩ = τ.linearEquiv ⟨z.proj, hz⟩) ∧
      b.compactSupportClass = a.compactSupportClass := by
  classical
  let Z := TotalSpace G V
  let πV := projection G V
  let PE := (πV : Z → X) *ᵖ E.Fiber
  let PF := (πV : Z → X) *ᵖ F.Fiber
  obtain ⟨ν, hν, hzero, hsmul, _, hdisk⟩ := exists_continuous_fiber_norm G V
  have hsame (x : X) (v w : V x)
      (hv : (⟨x, v⟩ : Z) ∈ a.controlᶜ) (hw : (⟨x, w⟩ : Z) ∈ a.controlᶜ)
      (h : v = w) (u : E.Fiber x) :
      a.boundary.linearEquiv ⟨⟨x, v⟩, hv⟩ u =
        a.boundary.linearEquiv ⟨⟨x, w⟩, hw⟩ u := by
    subst w
    rfl
  obtain ⟨B, hB⟩ := a.isCompact_control.bddAbove_image ν.continuous.continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound (z : Z) (hz : z ∈ a.control) : ν z < R := by
    have h := hB (Set.mem_image_of_mem ν hz)
    dsimp only [R]
    linarith [le_max_left B 0]
  let K₀ : Set Z := zeroSection G V '' K
  have hK₀ : IsCompact K₀ := hK.image (zeroSection G V).continuous
  have hpos (z : Z) (hz : z ∈ K₀ᶜ) (hx : z.proj ∈ K) : 0 < ν z := by
    apply lt_of_le_of_ne (hν z)
    intro h
    have hv := (hzero z.proj z.snd).mp h.symm
    apply hz
    refine ⟨z.proj, hx, ?_⟩
    change (⟨z.proj, 0⟩ : Z) = z
    exact TotalSpace.ext rfl (heq_of_eq hv.symm)
  let p₀ : C((K₀ᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let s (z : (K₀ᶜ : Set Z)) : ℝ := R / ν z.val
  have hs (z : (K₀ᶜ : Set Z)) (hx : z.val.proj ∈ K) : ContinuousAt s z :=
    continuousAt_const.div (ν.continuous.comp continuous_subtype_val).continuousAt
      (ne_of_gt (hpos z.val z.property hx))
  have hsupport (z : (K₀ᶜ : Set Z)) :
      (⟨z.val.proj, s z • z.val.snd⟩ : Z) ∈ a.controlᶜ := by
    intro ha
    have hx : z.val.proj ∈ K := hcontrol ⟨z.val.proj, s z • z.val.snd⟩ ha
    have hp := hpos z.val z.property hx
    have hn : ν ⟨z.val.proj, s z • z.val.snd⟩ = R := by
      rw [hsmul, abs_of_pos (div_pos hR hp)]
      exact div_mul_cancel₀ R (ne_of_gt hp)
    exact (lt_irrefl R) (hn ▸ hbound _ ha)
  -- Normalize every nonzero vector to the same sphere, and use the fixed frame across zero off K.
  obtain ⟨d, hd⟩ := exists_boundary_reparametrization G V E F a K hK hcontrol τ hτ
    p₀ s hs hsupport
  let b : CompactSupportTriple PE PF := ⟨K₀, hK₀, d⟩
  have hb (z : Z) (hz : z.proj ∉ K) (h : z ∈ K₀ᶜ) :
      b.boundary.linearEquiv ⟨z, h⟩ = τ.linearEquiv ⟨z.proj, hz⟩ := by
    apply LinearEquiv.ext
    intro v
    rw [show b.boundary.linearEquiv ⟨z, h⟩ v = _ from hd ⟨z, h⟩ v]
    exact congrArg (fun f : E.Fiber z.proj ≃ₗ[ℂ] F.Fiber z.proj ↦ f v)
      (hτ ⟨z.proj, s ⟨z, h⟩ • z.snd⟩ hz _)
  refine ⟨b, rfl, ?_, hb, ?_⟩
  · intro x v t ht hv htv
    by_cases hx : x ∈ K
    · have hp := hpos ⟨x, v⟩ hv hx
      have hnt : ν ⟨x, t • v⟩ = t * ν ⟨x, v⟩ := by
        rw [hsmul, abs_of_pos ht]
      have hrad : (⟨x, s ⟨⟨x, t • v⟩, htv⟩ • (t • v)⟩ : Z) =
          ⟨x, s ⟨⟨x, v⟩, hv⟩ • v⟩ := by
        dsimp only [s]
        rw [hnt, smul_smul]
        have hc : R / (t * ν ⟨x, v⟩) * t = R / ν ⟨x, v⟩ := by
          field_simp
        rw [hc]
      have hfiber : s ⟨⟨x, t • v⟩, htv⟩ • (t • v) = s ⟨⟨x, v⟩, hv⟩ • v :=
        eq_of_heq (congr_arg_heq (fun z : Z ↦ z.snd) hrad)
      apply LinearEquiv.ext
      intro w
      change E.Fiber x at w
      change d.linearEquiv ⟨⟨x, t • v⟩, htv⟩ w = d.linearEquiv ⟨⟨x, v⟩, hv⟩ w
      rw [hd, hd]
      change a.boundary.linearEquiv
          ⟨⟨x, s ⟨⟨x, t • v⟩, htv⟩ • (t • v)⟩, _⟩ w =
        a.boundary.linearEquiv ⟨⟨x, s ⟨⟨x, v⟩, hv⟩ • v⟩, _⟩ w
      exact hsame x _ _ _ _ hfiber w
    · exact (hb ⟨x, t • v⟩ hx htv).trans (hb ⟨x, v⟩ hx hv).symm
  · -- A common compact disk controls the interpolation from the old radius to R.
    let D : Set Z := {z | z.proj ∈ K ∧ ν z ≤ R}
    have hD : IsCompact D := hdisk K hK R
    have haD : a.control ⊆ D := fun z hz ↦ ⟨hcontrol z hz, (hbound z hz).le⟩
    have hbD : b.control ⊆ D := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨hx, ?_⟩
      change ν ⟨x, 0⟩ ≤ R
      rw [(hzero x 0).mpr rfl]
      exact hR.le
    let pD : C((Dᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
    let sndD : C(unitInterval × (Dᶜ : Set Z), (Dᶜ : Set Z)) := ⟨Prod.snd, continuous_snd⟩
    let p := pD.comp sndD
    let c (z : unitInterval × (Dᶜ : Set Z)) : ℝ :=
      (1 - (z.1 : ℝ)) + (z.1 : ℝ) * R / ν z.2.val
    have hlarge (z : (Dᶜ : Set Z)) (hx : z.val.proj ∈ K) : R < ν z.val :=
      lt_of_not_ge (fun h ↦ z.property ⟨hx, h⟩)
    have hc (z : unitInterval × (Dᶜ : Set Z)) (hx : (p z).proj ∈ K) : ContinuousAt c z :=
      ((continuousAt_const.sub
        (continuous_subtype_val.comp continuous_fst).continuousAt).add
        (((continuous_subtype_val.comp continuous_fst).continuousAt.mul continuousAt_const).div
          ((ν.continuous.comp continuous_subtype_val).comp continuous_snd).continuousAt
          (ne_of_gt (hR.trans (hlarge z.2 hx)))))
    have hcSupport (z : unitInterval × (Dᶜ : Set Z)) :
        (⟨(p z).proj, c z • (p z).snd⟩ : Z) ∈ a.controlᶜ := by
      intro ha
      have hx : z.2.val.proj ∈ K :=
        hcontrol ⟨(p z).proj, c z • (p z).snd⟩ ha
      have hn := hlarge z.2 hx
      have hνpos := hR.trans hn
      have hcpos : 0 < c z := by
        dsimp only [c]
        have ht := z.1.property
        have hratio := div_pos hR hνpos
        by_cases ht₁ : (z.1 : ℝ) = 1
        · simp only [ht₁, sub_self, one_mul, zero_add]
          exact hratio
        · have htlt : (z.1 : ℝ) < 1 := lt_of_le_of_ne ht.2 ht₁
          exact add_pos_of_pos_of_nonneg (sub_pos.mpr htlt)
            (div_nonneg (mul_nonneg ht.1 hR.le) hνpos.le)
      have hnorm : R ≤ ν ⟨(p z).proj, c z • (p z).snd⟩ := by
        rw [hsmul, abs_of_pos hcpos]
        change R ≤ c z * ν z.2.val
        dsimp only [c]
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hνpos)]
        nlinarith [z.1.property.1, z.1.property.2]
      exact (not_lt_of_ge hnorm) (hbound _ ha)
    obtain ⟨j, hj⟩ := exists_boundary_reparametrization G V E F a K hK hcontrol τ hτ
      p c hc hcSupport
    let ce := pullbackCompIso (E := PE) pD sndD
    let cf := pullbackCompIso (E := PF) pD sndD
    let j' := ce.trans (j.trans cf.symm)
    have hj' (z : unitInterval × (Dᶜ : Set Z)) (v : E.Fiber z.2.val.proj) :
        j'.linearEquiv z v =
          a.boundary.linearEquiv ⟨⟨(p z).proj, c z • (p z).snd⟩, hcSupport z⟩ v := by
      change (cf.linearEquiv z).symm (j.linearEquiv z (ce.linearEquiv z v)) = _
      rw [pullbackCompIso_apply, hj]
      apply (cf.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    have H : a.Homotopic b := by
      refine ⟨D, hD, haD, hbD, ⟨{ iso := j', map_zero := ?_, map_one := ?_ }⟩⟩
      · intro z v
        change (Dᶜ : Set Z) at z
        change E.Fiber z.val.proj at v
        refine (hj' (0, z) v).trans ?_
        refine Eq.trans ?_ (a.enlarge_apply D hD haD z v).symm
        have hc₀ : c (0, z) = 1 := by simp [c]
        apply hsame z.val.proj _ z.val.snd _ _ _ v
        change c (0, z) • z.val.snd = z.val.snd
        rw [hc₀, one_smul]
      · intro z v
        change (Dᶜ : Set Z) at z
        change E.Fiber z.val.proj at v
        refine (hj' (1, z) v).trans ?_
        refine Eq.trans ?_ (b.enlarge_apply D hD hbD z v).symm
        change _ = d.linearEquiv ⟨z.val, fun hz ↦ z.property (hbD hz)⟩ v
        rw [hd]
        have hc₁ : c (1, z) = R / ν z.val := by simp [c]
        apply hsame z.val.proj _ _ _ _ _ v
        change c (1, z) • z.val.snd = (R / ν z.val) • z.val.snd
        rw [hc₁]
    exact (a.compactSupportClass_eq_of_homotopic b H).symm

end AtiyahSinger.RealBundle
