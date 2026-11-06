/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Analysis.SchwartzEuclideanParameter

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The original local PDO acting on smooth parameter families

Public module ID: M0897.

A compactly supported PDO piece preserves joint smoothness in an independent
Euclidean parameter and the base variable. The action is its original input
localization, specified Schwartz operator and output extension. The common
compact support is the original input cutoff; the parameter is never cut off.

This is the local horizontal action used in the principal charts of the
associated-sphere index construction. Descent and the commuting vertical
operator squares remain separate obligations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped ContDiff Manifold SchwartzMap Topology

variable {n k r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

local notation "Y" => EuclideanSpace ℝ (Fin k)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Vin" => EuclideanSpace ℂ (Fin r)
local notation "Vout" => EuclideanSpace ℂ (Fin q)

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same local PDO preserves joint smoothness without truncating its parameter. -/
theorem PseudodifferentialPiece.contMDiffOn_apply_parameter {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (u : Y → smoothSections (n := n) (r := r) E)
    (hu : ∀ (e : Trivialization Vin (π Vin E)), MemTrivializationAtlas e →
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
        (fun p : Y × M ↦ (e ⟨p.2, (u p.1).val p.2⟩).2)
        (Set.univ ×ˢ e.baseSet))
    (e : Trivialization Vout (π Vout F)) (he : MemTrivializationAtlas e) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vout) ∞
      (fun p : Y × M ↦ (e ⟨p.2, (L.toLinearMap (u p.1)).val p.2⟩).2)
      (Set.univ ×ˢ e.baseSet) := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let := he
  let c := L.chart
  let f (y : Y) : 𝓢(X, Vin) := L.input.localize L.chart_mem_atlas (u y)
  -- Original input localization has one fixed compact support for all parameter values.
  have hf : ContDiff ℝ ∞ (fun p : Y × X ↦ f p.1 p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.2 ∈ tsupport L.input.cutoff
    · have hc := (L.input.support_subset hp).1
      have hframe := (L.input.support_subset hp).2
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X))
          (n := ∞) L.chart_mem_atlas) hc
      have hsection : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
          (fun w : Y × M ↦ (L.input.frame ⟨w.2, (u w.1).val w.2⟩).2)
          (p.1, c.symm p.2) := (hu L.input.frame L.input.frame_mem_atlas).contMDiffAt
        ((isOpen_univ.prod L.input.frame.open_baseSet).mem_nhds ⟨Set.mem_univ _, hframe⟩)
      have hpair : ContMDiffAt 𝓘(ℝ, Y × X) ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞
          (fun z : Y × X ↦ (z.1, c.symm z.2)) p :=
        contDiffAt_fst.contMDiffAt.prodMk (hchart.comp p contDiffAt_snd.contMDiffAt)
      have hcoords := hsection.comp p hpair
      have hcutoff : ContDiffAt ℝ ∞ (fun w : Y × X ↦ (L.input.cutoff w.2 : ℂ)) p :=
        ((Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff).comp contDiff_snd).contDiffAt
      apply (hcutoff.smul hcoords.contDiffAt).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt (c.open_target.mem_nhds hc)] with z hz
      change L.input.localizedFunction (u z.1) z.2 =
        (L.input.cutoff z.2 : ℂ) •
          (L.input.frame ⟨c.symm z.2, (u z.1).val (c.symm z.2)⟩).2
      have hz' : z.2 ∈ L.chart.target := hz
      simp only [BundleChartCutoff.localizedFunction, ite_eq_left hz', sectionInChart]
      rfl
    · apply (contDiffAt_const (c := (0 : Vin))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt
        ((isClosed_tsupport L.input.cutoff).isOpen_compl.mem_nhds hp)] with z hz
      change L.input.localizedFunction (u z.1) z.2 = 0
      simp [BundleChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  have hout : ContDiff ℝ ∞ (fun p : Y × X ↦ L.operator (f p.1) p.2) :=
    contDiff_schwartzOperator_euclidean_of_common_compact_support f hf
      (tsupport L.input.cutoff) L.input.compact_support
      (fun y ↦ L.input.tsupport_localizedFunction_subset (u y)) L.operator
  have hcompact : IsCompact (c.symm '' tsupport L.output.cutoff) :=
    L.output.compact_support.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ (L.output.support_subset hz).1))
  -- Output extension uses the original inverse frame and base cutoff in every parameter.
  intro p hp
  have hsnd : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, X) ∞
      (Prod.snd : Y × M → M) p := contMDiffAt_snd
  by_cases hx : p.2 ∈ c.symm '' tsupport L.output.cutoff
  · obtain ⟨z, hz, hzx⟩ := hx
    have hzchart := (L.output.support_subset hz).1
    have hxsource : p.2 ∈ c.source := hzx ▸ c.map_target hzchart
    have hxframe : p.2 ∈ L.output.frame.baseSet := hzx ▸ (L.output.support_subset hz).2
    have hchart := (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X))
        (n := ∞) L.chart_mem_atlas) hxsource).comp p hsnd
    have htransition := ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n)
      L.output.frame e).contMDiffAt
        ((L.output.frame.open_baseSet.inter e.open_baseSet).mem_nhds
          ⟨hxframe, hp.2⟩)).comp p hsnd
    have hvector := hout.comp_contMDiffAt (contMDiffAt_fst.prodMk_space hchart)
    have happly : ContDiff ℝ ∞ (fun p : (Vout →L[ℂ] Vout) × Vout ↦ p.1 p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hcoords := happly.comp_contMDiffAt (htransition.prodMk_space hvector)
    have hcutoff := (Complex.ofRealCLM.contDiff.comp L.output.smooth_cutoff).comp_contMDiffAt
      hchart
    have hmul : ContDiff ℝ ∞ (fun p : ℂ × Vout ↦ p.1 • p.2) := contDiff_smul
    have hlocal := hmul.comp_contMDiffAt (hcutoff.prodMk_space hcoords)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [continuous_snd.continuousAt (c.open_source.mem_nhds hxsource),
      continuous_snd.continuousAt (L.output.frame.open_baseSet.mem_nhds hxframe),
      continuous_snd.continuousAt (e.open_baseSet.mem_nhds hp.2)] with w hwc hwframe hwe
    change (e ⟨w.2, L.output.extendedFunction (L.operator (f w.1)) w.2⟩).2 = _
    have hwc' : w.2 ∈ L.chart.source := hwc
    simp only [BundleChartCutoff.extendedFunction, ite_eq_left hwc']
    change (e.linearEquivAt ℂ w.2 hwe)
      ((L.output.cutoff (c w.2) : ℂ) • L.output.frame.symmL ℂ w.2
        (L.operator (f w.1) (c w.2))) =
      (L.output.cutoff (c w.2) : ℂ) • (L.output.frame.coordChangeL ℂ e w.2)
        (L.operator (f w.1) (c w.2))
    rw [map_smul, L.output.frame.coordChangeL_apply e ⟨hwframe, hwe⟩,
      L.output.frame.symmL_apply hwframe]
    rfl
  · have hzero : ∀ᶠ w : Y × M in nhds p,
        (e ⟨w.2, (L.toLinearMap (u w.1)).val w.2⟩).2 = 0 := by
      filter_upwards [continuous_snd.continuousAt (hcompact.isClosed.isOpen_compl.mem_nhds hx),
        continuous_snd.continuousAt (e.open_baseSet.mem_nhds hp.2)] with w hw hwe
      rw [L.toLinearMap_eq_zero (u w.1) w.2 hw]
      exact (e.linearEquivAt ℂ w.2 hwe).map_zero
    exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint smoothness is local in the unchanged parameter, so actual open charts suffice. -/
theorem PseudodifferentialPiece.contMDiffOn_apply_parameter_of_isOpen {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (U : Set Y) (hU : IsOpen U)
    (u : Y → smoothSections (n := n) (r := r) E)
    (hu : ∀ (e : Trivialization Vin (π Vin E)), MemTrivializationAtlas e →
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
        (fun p : Y × M ↦ (e ⟨p.2, (u p.1).val p.2⟩).2) (U ×ˢ e.baseSet))
    (e : Trivialization Vout (π Vout F)) (he : MemTrivializationAtlas e) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vout) ∞
      (fun p : Y × M ↦ (e ⟨p.2, (L.toLinearMap (u p.1)).val p.2⟩).2)
      (U ×ˢ e.baseSet) := by
  classical
  let := he
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp.1)
  let β : ContDiffBump p.1 :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hβsupport : tsupport β ⊆ U := by
    rw [β.tsupport_eq]
    intro y hy
    apply hball
    exact lt_of_le_of_lt hy (half_lt_self hε)
  let v (y : Y) : smoothSections (n := n) (r := r) E := (β y : ℂ) • u y
  -- A proof-local plateau supplies a global family; it is one near the original parameter.
  have hv : ∀ (d : Trivialization Vin (π Vin E)), MemTrivializationAtlas d →
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
        (fun z : Y × M ↦ (d ⟨z.2, (v z.1).val z.2⟩).2)
        (Set.univ ×ˢ d.baseSet) := by
    intro d hd z hz
    let := hd
    by_cases hb : z.1 ∈ tsupport β
    · have huAt := (hu d hd).contMDiffAt
        ((hU.prod d.open_baseSet).mem_nhds ⟨hβsupport hb, hz.2⟩)
      have hβ : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, ℂ) ∞
          (fun w : Y × M ↦ (β w.1 : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.comp β.contDiff).comp_contMDiffAt contMDiffAt_fst
      have hmul : ContDiff ℝ ∞ (fun p : ℂ × Vin ↦ p.1 • p.2) := contDiff_smul
      have hlocal := hmul.comp_contMDiffAt (hβ.prodMk_space huAt)
      apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [continuous_snd.continuousAt (d.open_baseSet.mem_nhds hz.2)] with w hw
      change (d.linearEquivAt ℂ w.2 hw) ((β w.1 : ℂ) • (u w.1).val w.2) =
        (β w.1 : ℂ) • (d.linearEquivAt ℂ w.2 hw) ((u w.1).val w.2)
      exact map_smul _ _ _
    · have hzero : ∀ᶠ w : Y × M in nhds z,
          (d ⟨w.2, (v w.1).val w.2⟩).2 = 0 := by
        filter_upwards [continuous_fst.continuousAt
          ((isClosed_tsupport β).isOpen_compl.mem_nhds hb),
          continuous_snd.continuousAt (d.open_baseSet.mem_nhds hz.2)] with w hw hwd
        have hbzero : β w.1 = 0 := image_eq_zero_of_notMem_tsupport hw
        have hvzero : v w.1 = 0 := by simp only [v, hbzero, Complex.ofReal_zero, zero_smul]
        rw [hvzero]
        exact (d.linearEquivAt ℂ w.2 hwd).map_zero
      exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
  have hresult := (L.contMDiffOn_apply_parameter v hv e he).contMDiffAt
    ((isOpen_univ.prod e.open_baseSet).mem_nhds ⟨Set.mem_univ _, hp.2⟩)
  -- Linearity preserves the plateau exactly, so the resulting local map is the same L action.
  apply (hresult.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [continuous_fst.continuousAt β.eventuallyEq_one] with w hw
  have hw' : β w.1 = 1 := hw
  have hvu : v w.1 = u w.1 := by
    change (β w.1 : ℂ) • u w.1 = u w.1
    rw [hw', Complex.ofReal_one, one_smul]
  exact congrArg (fun s : smoothSections (n := n) (r := r) E ↦
    (e ⟨w.2, (L.toLinearMap s).val w.2⟩).2) hvu.symm

end AtiyahSinger
