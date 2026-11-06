/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator
public import AtiyahSinger.Analysis.SchwartzEuclideanParameter

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Joint parameter smoothness for atlas PDO pieces

The specified local PDO preserves joint smoothness in a full Euclidean
parameter. Its input cutoff supplies one common compact Schwartz support;
its output frame transitions recover the output in each original bundle
chart. Locally varying ranks are retained. A temporary plateau in the open
parameter proof extends the family and equals one near the chosen point,
so the conclusion concerns the same operator and original parameter family.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

local notation "Y" => EuclideanSpace ℝ (Fin k)
local notation "X" => EuclideanSpace ℝ (Fin n)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original atlas PDO piece preserves joint smoothness in the full parameter. -/
theorem AtlasPseudodifferentialPiece.contMDiffOn_apply_parameter {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m) (u : Y → A.smoothSections)
    (hu : ∀ i : A.Index,
      ContMDiffOn ((𝓘(ℝ, Y)).prod (𝓘(ℝ, X))) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : Y × M ↦ (A.chart i ⟨p.2, (u p.1).val p.2⟩).2)
        (Set.univ ×ˢ (A.chart i).baseSet)) (j : B.Index) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod (𝓘(ℝ, X))) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
      (fun p : Y × M ↦ (B.chart j ⟨p.2, (L.toLinearMap (u p.1)).val p.2⟩).2)
      (Set.univ ×ˢ (B.chart j).baseSet) := by
  classical
  let c := L.chart
  let Vin := EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex))
  let Vout := EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex))
  let f (y : Y) : 𝓢(X, Vin) := L.input.localize L.chart_mem_atlas (u y)
  -- The actual input cutoff supplies a common compact support for the whole family.
  have hf : ContDiff ℝ ∞ (fun p : Y × X ↦ f p.1 p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.2 ∈ tsupport L.input.cutoff
    · have hc := (L.input.support_subset hp).1
      have hframe := (L.input.support_subset hp).2
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) L.chart_mem_atlas) hc
      have hsection : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
          𝓘(ℝ, Fin (A.rank L.input.frameIndex) → ℂ) ∞
          (fun w : Y × M ↦ (A.chart L.input.frameIndex ⟨w.2, (u w.1).val w.2⟩).2)
          (p.1, c.symm p.2) := (hu L.input.frameIndex).contMDiffAt
        ((isOpen_univ.prod (A.chart L.input.frameIndex).open_baseSet).mem_nhds
          ⟨Set.mem_univ p.1, hframe⟩)
      have hpair : ContMDiffAt 𝓘(ℝ, Y × X) ((𝓘(ℝ, Y)).prod (𝓘(ℝ, X))) ∞
          (fun z : Y × X ↦ (z.1, c.symm z.2)) p :=
        contDiffAt_fst.contMDiffAt.prodMk (hchart.comp p contDiffAt_snd.contMDiffAt)
      let e := EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ
      have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp p
        (hsection.comp p hpair)
      have hcutoff : ContDiffAt ℝ ∞ (fun w : Y × X ↦ (L.input.cutoff w.2 : ℂ)) p :=
        ((Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff).comp contDiff_snd).contDiffAt
      apply (hcutoff.smul hcoords.contDiffAt).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt (c.open_target.mem_nhds hc)] with z hz
      change L.input.localizedFunction (u z.1) z.2 = _
      have hz' : z.2 ∈ L.chart.target := hz
      simp [AtlasChartCutoff.localizedFunction, atlasSectionInChart, hz', e, c]
    · apply (contDiffAt_const (c := (0 : Vin))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt
        ((isClosed_tsupport L.input.cutoff).isOpen_compl.mem_nhds hp)] with z hz
      change L.input.localizedFunction (u z.1) z.2 = 0
      simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  have hout : ContDiff ℝ ∞ (fun p : Y × X ↦ L.operator (f p.1) p.2) :=
    contDiff_schwartzOperator_euclidean_of_common_compact_support f hf
      (tsupport L.input.cutoff) L.input.compact_support
      (fun y ↦ (L.input.localizedFunction_properties L.chart_mem_atlas (u y)).2.1) L.operator
  have hcompact : IsCompact (c.symm '' tsupport L.output.cutoff) :=
    L.output.compact_support.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ (L.output.support_subset hz).1))
  -- The original transition columns recover every output frame from the same Schwartz output.
  intro p hp
  have hsnd : ContMDiffAt ((𝓘(ℝ, Y)).prod (𝓘(ℝ, X))) (𝓘(ℝ, X)) ∞
      (Prod.snd : Y × M → M) p := contMDiffAt_snd
  by_cases hx : p.2 ∈ c.symm '' tsupport L.output.cutoff
  · obtain ⟨z, hz, hzx⟩ := hx
    have hzchart := (L.output.support_subset hz).1
    have hxsource : p.2 ∈ c.source := hzx ▸ c.map_target hzchart
    have hxframe : p.2 ∈ (B.chart L.output.frameIndex).baseSet :=
      hzx ▸ (L.output.support_subset hz).2
    have hchart := (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X))
        (n := ∞) L.chart_mem_atlas) hxsource).comp p hsnd
    let e := EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ
    have hvector := (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contMDiffAt
      (hout.comp_contMDiffAt (contMDiffAt_fst.prodMk_space hchart))
    have hcutoff := (Complex.ofRealCLM.contDiff.comp L.output.smooth_cutoff).comp_contMDiffAt
      hchart
    have hsum : ContMDiffAt ((𝓘(ℝ, Y)).prod (𝓘(ℝ, X))) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
        (fun w : Y × M ↦ ∑ i : Fin (B.rank L.output.frameIndex),
          (e (L.operator (f w.1) (c w.2))) i •
            (B.chart j ((B.chart L.output.frameIndex).toPartialEquiv.symm
              (w.2, Pi.single i 1))).2) p := by
      apply contMDiffAt_finsetSum
      intro i _
      have hcoeff := contMDiffAt_pi_space.mp hvector i
      have hcolumn := ((B.contMDiffOn_coordChange L.output.frameIndex j i).contMDiffAt
        (((B.chart L.output.frameIndex).open_baseSet.inter
          (B.chart j).open_baseSet).mem_nhds ⟨hxframe, hp.2⟩)).comp p hsnd
      have hmul : ContDiff ℝ ∞
          (fun v : ℂ × (Fin (B.rank j) → ℂ) ↦ v.1 • v.2) := contDiff_smul
      exact hmul.comp_contMDiffAt (hcoeff.prodMk_space hcolumn)
    have hmul : ContDiff ℝ ∞
        (fun v : ℂ × (Fin (B.rank j) → ℂ) ↦ v.1 • v.2) := contDiff_smul
    have hlocal := hmul.comp_contMDiffAt (hcutoff.prodMk_space hsum)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [continuous_snd.continuousAt (c.open_source.mem_nhds hxsource),
      continuous_snd.continuousAt ((B.chart L.output.frameIndex).open_baseSet.mem_nhds hxframe),
      continuous_snd.continuousAt ((B.chart j).open_baseSet.mem_nhds hp.2)] with w hwc hwi hwj
    change (B.chart j ⟨w.2, L.output.extendedFunction (L.operator (f w.1)) w.2⟩).2 = _
    have hwvalid : w.2 ∈ L.chart.source ∩ (B.chart L.output.frameIndex).baseSet := ⟨hwc, hwi⟩
    simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hwvalid]
    rw [(B.linear j w.2 hwj).map_smul]
    congr 1
    let T := (B.frameLinearEquiv j w.2 hwj).toLinearMap.comp
      (B.frameLinearEquiv L.output.frameIndex w.2 hwi).symm.toLinearMap
    have hexpand := congrArg T ((Pi.basisFun ℂ (Fin (B.rank L.output.frameIndex))).sum_repr
      (e (L.operator (f w.1) (c w.2))))
    simp [T, map_sum, map_smul] at hexpand
    have hcolumn (i : Fin (B.rank L.output.frameIndex)) :
        (B.frameLinearEquiv j w.2 hwj)
            ((B.frameLinearEquiv L.output.frameIndex w.2 hwi).symm (Pi.single i 1)) =
          (B.chart j ((B.chart L.output.frameIndex).toPartialEquiv.symm
            (w.2, Pi.single i 1))).2 := by
      change (B.chart j ⟨w.2, cast (congrArg F
        ((B.chart L.output.frameIndex).proj_symm_apply' hwi))
          ((B.chart L.output.frameIndex).toOpenPartialHomeomorph.symm
            (w.2, Pi.single i 1)).2⟩).2 = _
      have hpoint := TotalSpace.mk_cast (F := Unit) (E := F)
        ((B.chart L.output.frameIndex).proj_symm_apply' (x := Pi.single i 1) hwi)
        ((B.chart L.output.frameIndex).toOpenPartialHomeomorph.symm (w.2, Pi.single i 1)).2
      exact congrArg (fun v : TotalSpace Unit F ↦ (B.chart j v).2) hpoint
    simp only [hcolumn] at hexpand
    change (B.frameLinearEquiv j w.2 hwj)
      ((B.frameLinearEquiv L.output.frameIndex w.2 hwi).symm
        (e (L.operator (f w.1) (c w.2)))) = _
    exact hexpand.symm
  · -- The entire output family is locally zero off the original compact output support.
    have hzero : ∀ᶠ w : Y × M in nhds p,
        (B.chart j ⟨w.2, (L.toLinearMap (u w.1)).val w.2⟩).2 = 0 := by
      filter_upwards [continuous_snd.continuousAt (hcompact.isClosed.isOpen_compl.mem_nhds hx),
        continuous_snd.continuousAt ((B.chart j).open_baseSet.mem_nhds hp.2)] with w hw hwj
      rw [L.toLinearMap_support_properties.1 (u w.1) w.2 hw]
      exact (B.linear j w.2 hwj).map_zero
    exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint smoothness is local in an unchanged parameter chart for the same original atlas PDO. -/
theorem AtlasPseudodifferentialPiece.contMDiffOn_apply_parameter_of_isOpen {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m) (U : Set Y) (hU : IsOpen U)
    (u : Y → A.smoothSections)
    (hu : ∀ i : A.Index,
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : Y × M ↦ (A.chart i ⟨p.2, (u p.1).val p.2⟩).2)
        (U ×ˢ (A.chart i).baseSet)) (j : B.Index) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
      (fun p : Y × M ↦ (B.chart j ⟨p.2, (L.toLinearMap (u p.1)).val p.2⟩).2)
      (U ×ˢ (B.chart j).baseSet) := by
  classical
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
  let v (y : Y) : A.smoothSections := (β y : ℂ) • u y
  -- A proof-local plateau supplies a global family equal to the original one near the point.
  have hv (i : A.Index) :
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun z : Y × M ↦ (A.chart i ⟨z.2, (v z.1).val z.2⟩).2)
        (Set.univ ×ˢ (A.chart i).baseSet) := by
    intro z hz
    by_cases hb : z.1 ∈ tsupport β
    · have huAt := (hu i).contMDiffAt
        ((hU.prod (A.chart i).open_baseSet).mem_nhds ⟨hβsupport hb, hz.2⟩)
      have hβ : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, ℂ) ∞
          (fun w : Y × M ↦ (β w.1 : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.comp β.contDiff).comp_contMDiffAt contMDiffAt_fst
      have hmul : ContDiff ℝ ∞
          (fun q : ℂ × (Fin (A.rank i) → ℂ) ↦ q.1 • q.2) := contDiff_smul
      have hlocal := hmul.comp_contMDiffAt (hβ.prodMk_space huAt)
      apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [continuous_snd.continuousAt ((A.chart i).open_baseSet.mem_nhds hz.2)]
        with w hw
      exact (A.linear i w.2 hw).map_smul (β w.1 : ℂ) ((u w.1).val w.2)
    · have hzero : ∀ᶠ w : Y × M in nhds z,
          (A.chart i ⟨w.2, (v w.1).val w.2⟩).2 = 0 := by
        filter_upwards [continuous_fst.continuousAt
          ((isClosed_tsupport β).isOpen_compl.mem_nhds hb),
          continuous_snd.continuousAt ((A.chart i).open_baseSet.mem_nhds hz.2)] with w hw hwi
        have hbzero : β w.1 = 0 := image_eq_zero_of_notMem_tsupport hw
        have hvzero : v w.1 = 0 := by simp only [v, hbzero, Complex.ofReal_zero, zero_smul]
        rw [hvzero]
        exact (A.linear i w.2 hwi).map_zero
      exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
  have hresult := (L.contMDiffOn_apply_parameter A B v hv j).contMDiffAt
    ((isOpen_univ.prod (B.chart j).open_baseSet).mem_nhds ⟨Set.mem_univ _, hp.2⟩)
  -- Linearity removes the proof-local plateau exactly; the actual operator never truncates it.
  apply (hresult.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [continuous_fst.continuousAt β.eventuallyEq_one] with w hw
  have hw' : β w.1 = 1 := hw
  have hvu : v w.1 = u w.1 := by
    change (β w.1 : ℂ) • u w.1 = u w.1
    rw [hw', Complex.ofReal_one, one_smul]
  exact congrArg (fun s : A.smoothSections ↦
    (B.chart j ⟨w.2, (L.toLinearMap s).val w.2⟩).2) hvu.symm

end AtiyahSinger
