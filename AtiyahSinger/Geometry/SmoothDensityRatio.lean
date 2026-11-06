/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Ratios of positive smooth densities

Public module ID: M1389.

D02/E01: on a Hausdorff second-countable smooth manifold, the unique positive
smooth ratio w = dν/dμ is specified by equality
of Borel measures. It is a pointwise smooth function, not an arbitrary a.e.
representative. Its reciprocal and cocycle laws fix all later transport directions.
Sources: the coordinate density definition, SG III.3.17 and III.5 (5.2).
These elementary comparison statements are project deductions, not numbered SG lemmas.
Compactness is used only for the final uniform bounds. No orientation is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]

variable (μ ν : Measure M)
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hT2 hSC hμ hν

/-- Two positive smooth densities have a unique everywhere positive smooth ratio. -/
theorem existsUnique_smoothDensityRatio :
    ∃! w : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ w ∧
      (∀ x, 0 < w x) ∧ ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := by
  classical
  -- Positive chart densities give full support and local finiteness of the reference measure.
  let : IsLocallyFiniteMeasure μ := by
    constructor
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hcx : c x ∈ c.target := c.map_source hx
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    have hwcont : ContinuousAt w (c x) :=
      hw.continuousOn.continuousAt (c.open_target.mem_nhds hcx)
    have hneigh : c.target ∩ {z | w z < w (c x) + 1} ∈ nhds (c x) :=
      Filter.inter_mem (c.open_target.mem_nhds hcx)
        (hwcont.eventually (gt_mem_nhds (lt_add_one _)))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hneigh
    let U := c ⁻¹' Metric.ball (c x) ε ∩ c.source
    have hUnhds : U ∈ nhds x :=
      Filter.inter_mem ((c.continuousAt hx).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
        (c.open_source.mem_nhds hx)
    refine ⟨U, hUnhds, ?_⟩
    -- The chart pushforward measures the same restricted neighborhood.
    have heq : μ U = ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) (Metric.ball (c x) ε) := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) measurableSet_ball,
        Measure.restrict_apply' c.open_source.measurableSet]
    rw [heq, withDensity_apply _ measurableSet_ball]
    have hbound : (∫⁻ z in Metric.ball (c x) ε, ENNReal.ofReal (w z)
        ∂(volume.restrict c.target)) ≤ ENNReal.ofReal (w (c x) + 1) *
          volume (Metric.ball (c x) ε) := by
      calc
        _ ≤ ∫⁻ _z in Metric.ball (c x) ε, ENNReal.ofReal (w (c x) + 1)
            ∂(volume.restrict c.target) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          exact ENNReal.ofReal_le_ofReal (hball hz).2.le
        _ ≤ _ := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)
  let : μ.IsOpenPosMeasure := by
    constructor
    intro U hU hUne hzero
    obtain ⟨x, hxU⟩ := hUne
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    let A := c '' (c.source ∩ U)
    have hAopen : IsOpen A := c.isOpen_image_source_inter hU
    have hAnon : A.Nonempty := ⟨c x, ⟨x, ⟨hx, hxU⟩, rfl⟩⟩
    have hAsub : A ⊆ c.target := by
      rintro _ ⟨y, hy, rfl⟩
      exact c.map_source hy.1
    have hpre : c ⁻¹' A ∩ c.source ⊆ U := by
      rintro y ⟨⟨z, hz, hzy⟩, hy⟩
      have heq : z = y := c.injOn hz.1 hy hzy
      simpa only [← heq] using hz.2
    have hAnull : ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) A = 0 := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hAopen.measurableSet,
        Measure.restrict_apply' c.open_source.measurableSet]
      exact measure_mono_null hpre hzero
    -- Positivity makes coordinate Lebesgue measure absolutely continuous in the density.
    have hac : volume.restrict c.target ≪ (volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z)) := by
      apply withDensity_absolutelyContinuous'
        (hw.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (ENNReal.ofReal_pos.mpr (hwpos z hz)).ne'
    have hvol := hac hAnull
    rw [Measure.restrict_apply hAopen.measurableSet,
      Set.inter_eq_left.mpr hAsub] at hvol
    exact hAopen.measure_ne_zero volume hAnon hvol
  -- Pushforward commutes with a density pulled back from the target.
  have hmapDensity (θ : Measure M) (f : M → EuclideanSpace ℝ (Fin n))
      (g : EuclideanSpace ℝ (Fin n) → ENNReal) (hf : AEMeasurable f θ)
      (hg : AEMeasurable g (Measure.map f θ)) :
      (Measure.map f θ).withDensity g =
        Measure.map f (θ.withDensity (fun x ↦ g (f x))) := by
    ext A hA
    rw [withDensity_apply _ hA,
      Measure.map_apply_of_aemeasurable
        (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hA,
      withDensity_apply₀ _ (hf.nullMeasurable hA),
      ← lintegral_indicator hA, ← lintegral_indicator₀ (hf.nullMeasurable hA)]
    rw [lintegral_map' (hg.indicator hA) hf]
    congr 1
  -- In a fixed chart, both measures use the same Lebesgue measure, so their quotient is local.
  choose a ha using fun x : M ↦
    hμ.exists_smooth_density (chartAt (EuclideanSpace ℝ (Fin n)) x) (chart_mem_atlas _ x)
  choose b hb using fun x : M ↦
    hν.exists_smooth_density (chartAt (EuclideanSpace ℝ (Fin n)) x) (chart_mem_atlas _ x)
  let U (x : M) := (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  let q (x y : M) := b x (chartAt (EuclideanSpace ℝ (Fin n)) x y) /
    a x (chartAt (EuclideanSpace ℝ (Fin n)) x y)
  have hqpos (x y : M) (hy : y ∈ U x) : 0 < q x y :=
    div_pos ((hb x).2.1 _ ((chartAt _ x).map_source hy))
      ((ha x).2.1 _ ((chartAt _ x).map_source hy))
  have hqsmooth (x : M) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ)
      ∞ (q x) (U x) := by
    exact ((hb x).1.div (ha x).1 (fun z hz ↦ ((ha x).2.1 z hz).ne')).contMDiffOn.comp
      contMDiffOn_chart (chartAt _ x).mapsTo
  have hqmeasure (x : M) : ν.restrict (U x) =
      (μ.restrict (U x)).withDensity (fun y ↦ ENNReal.ofReal (q x y)) := by
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let r (z : EuclideanSpace ℝ (Fin n)) := b x z / a x z
    have hc : AEMeasurable c (μ.restrict (U x)) :=
      c.continuousOn.aemeasurable c.open_source.measurableSet
    have hr : AEMeasurable (fun z ↦ ENNReal.ofReal (r z)) (volume.restrict c.target) :=
      (((hb x).1.div (ha x).1 (fun z hz ↦ ((ha x).2.1 z hz).ne')).continuousOn.aemeasurable
        c.open_target.measurableSet).ennreal_ofReal
    have heq : Measure.map c (ν.restrict (U x)) =
        Measure.map c ((μ.restrict (U x)).withDensity
          (fun y ↦ ENNReal.ofReal (q x y))) := by
      rw [← hmapDensity _ c (fun z ↦ ENNReal.ofReal (r z)) hc
        (by rw [(ha x).2.2]; exact hr.mono_ac (withDensity_absolutelyContinuous _ _)),
        (ha x).2.2, (hb x).2.2]
      rw [← withDensity_mul₀
        ((ha x).1.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal hr]
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      change ENNReal.ofReal (b x z) = ENNReal.ofReal (a x z) * ENNReal.ofReal (r z)
      rw [← ENNReal.ofReal_mul ((ha x).2.1 z hz).le]
      congr 1
      dsimp [r]
      field_simp [((ha x).2.1 z hz).ne']
    -- Pull back the equality with the same inverse chart, where both measures are supported.
    have hsymm : AEMeasurable c.symm (Measure.map c (ν.restrict (U x))) := by
      rw [(hb x).2.2]
      exact (c.symm.continuousOn.aemeasurable c.open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    have hνpull : Measure.map c.symm (Measure.map c (ν.restrict (U x))) =
        ν.restrict (U x) := by
      rw [hsymm.map_map_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet)]
      calc
        _ = Measure.map id (ν.restrict (U x)) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem c.open_source.measurableSet] with y hy
          exact c.left_inv hy
        _ = _ := Measure.map_id
    have hμpull : Measure.map c.symm (Measure.map c
        ((μ.restrict (U x)).withDensity (fun y ↦ ENNReal.ofReal (q x y)))) =
          (μ.restrict (U x)).withDensity (fun y ↦ ENNReal.ofReal (q x y)) := by
      have hsymm' := heq ▸ hsymm
      rw [hsymm'.map_map_of_aemeasurable
        (hc.mono_ac (withDensity_absolutelyContinuous _ _))]
      calc
        _ = Measure.map id ((μ.restrict (U x)).withDensity
            (fun y ↦ ENNReal.ofReal (q x y))) := by
          apply Measure.map_congr
          filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
            (ae_restrict_mem c.open_source.measurableSet)] with y hy
          exact c.left_inv hy
        _ = _ := Measure.map_id
    exact hνpull.symm.trans ((congrArg (Measure.map c.symm) heq).trans hμpull)
  -- Equality of local weighted measures identifies continuous positive weights pointwise.
  have huniq (s : Set M) (hs : IsOpen s) (f g : M → ℝ)
      (hf : ContinuousOn f s) (hg : ContinuousOn g s)
      (hfpos : ∀ y ∈ s, 0 < f y) (hgpos : ∀ y ∈ s, 0 < g y)
      (heq : (μ.restrict s).withDensity (fun y ↦ ENNReal.ofReal (f y)) =
        (μ.restrict s).withDensity (fun y ↦ ENNReal.ofReal (g y))) :
      Set.EqOn f g s := by
    have hae := (withDensity_eq_iff_of_sigmaFinite
      (hf.aemeasurable hs.measurableSet).ennreal_ofReal
      (hg.aemeasurable hs.measurableSet).ennreal_ofReal).mp heq
    apply Measure.eqOn_open_of_ae_eq (μ := μ) _ hs hf hg
    filter_upwards [hae, ae_restrict_mem hs.measurableSet] with y hy hys
    have hr := congrArg ENNReal.toReal hy
    simpa only [ENNReal.toReal_ofReal (hfpos y hys).le,
      ENNReal.toReal_ofReal (hgpos y hys).le] using hr
  have hqrestrict (x : M) : ν.restrict (U x) =
      (μ.withDensity (fun y ↦ ENNReal.ofReal (q x y))).restrict (U x) := by
    rw [restrict_withDensity (chartAt _ x).open_source.measurableSet]
    exact hqmeasure x
  have hcompat (x y : M) : Set.EqOn (q x) (q y) (U x ∩ U y) := by
    apply huniq _ ((chartAt _ x).open_source.inter (chartAt _ y).open_source)
      _ _ ((hqsmooth x).continuousOn.mono Set.inter_subset_left)
      ((hqsmooth y).continuousOn.mono Set.inter_subset_right)
      (fun z hz ↦ hqpos x z hz.1) (fun z hz ↦ hqpos y z hz.2)
    have hx := Measure.restrict_congr_mono (s := U x ∩ U y) Set.inter_subset_left (hqrestrict x)
    have hy := Measure.restrict_congr_mono (s := U x ∩ U y) Set.inter_subset_right (hqrestrict y)
    have heq := hx.symm.trans hy
    simpa only [U, restrict_withDensity
      ((chartAt _ x).open_source.inter (chartAt _ y).open_source).measurableSet] using heq
  let w (x : M) := q x x
  have hwlocal (x : M) : Set.EqOn w (q x) (U x) := by
    intro y hy
    exact (hcompat x y ⟨hy, mem_chart_source _ y⟩).symm
  have hw : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ w := by
    apply contMDiff_of_locally_contMDiffOn
    intro x
    exact ⟨U x, (chartAt _ x).open_source, mem_chart_source _ x,
      (hqsmooth x).congr (hwlocal x)⟩
  have hwpos (x : M) : 0 < w x := hqpos x x (mem_chart_source _ x)
  have hwmeasure : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := by
    -- Second countability makes the open chart cover a countable cover for measure extensionality.
    obtain ⟨S, hS, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable U
      (fun x ↦ (chartAt _ x).open_source)
    have hcover' : ⋃ x ∈ S, U x = Set.univ := by
      rw [hcover]
      exact Set.eq_univ_of_forall (fun x ↦ Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
    apply Measure.ext_of_biUnion_eq_univ hS hcover'
    intro x hx
    rw [restrict_withDensity (chartAt _ x).open_source.measurableSet, hqmeasure x]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (chartAt _ x).open_source.measurableSet] with y hy
    exact congrArg ENNReal.ofReal ((hwlocal x hy).symm)
  refine ⟨w, ⟨hw, hwpos, hwmeasure⟩, ?_⟩
  intro v hv
  have heq : (μ.restrict Set.univ).withDensity (fun y ↦ ENNReal.ofReal (v y)) =
      (μ.restrict Set.univ).withDensity (fun y ↦ ENNReal.ofReal (w y)) := by
    simpa only [Measure.restrict_univ] using hv.2.2.symm.trans hwmeasure
  exact funext (fun x ↦ huniq Set.univ isOpen_univ v w hv.1.continuous.continuousOn
    hw.continuous.continuousOn (fun y _ ↦ hv.2.1 y) (fun y _ ↦ hwpos y) heq (Set.mem_univ x))

/-- The canonical positive smooth function dν/dμ. -/
def smoothDensityRatio : M → ℝ :=
  Classical.choose (existsUnique_smoothDensityRatio (n := n) μ ν).exists

/-- The canonical ratio is smooth at every base point. -/
theorem contMDiff_smoothDensityRatio :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (smoothDensityRatio (n := n) μ ν) := by
  /- Take the smoothness component of the unique ratio's witness property.
  This is a global smooth representative, rather than a Radon--Nikodym a.e. class. -/
  exact (Classical.choose_spec (existsUnique_smoothDensityRatio (n := n) μ ν).exists).1

/-- The canonical ratio is strictly positive, including at every possible test point. -/
theorem smoothDensityRatio_pos (x : M) : 0 < smoothDensityRatio (n := n) μ ν x := by
  /- The defining existence theorem selects a function positive at every point.
  Extract that component before taking reciprocals; no nonzero condition is inferred a.e. -/
  exact (Classical.choose_spec (existsUnique_smoothDensityRatio (n := n) μ ν).exists).2.1 x

/-- The ratio direction is fixed by dν = (dν/dμ) dμ. -/
theorem withDensity_smoothDensityRatio :
    μ.withDensity (fun x ↦ ENNReal.ofReal (smoothDensityRatio (n := n) μ ν x)) = ν := by
  /- Use the measure identity in the chosen ratio's specification and reverse it.
  Keeping this orientation explicit prevents reversing the weights in later kernels. -/
  exact (Classical.choose_spec (existsUnique_smoothDensityRatio (n := n) μ ν).exists).2.2.symm

/-- A proposed smooth positive density quotient agrees with the canonical ratio pointwise. -/
theorem smoothDensityRatio_eq (w : M → ℝ)
    (hw : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ w)
    (hwpos : ∀ x, 0 < w x)
    (hmeasure : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) :
    smoothDensityRatio (n := n) μ ν = w := by
  /- Both functions satisfy all three parts of the unique-ratio specification.
  Apply its uniqueness clause; positivity of μ on open sets upgrades the result
  to pointwise equality, which is needed by the actual test multiplication maps. -/
  exact (existsUnique_smoothDensityRatio (n := n) μ ν).unique
    (Classical.choose_spec (existsUnique_smoothDensityRatio (n := n) μ ν).exists)
    ⟨hw, hwpos, hmeasure⟩

omit hν in
/-- A density divided by itself is the constant one function. -/
theorem smoothDensityRatio_self :
    smoothDensityRatio (n := n) μ μ = fun _ ↦ 1 := by
  /- The constant one function is smooth and positive, and withDensity one
  leaves μ unchanged. The preceding uniqueness theorem identifies this candidate. -/
  apply smoothDensityRatio_eq (n := n) μ μ (fun _ ↦ 1) contMDiff_const
    (fun _ ↦ zero_lt_one)
  simp

/-- Reversing the two densities takes the reciprocal of their pointwise ratio. -/
theorem smoothDensityRatio_swap (x : M) :
    smoothDensityRatio (n := n) ν μ x = (smoothDensityRatio (n := n) μ ν x)⁻¹ := by
  /- The reciprocal is smooth because the original ratio never vanishes.
  The withDensity composition law cancels the positive weights and recovers μ.
  Apply uniqueness to the reversed density pair and evaluate at x. -/
  have hpos (y : M) := smoothDensityRatio_pos (n := n) μ ν y
  have hsmooth := contMDiff_smoothDensityRatio (n := n) μ ν
  have heq := smoothDensityRatio_eq (n := n) ν μ
    (fun y ↦ (smoothDensityRatio (n := n) μ ν y)⁻¹)
    (hsmooth.inv₀ (fun y ↦ (hpos y).ne')) (fun y ↦ inv_pos.mpr (hpos y))
  apply congrFun (heq ?_) x
  -- The two strictly positive density weights cancel as measures, without finite-mass hypotheses.
  conv_rhs =>
    arg 1
    rw [← withDensity_smoothDensityRatio (n := n) μ ν]
  have hweight : (fun y ↦ ENNReal.ofReal ((smoothDensityRatio (n := n) μ ν y)⁻¹)) =
      fun y ↦ (ENNReal.ofReal (smoothDensityRatio (n := n) μ ν y))⁻¹ :=
    funext (fun y ↦ ENNReal.ofReal_inv_of_pos (hpos y))
  rw [hweight]
  exact (withDensity_inv_same hsmooth.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun y ↦ (ENNReal.ofReal_pos.mpr (hpos y)).ne'))
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_ne_top))).symm

/-- Density ratios compose pointwise; the intermediate density cancels. -/
theorem smoothDensityRatio_mul (κ : Measure M) [IsSmoothPositiveMeasure (n := n) κ]
    (x : M) :
    smoothDensityRatio (n := n) μ κ x =
      smoothDensityRatio (n := n) μ ν x * smoothDensityRatio (n := n) ν κ x := by
  /- Multiply the two smooth positive functions and compose their withDensity
  formulas. Uniqueness identifies the product with dκ/dμ; no finite total mass
  is needed for this measure identity or for the pointwise conclusion. -/
  have hμν := contMDiff_smoothDensityRatio (n := n) μ ν
  have hνκ := contMDiff_smoothDensityRatio (n := n) ν κ
  have heq := smoothDensityRatio_eq (n := n) μ κ
    (fun y ↦ smoothDensityRatio (n := n) μ ν y * smoothDensityRatio (n := n) ν κ y)
    (hμν.smul hνκ) (fun y ↦ mul_pos (smoothDensityRatio_pos (n := n) μ ν y)
      (smoothDensityRatio_pos (n := n) ν κ y))
  apply congrFun (heq ?_) x
  -- Composing the two specified measure changes fixes the order of the quotient factors.
  have hweight : (fun y ↦ ENNReal.ofReal (smoothDensityRatio (n := n) μ ν y *
      smoothDensityRatio (n := n) ν κ y)) =
      (fun y ↦ ENNReal.ofReal (smoothDensityRatio (n := n) μ ν y)) *
        (fun y ↦ ENNReal.ofReal (smoothDensityRatio (n := n) ν κ y)) :=
    funext (fun y ↦ ENNReal.ofReal_mul (smoothDensityRatio_pos (n := n) μ ν y).le)
  rw [hweight, withDensity_mul μ hμν.continuous.measurable.ennreal_ofReal
    hνκ.continuous.measurable.ennreal_ofReal, withDensity_smoothDensityRatio,
    withDensity_smoothDensityRatio]

/-- Complex-valued multiplication uses the real positive ratio with its ordinary cast. -/
theorem contMDiff_complex_smoothDensityRatio :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ)) := by
  /- Compose the real-smooth ratio with the real-linear inclusion of ℝ into ℂ.
  This does not introduce a conjugation or a choice of a complex square root. -/
  exact Complex.ofRealCLM.contMDiff.comp (contMDiff_smoothDensityRatio (n := n) μ ν)

/-- The positive square root of the density ratio is smooth, also as a complex scalar. -/
theorem contMDiff_complex_sqrt_smoothDensityRatio :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ (Real.sqrt (smoothDensityRatio (n := n) μ ν x) : ℂ)) := by
  /- The real square-root function is smooth on the positive half-line.
  Strict pointwise positivity permits composition, followed by the real-linear
  complex inclusion. No regularity at zero is being asserted. -/
  have hsqrt : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ Real.sqrt (smoothDensityRatio (n := n) μ ν x)) := by
    intro x
    exact (Real.contDiffAt_sqrt (smoothDensityRatio_pos (n := n) μ ν x).ne').contMDiffAt.comp x
      (contMDiff_smoothDensityRatio (n := n) μ ν x)
  exact Complex.ofRealCLM.contMDiff.comp hsqrt

/-- Integration changes by the same positive scalar density ratio. -/
theorem integral_smoothDensityRatio (f : M → ℂ) :
    (∫ x, f x ∂ν) = ∫ x, (smoothDensityRatio (n := n) μ ν x : ℂ) * f x ∂μ := by
  /- Rewrite ν using its withDensity formula. The nonnegative real density
  is measurable and finite everywhere; the Bochner integral withDensity formula
  replaces it by real scalar multiplication, equal here to complex multiplication.
  The totalized identity holds also when both sides are nonintegrable integrals. -/
  conv_lhs => rw [← withDensity_smoothDensityRatio (n := n) μ ν]
  rw [integral_withDensity_eq_integral_toReal_smul
    (contMDiff_smoothDensityRatio (n := n) μ ν).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (smoothDensityRatio_pos (n := n) μ ν x).le]
    rfl)

/-- On a compact base a positive smooth ratio is uniformly bounded away from zero and infinity. -/
theorem exists_smoothDensityRatio_bounds [CompactSpace M] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c ≤ smoothDensityRatio (n := n) μ ν x ∧
      smoothDensityRatio (n := n) μ ν x ≤ C := by
  /- On a nonempty compact base continuity gives an attained minimum and maximum;
  pointwise positivity makes both values positive. On the empty base choose
  c = C = 1, since the pointwise requirement is vacuous. -/
  classical
  by_cases hMne : Nonempty M
  · let := hMne
    -- The extrema are values of the same everywhere-positive canonical ratio.
    have hc := (contMDiff_smoothDensityRatio (n := n) μ ν).continuous
    obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
    obtain ⟨y, _, hy⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
    exact ⟨smoothDensityRatio (n := n) μ ν x, smoothDensityRatio (n := n) μ ν y,
      smoothDensityRatio_pos (n := n) μ ν x, smoothDensityRatio_pos (n := n) μ ν y,
      fun z ↦ ⟨hx (Set.mem_univ z), hy (Set.mem_univ z)⟩⟩
  · -- On the empty base the pointwise bounds are vacuous.
    exact ⟨1, 1, zero_lt_one, zero_lt_one, fun x ↦ (hMne ⟨x⟩).elim⟩

end AtiyahSinger
