/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Smooth Hermitian metrics and the integral pairing of sections

Public module ID: M1274.

D02: smoothness of a Hermitian metric means that its Gram matrix in every smooth
complex frame has real-smooth entries. The fiber norms and topologies here are those
of the specified inner product spaces, so there is no second incompatible topology.

The metric class is defined over a charted base. It requires the original smooth
bundle transitions and Gram coefficients. Standard smooth-manifold clients supply
`IsManifold` separately; the class does not certify compatibility of the base charts.

A smooth positive measure is locally a strictly positive smooth density times Lebesgue
measure. This measure formulation also works on a nonorientable manifold. On a compact
base the integral pairing of smooth sections is finite and positive definite.
On a Hausdorff second-countable smooth base, a locally finite sum of weighted
chart measures constructs a positive smooth measure.

Sources: Spin Geometry III.2 and III.5, especially pp. 194–195. No orientation,
connection, spin structure, or Fredholm conclusion is part of either definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]

/-- A positive smooth density, expressed as its Borel measure in each manifold chart. -/
class IsSmoothPositiveMeasure (μ : Measure M) : Prop where
  /-- In every chart the measure has a strictly positive real-smooth density. -/
  exists_smooth_density :
    ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
        ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
          ContDiffOn ℝ ∞ w c.target ∧ (∀ z ∈ c.target, 0 < w z) ∧
            Measure.map c (μ.restrict c.source) =
              (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z))

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

set_option maxRecDepth 3000 in
-- Allow nested chart and measure calculations in this proof.
set_option maxHeartbeats 1200000 in
-- Allow the countable bump sum and change-of-variables proof to elaborate.
open Set Function in
open scoped Topology in
/-- A Hausdorff second-countable smooth manifold without boundary admits a positive
smooth density. -/
theorem exists_smoothPositiveMeasure :
    ∃ μ : Measure M, IsSmoothPositiveMeasure (n := n) μ := by
  /- Choose a countable locally finite smooth bump covering subordinate to the
  original coordinate charts. Sum the coordinate Lebesgue measures weighted
  by these bumps. In an arbitrary original chart, change variables on each
  overlap using the absolute inverse-coordinate Jacobian. Local finiteness
  gives smoothness of the resulting density and a covering bump gives strict
  positivity. The actual measure equality follows by nonnegative summation;
  no orientation, compactness, or positive-dimension assumption is needed. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  -- Choose compactly supported smooth bumps in the original chart domains.
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace V M
  obtain ⟨ι, φ, hφ⟩ := SmoothBumpCovering.exists_isSubordinate I isClosed_univ
    (U := fun x : M ↦ (chartAt V x).source)
    (fun x _ ↦ (chartAt V x).open_source.mem_nhds (mem_chart_source V x))
  -- Local finiteness on the sigma-compact base makes the index set countable.
  let : Encodable ι := φ.locallyFinite.encodable
    (fun i ↦ ⟨φ.c i, (φ i).c_mem_support⟩)
  -- Sum the actual weighted coordinate Lebesgue measures on the original base.
  let d (i : ι) := chartAt V (φ.c i)
  let a (i : ι) (z : V) := ENNReal.ofReal (φ i ((d i).symm z))
  let ν (i : ι) : Measure V := (volume.restrict (d i).target).withDensity (a i)
  let μi (i : ι) : Measure M := Measure.map (d i).symm (ν i)
  refine ⟨Measure.sum μi, ⟨?_⟩⟩
  intro c hc
  have hcM := contMDiffOn_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  have hcS := contMDiffOn_symm_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  let t (i : ι) : OpenPartialHomeomorph V V := c.symm.trans (d i)
  have ht (i : ι) : ContDiffOn ℝ ∞ (t i) (t i).source := by
    apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    have hcs := (hcS y hy.1).contMDiffAt (c.open_target.mem_nhds hy.1)
    have hd := (contMDiffOn_chart (I := I) (n := (∞ : ℕ∞ω)) (x := φ.c i)
      _ hy.2).contMDiffAt ((d i).open_source.mem_nhds hy.2)
    exact (hd.comp y hcs).contMDiffWithinAt
  have hts (i : ι) : ContDiffOn ℝ ∞ (t i).symm (t i).target := by
    apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    have hds := (contMDiffOn_chart_symm (I := I) (n := (∞ : ℕ∞ω)) (x := φ.c i)
      y hy.1).contMDiffAt ((d i).open_target.mem_nhds hy.1)
    have hcs := (hcM _ hy.2).contMDiffAt (c.open_source.mem_nhds hy.2)
    exact (hcs.comp y hds).contMDiffWithinAt
  -- The inverse coordinate identity makes each overlap Jacobian nonzero.
  have hdet (i : ι) (y : V) (hy : y ∈ (t i).source) :
      (fderiv ℝ (t i) y).det ≠ 0 := by
    have hf := ((ht i) y hy).contDiffAt ((t i).open_source.mem_nhds hy)
    have hg := ((hts i) ((t i) y) ((t i).map_source hy)).contDiffAt
      ((t i).open_target.mem_nhds ((t i).map_source hy))
    have hinv : (fderiv ℝ (t i).symm ((t i) y)).comp (fderiv ℝ (t i) y) =
        ContinuousLinearMap.id ℝ V := by
      have hh := (hg.differentiableAt (by simp)).hasFDerivAt.comp y
        (hf.differentiableAt (by simp)).hasFDerivAt
      have hid : HasFDerivAt (fun z : V ↦ z)
          ((fderiv ℝ (t i).symm ((t i) y)).comp (fderiv ℝ (t i) y)) y := by
        apply hh.congr_of_eventuallyEq
        filter_upwards [(t i).open_source.mem_nhds hy] with z hz
        exact ((t i).left_inv hz).symm
      exact hid.unique (hasFDerivAt_id y)
    have hd := congrArg ContinuousLinearMap.det hinv
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
    exact right_ne_zero_of_mul_eq_one hd
  let q (i : ι) (y : V) := |(fderiv ℝ (t i) y).det| * φ i (c.symm y)
  have hqnonneg (i : ι) (y : V) : 0 ≤ q i y :=
    mul_nonneg (abs_nonneg _) (φ i).nonneg
  -- The bump support stays inside its chart; each local density extends smoothly by zero.
  have hqsmooth (i : ι) : ContDiffOn ℝ ∞ (q i) c.target := by
    intro y hy
    by_cases hs : c.symm y ∈ tsupport (φ i)
    · have hyt : y ∈ (t i).source := ⟨hy, hφ i hs⟩
      have hf := ((ht i) y hyt).contDiffAt ((t i).open_source.mem_nhds hyt)
      have hfd := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
      have hds : ContDiffAt ℝ ∞ (fun z ↦ (fderiv ℝ (t i) z).det) y := by
        let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
        apply ContDiffAt.sum
        intro σ hσ
        apply ContDiffAt.mul contDiffAt_const
        apply contDiffAt_prod
        intro i hi
        simp only [LinearMap.toMatrix_apply]
        exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp y
          (hfd.clm_apply contDiffAt_const))
      have hφsmooth : ContDiffAt ℝ ∞ (fun z ↦ φ i (c.symm z)) y := by
        apply contMDiffAt_iff_contDiffAt.mp
        exact (φ i).contMDiff.contMDiffAt.comp y
          ((hcS y hy).contMDiffAt (c.open_target.mem_nhds hy))
      exact ((hds.abs (hdet i y hyt)).mul hφsmooth).contDiffWithinAt
    · have he : (fun z ↦ φ i (c.symm z)) =ᶠ[𝓝 y] 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hs).comp_tendsto
          ((c.continuousOn_symm y hy).continuousAt (c.open_target.mem_nhds hy))
      apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with z hz
      simp [q, hz]
  let w (y : V) := ∑ᶠ i, q i y
  -- One bump equals one at the point, so the locally finite density sum is positive.
  have hwpos (y : V) (hy : y ∈ c.target) : 0 < w y := by
    let j := φ.ind (c.symm y) (mem_univ _)
    have hj : φ j (c.symm y) = 1 := (φ.eventuallyEq_one _ (mem_univ _)).eq_of_nhds
    have hfin : (support (fun i ↦ q i y)).Finite :=
      (φ.point_finite (c.symm y)).subset (fun i hi ↦ right_ne_zero_of_mul hi)
    dsimp only [w]
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _]
    · apply Finset.sum_pos' (fun i hi ↦ hqnonneg i y)
      have hyt : y ∈ (t j).source :=
        ⟨hy, hφ j (subset_closure (by simp [hj]))⟩
      have hjq : 0 < q j y := by
        dsimp [q]
        rw [hj, mul_one]
        exact abs_pos.mpr (hdet j y hyt)
      exact ⟨j, hfin.mem_toFinset.mpr hjq.ne', hjq⟩
    · exact fun i hi ↦ hfin.mem_toFinset.mpr hi
  -- On a neighborhood only finitely many bumps contribute, making their sum smooth.
  have hwsmooth : ContDiffOn ℝ ∞ w c.target := by
    intro y hy
    obtain ⟨U, hUy, hUfinite⟩ := φ.locallyFinite (c.symm y)
    have hUpre : ∀ᶠ z in 𝓝 y, c.symm z ∈ U :=
      ((c.continuousOn_symm y hy).continuousAt (c.open_target.mem_nhds hy)).tendsto hUy
    have heq : w =ᶠ[𝓝 y] fun z ↦ ∑ i ∈ hUfinite.toFinset, q i z := by
      filter_upwards [hUpre] with z hz
      apply finsum_eq_sum_of_support_subset
      intro i hi
      exact hUfinite.mem_toFinset.mpr ⟨c.symm z, right_ne_zero_of_mul hi, hz⟩
    exact ((ContDiffAt.sum fun i hi ↦
      (hqsmooth i y hy).contDiffAt (c.open_target.mem_nhds hy)).congr_of_eventuallyEq
      heq).contDiffWithinAt
  refine ⟨w, hwsmooth, hwpos, ?_⟩
  -- A single supported coordinate measure has the expected Jacobian density in c.
  have hqmeasure (i : ι) : Measure.map c ((μi i).restrict c.source) =
      (volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal (q i y)) := by
    ext A hA
    have hpre : MeasurableSet (c ⁻¹' A ∩ c.source) := by
      simpa only [Set.domRestrict_eq, Set.preimage_comp,
        Set.image_preimage_eq_inter_range, Subtype.range_coe] using
        c.open_source.measurableSet.subtype_image
          (hA.preimage c.continuousOn.domRestrict.measurable)
    let A₀ := A ∩ (t i).source
    have hA₀ : MeasurableSet A₀ := hA.inter (t i).open_source.measurableSet
    let B := t i '' A₀
    have hder (y : V) (hy : y ∈ A₀) :
        HasFDerivWithinAt (t i) (fderiv ℝ (t i) y) A₀ y :=
      (((ht i) y hy.2).contDiffAt ((t i).open_source.mem_nhds hy.2)
        |>.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have hB : MeasurableSet B := measurable_image_of_fderivWithin hA₀ hder
      ((t i).injOn.mono Set.inter_subset_right)
    have hset : (d i).symm ⁻¹' (c ⁻¹' A ∩ c.source) ∩ (d i).target = B := by
      ext z
      constructor
      · rintro ⟨⟨hzA, hzc⟩, hzd⟩
        refine ⟨c ((d i).symm z), ⟨hzA, ?_⟩, ?_⟩
        · refine ⟨c.map_source hzc, ?_⟩
          change c.symm (c ((d i).symm z)) ∈ (d i).source
          rw [c.left_inv hzc]
          exact (d i).map_target hzd
        · change d i (c.symm (c ((d i).symm z))) = z
          rw [c.left_inv hzc, (d i).right_inv hzd]
      · rintro ⟨y, hy, rfl⟩
        have hdy : (d i).symm (t i y) = c.symm y := (d i).left_inv hy.2.2
        refine ⟨⟨?_, ?_⟩, ((t i).map_source hy.2).1⟩
        · change c ((d i).symm (t i y)) ∈ A
          rw [hdy, c.right_inv hy.2.1]
          exact hy.1
        · rw [hdy]
          exact c.map_target hy.2.1
    have hdmeas : AEMeasurable (d i).symm (ν i) :=
      ((d i).continuousOn_symm.aemeasurable (d i).open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [Measure.map_apply_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet) hA,
      Measure.restrict_apply' c.open_source.measurableSet]
    change (Measure.map (d i).symm (ν i)) (c ⁻¹' A ∩ c.source) = _
    rw [Measure.map_apply_of_aemeasurable hdmeas hpre]
    have hleft : (ν i) ((d i).symm ⁻¹' (c ⁻¹' A ∩ c.source)) =
        ∫⁻ y in B, a i y ∂volume := by
      change ((volume.restrict (d i).target).withDensity (a i)) _ = _
      rw [withDensity_apply', Measure.restrict_restrict'
        (d i).open_target.measurableSet, hset]
    rw [hleft, withDensity_apply _ hA, Measure.restrict_restrict hA]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA₀ hder
      ((t i).injOn.mono Set.inter_subset_right)]
    calc
      (∫⁻ y in A₀, ENNReal.ofReal |(fderiv ℝ (t i) y).det| * a i (t i y) ∂volume) =
          ∫⁻ y in A₀, ENNReal.ofReal (q i y) ∂volume := by
        apply setLIntegral_congr_fun hA₀
        intro y hy
        dsimp only [a, q]
        rw [show (d i).symm (t i y) = c.symm y from (d i).left_inv hy.2.2,
          ENNReal.ofReal_mul (abs_nonneg _)]
      _ = ∫⁻ y in A ∩ c.target, ENNReal.ofReal (q i y) ∂volume := by
        rw [← lintegral_indicator hA₀,
          ← lintegral_indicator (hA.inter c.open_target.measurableSet)]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ A₀
        · rw [Set.indicator_of_mem hy,
            Set.indicator_of_mem (show y ∈ A ∩ c.target from ⟨hy.1, hy.2.1⟩)]
        · rw [Set.indicator_of_notMem hy]
          by_cases hyc : y ∈ A ∩ c.target
          · rw [Set.indicator_of_mem hyc]
            have hz : φ i (c.symm y) = 0 := by
              by_contra hn
              exact hy ⟨hyc.1, hyc.2, hφ i (subset_closure hn)⟩
            simp [q, hz]
          · rw [Set.indicator_of_notMem hyc]
  -- Nonnegative summation agrees with the pointwise finite real density sum.
  have hsum (y : V) : ENNReal.ofReal (w y) = ∑' i, ENNReal.ofReal (q i y) := by
    have hfin : (support (fun i ↦ q i y)).Finite :=
      (φ.point_finite (c.symm y)).subset (fun i hi ↦ right_ne_zero_of_mul hi)
    dsimp only [w]
    rw [finsum_eq_sum_of_support_subset (fun i ↦ q i y)
      (s := hfin.toFinset) (fun i hi ↦ hfin.mem_toFinset.mpr hi),
      ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ hqnonneg i y)]
    symm
    apply tsum_eq_sum
    intro i hi
    have hz : q i y = 0 := by
      by_contra hn
      exact hi (hfin.mem_toFinset.mpr hn)
    simp [hz]
  have hcm := c.continuousOn.aemeasurable (μ := Measure.sum μi)
    c.open_source.measurableSet
  rw [Measure.restrict_sum _ c.open_source.measurableSet] at hcm ⊢
  rw [Measure.map_sum hcm]
  simp_rw [hqmeasure]
  ext A hA
  rw [Measure.sum_apply _ hA, withDensity_apply _ hA]
  simp_rw [withDensity_apply _ hA]
  rw [show (fun y ↦ ENNReal.ofReal (w y)) = (fun y ↦ ∑' i, ENNReal.ofReal (q i y))
    from funext hsum]
  symm
  apply lintegral_tsum
  intro i
  exact ((hqsmooth i).continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal.restrict


variable (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hμ in
set_option linter.unusedSectionVars false in
/-- A smooth positive density has finite total mass on a compact manifold. -/
theorem isFiniteMeasure_of_smoothPositiveMeasure [CompactSpace M] : IsFiniteMeasure μ := by
  /- In a chart around each point, bound the smooth density on a small
  closed coordinate ball. Its finite Lebesgue measure gives a finite-measure
  neighborhood in the original manifold. This proves local finiteness of μ;
  the compact-space measure instance then gives finite total mass. -/
  classical
  -- A bounded density on a small coordinate ball gives a finite-measure neighborhood.
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
  -- Compactness upgrades local finiteness to finite total mass.
  infer_instance

variable {r : ℕ} (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- The original complex bundle has real-smooth transitions and its given Hermitian
metric has real-smooth local Gram matrices. -/
class IsSmoothHermitianBundle : Prop
    extends IsSmoothComplexBundle (n := n) (r := r) E where
  /-- Smoothness of all Gram matrix entries in every complex-linear bundle chart. -/
  contMDiffOn_inner :
    ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e],
      ∀ i j : Fin r,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ inner ℂ (e.symmL ℂ x (EuclideanSpace.single i 1))
            (e.symmL ℂ x (EuclideanSpace.single j 1))) e.baseSet

/-- The integral of the pointwise Hermitian pairing of two smooth sections.
As in mathlib, it is conjugate-linear in its first argument and linear in its second. -/
def smoothSectionPairing
    (s t : smoothSections (n := n) (r := r) E) : ℂ :=
  ∫ x, inner ℂ (s.val x) (t.val x) ∂μ

variable [CompactSpace M] [IsSmoothHermitianBundle (n := n) (r := r) E]

/-- On a compact base the integrand defining the section pairing is integrable. -/
theorem integrable_inner_smoothSections
    (s t : smoothSections (n := n) (r := r) E) :
    Integrable (fun x ↦ inner ℂ (s.val x) (t.val x)) μ := by
  /- In a local frame this is a finite sum of products of smooth section coordinates
  and smooth Gram matrix entries. Thus it is continuous, and on the compact base it
  is bounded. The positive smooth density has finite total mass, giving integrability. -/
  classical
  open scoped ComplexConjugate in
    let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
    -- In each bundle frame the original pairing is a continuous finite Gram sum.
    have hcont : Continuous (fun x ↦ inner ℂ (s.val x) (t.val x)) := by
      rw [continuous_iff_continuousAt]
      intro x
      let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
      have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
      have hcoord (u : smoothSections (n := n) (r := r) E) (i : Fin r) :
          ContinuousOn (fun y ↦ (e ⟨y, u.val y⟩).2 i) e.baseSet :=
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).continuous.comp_continuousOn
          (u.property e inferInstance).continuousOn
      have hsum : ContinuousOn (fun y ↦ ∑ i, ∑ j,
          conj ((e ⟨y, s.val y⟩).2 i) *
            inner ℂ (e.symmL ℂ y (EuclideanSpace.single i 1))
              (e.symmL ℂ y (EuclideanSpace.single j 1)) *
                (e ⟨y, t.val y⟩).2 j) e.baseSet := by
        apply continuousOn_finsetSum
        intro i _
        apply continuousOn_finsetSum
        intro j _
        exact ((hcoord s i).star.mul
          (IsSmoothHermitianBundle.contMDiffOn_inner (n := n) e i j).continuousOn).mul
            (hcoord t j)
      -- Expand both actual vectors using the same inverse frame.
      have heval (y : M) (hy : y ∈ e.baseSet) :
          inner ℂ (s.val y) (t.val y) = ∑ i, ∑ j,
            conj ((e ⟨y, s.val y⟩).2 i) *
              inner ℂ (e.symmL ℂ y (EuclideanSpace.single i 1))
                (e.symmL ℂ y (EuclideanSpace.single j 1)) *
                  (e ⟨y, t.val y⟩).2 j := by
        have hexpand (u : E y) : ∑ i : Fin r, (e ⟨y, u⟩).2 i •
            e.symmL ℂ y (EuclideanSpace.single i 1) = u := by
          have heq := congrArg (e.symmL ℂ y)
            ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨y, u⟩).2))
          calc
            _ = e.symmL ℂ y ((e ⟨y, u⟩).2) := by
              simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
            _ = u := by
              rw [← e.continuousLinearMapAt_apply_of_mem ℂ hy]
              exact e.symmL_continuousLinearMapAt hy _
        conv_lhs => rw [← hexpand (s.val y), ← hexpand (t.val y)]
        rw [sum_inner]
        simp only [inner_smul_left, inner_sum, inner_smul_right]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      exact (hsum.congr heval).continuousAt (e.open_baseSet.mem_nhds hx)
    -- A continuous integrand on this compact finite-measure base is integrable.
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral Hermitian pairing separates smooth sections. -/
theorem smoothSectionPairing_self_eq_zero_iff
    (s : smoothSections (n := n) (r := r) E) :
    smoothSectionPairing μ E s s = 0 ↔ s = 0 := by
  /- The real part of the integrand is the pointwise squared norm and is nonnegative.
  A zero integral therefore makes the section zero almost everywhere. Positive local
  densities give every nonempty open set positive measure. Continuity of the section
  coordinates in each frame upgrades almost-everywhere vanishing to pointwise vanishing.
  The converse is the zero integral. -/
  classical
  -- Strictly positive coordinate densities give every nonempty open set positive mass.
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
  constructor
  · intro hzero
    -- A zero integral forces the nonnegative real self-pairing to vanish almost everywhere.
    have hint := integrable_inner_smoothSections (n := n) μ E s s
    have hrealint : Integrable (fun x ↦ (inner ℂ (s.val x) (s.val x)).re) μ :=
      Complex.reCLM.integrable_comp hint
    have hrealzero : (∫ x, (inner ℂ (s.val x) (s.val x)).re ∂μ) = 0 := by
      calc
        _ = (∫ x, inner ℂ (s.val x) (s.val x) ∂μ).re := by
          simpa only [RCLike.re_eq_complex_re] using integral_re hint
        _ = 0 := congrArg Complex.re hzero
    have hae : ∀ᵐ x ∂μ, s.val x = 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg
        (fun x ↦ inner_self_nonneg (𝕜 := ℂ) (x := s.val x)) hrealint).mp hrealzero
      filter_upwards [hz] with x hx
      change RCLike.re (inner ℂ (s.val x) (s.val x)) = 0 at hx
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      rw [← inner_self_ofReal_re, hx]
      rfl
    -- Continuous frame coordinates upgrade almost-everywhere zero to pointwise zero.
    apply Subtype.ext
    funext x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoordae : (fun y ↦ (e ⟨y, s.val y⟩).2) =ᵐ[μ.restrict e.baseSet]
        (fun _ ↦ (0 : EuclideanSpace ℂ (Fin r))) := by
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem e.open_baseSet.measurableSet]
        with y hy hye
      rw [hy, ← e.continuousLinearMapAt_apply_of_mem ℂ hye, map_zero]
    have hcoordzero := Measure.eqOn_open_of_ae_eq hcoordae e.open_baseSet
      (s.property e inferInstance).continuousOn continuousOn_const hx
    change s.val x = 0
    apply (e.continuousLinearEquivAt ℂ x hx).injective
    simpa only [map_zero, Trivialization.continuousLinearEquivAt_apply] using hcoordzero
  · rintro rfl
    simp [smoothSectionPairing]

end AtiyahSinger
