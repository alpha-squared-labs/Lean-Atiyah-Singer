/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Geometry.MetricTransport
public import AtiyahSinger.Geometry.SupportedSectionEquivalence

/-!
# Integral pairings on compactly supported smooth sections

Public module ID: M1017.

D02/UL03/P02: compact support replaces compactness of the ambient base for the
scalar integrability and definiteness needed in local adjoint comparisons.
Zero extension preserves the actual pairing when the metrics and measures agree
on the support. No new Hilbert completion or unrestricted noncompact adjoint is
introduced. Sources: SG III.5 pp.194--195 and III.13.4 pp.248--249; the explicit
relative pairing statements are project supplements to the book's kernel argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 25

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT hSC hμ


set_option linter.unusedSectionVars false in
/-- One compactly supported smooth factor makes the scalar metric pairing integrable. -/
theorem SmoothHermitianMetric.integrable_pairing_of_supported
    (K : Set M) (hK : IsCompact K)
    (s : supportedSmoothSections (n := n) (r := r) E K)
    (t : smoothSections (n := n) (r := r) E) :
    Integrable (fun x ↦ h.pairing x (s.val.val x) (t.val x)) μ := by
  /- Smooth Gram entries and section coordinates give a continuous scalar
  function, zero off K. A finite cover of K by relatively compact coordinate
  neighborhoods bounds the positive smooth density and proves μ(K)<∞.
  The scalar function is bounded on K, hence integrable. The second section
  need not have compact support or any global growth bound. -/
  classical
  -- Smooth coordinate densities are locally finite, without compactness of the base.
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
  -- The actual Gram expansion proves continuity of this same scalar pairing.
  have hcont : Continuous (fun x ↦ h.pairing x (s.val.val x) (t.val x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoord (u : smoothSections (n := n) (r := r) E) (i : Fin r) :
        ContinuousOn (fun y ↦ (e ⟨y, u.val y⟩).2 i) e.baseSet :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).continuous.comp_continuousOn
        (u.property e inferInstance).continuousOn
    have hsum : ContinuousOn (fun y ↦ ∑ i, ∑ j,
        conj ((e ⟨y, s.val.val y⟩).2 i) * h.gramMatrix e y i j *
          (e ⟨y, t.val y⟩).2 j) e.baseSet := by
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact ((hcoord s.val i).star.mul (h.contMDiffOn_gram e i j).continuousOn).mul (hcoord t j)
    have heval (y : M) (hy : y ∈ e.baseSet) :
        h.pairing y (s.val.val y) (t.val y) = ∑ i, ∑ j,
          conj ((e ⟨y, s.val.val y⟩).2 i) * h.gramMatrix e y i j *
            (e ⟨y, t.val y⟩).2 j :=
      h.pairing_eq_gramMatrix e y hy _ _
    exact (hsum.congr heval).continuousAt (e.open_baseSet.mem_nhds hx)
  -- Only the first factor needs support: the scalar pairing vanishes outside K.
  have hsupport : Function.support (fun x ↦ h.pairing x (s.val.val x) (t.val x)) ⊆ K := by
    intro x hx
    by_contra hxK
    apply hx
    change h.pairing x (s.val.val x) (t.val x) = 0
    rw [s.property x hxK]
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  have hcompact : HasCompactSupport (fun x ↦ h.pairing x (s.val.val x) (t.val x)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hsupport hK.isClosed)
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The actual integral pairing is definite on sections with prescribed compact support. -/
theorem SmoothHermitianMetric.sectionPairing_self_eq_zero_iff_of_supported
    (K : Set M) (hK : IsCompact K)
    (s : supportedSmoothSections (n := n) (r := r) E K) :
    h.sectionPairing μ s.val s.val = 0 ↔ s = 0 := by
  /- Compact support gives integrability by integrable_pairing_of_supported.
  If s is nonzero at a point, positivity of the fiber form and continuity give
  a positive lower bound for its real quadratic form on a neighborhood.
  Every nonempty open set has positive smooth-density measure, contradicting
  zero integral. The converse uses the zero integrand. No regularity of the
  boundary or nonempty interior of K is assumed; K may be empty. -/
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
    have hint := h.integrable_pairing_of_supported μ K hK s s.val
    have hrealint : Integrable (fun x ↦ (h.pairing x (s.val.val x) (s.val.val x)).re) μ :=
      Complex.reCLM.integrable_comp hint
    have hrealzero : (∫ x, (h.pairing x (s.val.val x) (s.val.val x)).re ∂μ) = 0 := by
      calc
        _ = (∫ x, h.pairing x (s.val.val x) (s.val.val x) ∂μ).re := by
          simpa only [RCLike.re_eq_complex_re] using integral_re hint
        _ = 0 := congrArg Complex.re hzero
    have hae : ∀ᵐ x ∂μ, s.val.val x = 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg
        (fun x ↦ (h.toCore x).re_inner_nonneg (s.val.val x)) hrealint).mp hrealzero
      filter_upwards [hz] with x hx
      by_contra hu
      exact (ne_of_gt (h.pairing_self_pos x (s.val.val x) hu)) hx
    -- Continuous frame coordinates upgrade almost-everywhere zero to pointwise zero.
    apply Subtype.ext
    apply Subtype.ext
    funext x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoordae : (fun y ↦ (e ⟨y, s.val.val y⟩).2) =ᵐ[μ.restrict e.baseSet]
        (fun _ ↦ (0 : EuclideanSpace ℂ (Fin r))) := by
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem e.open_baseSet.measurableSet]
        with y hy hye
      rw [hy, ← e.continuousLinearMapAt_apply_of_mem ℂ hye, map_zero]
    have hcoordzero := Measure.eqOn_open_of_ae_eq hcoordae e.open_baseSet
      (s.val.property e inferInstance).continuousOn continuousOn_const hx
    change s.val.val x = 0
    apply (e.continuousLinearEquivAt ℂ x hx).injective
    simpa only [map_zero, Trivialization.continuousLinearEquivAt_apply] using hcoordzero
  · rintro rfl
    have hz (x : M) : h.pairing x 0 0 = 0 := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    simp only [SmoothHermitianMetric.sectionPairing]
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall hz)

-- The restricted measure equality identifies the two supported scalar integrals.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Zero extension and restriction preserve the pairing for geometries agreeing on its support. -/
theorem SmoothHermitianMetric.sectionPairing_zeroExtension
    (U : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (k : SmoothHermitianMetric (n := n) (r := r) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E))
    (ν : Measure U) [hν : IsSmoothPositiveMeasure (n := n) ν]
    (hk : ∀ (x : U), x.val ∈ K → ∀ v w : E x.val,
      h.pairing x.val v w = k.pairing x v w)
    (hνμ : ν.restrict ((Subtype.val : U → M) ⁻¹' K) =
      (μ.comap (Subtype.val : U → M)).restrict ((Subtype.val : U → M) ⁻¹' K))
    (s : supportedSmoothSections (n := n) (r := r) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      ((Subtype.val : U → M) ⁻¹' K))
    (t : smoothSections (n := n) (r := r) E) :
    h.sectionPairing μ (smoothSectionZeroExtension E U K hK.isClosed hKU s) t =
      k.sectionPairing ν s.val (smoothSectionRestriction E U t) := by
  /- First restrict the ambient zero-extension integrand to U. Its fiber value
  there is exactly the original local section. The metrics agree on K, and
  the supported section vanishes outside K, so the scalar integrands agree
  on all of U. Use the measurable inclusion's comap integral identity, then
  restrict both local measures to the same preimage of K and apply hνμ.
  This identity itself uses only the supplied restricted measure equality;
  finiteness of the supported pairings is provided by the preceding theorem.
  No equality of metrics or measures away from K is needed. -/
  classical
  let f : M → ℂ := fun x ↦ h.pairing x
    ((smoothSectionZeroExtension E U K hK.isClosed hKU s).val x) (t.val x)
  let g : U → ℂ := fun x ↦ k.pairing x (s.val.val x) (t.val x.val)
  -- The ambient zero extension makes the integral supported inside the same open set.
  have hfzero (x : M) (hx : x ∉ (U : Set M)) : f x = 0 := by
    change h.pairing x (if hxU : x ∈ U then s.val.val ⟨x, hxU⟩ else 0) _ = 0
    erw [dite_eq_right hx]
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  -- Agreement is needed only on K: away from K the first local section is zero.
  have hfg (x : U) : f x.val = g x := by
    change h.pairing x.val
      (if hxU : x.val ∈ U then s.val.val ⟨x.val, hxU⟩ else 0) (t.val x.val) = _
    erw [dite_eq_left x.property]
    by_cases hxK : x.val ∈ K
    · exact hk x hxK _ _
    · have hs : s.val.val x = 0 := s.property x hxK
      change h.pairing x.val (s.val.val x) (t.val x.val) =
        k.pairing x (s.val.val x) (t.val x.val)
      rw [hs]
      have hz₁ : h.pairing x.val 0 (t.val x.val) = 0 := by
        let : InnerProductSpace.Core ℂ (E x.val) := h.toCore x.val
        exact InnerProductSpace.Core.inner_zero_left _
      have hz₂ : k.pairing x 0 (t.val x.val) = 0 := by
        let := k.toCore x
        exact InnerProductSpace.Core.inner_zero_left _
      exact hz₁.trans hz₂.symm
  have hgzero (x : U) (hx : x ∉ (Subtype.val : U → M) ⁻¹' K) : g x = 0 := by
    change k.pairing x (s.val.val x) (t.val x.val) = 0
    rw [s.property x hx]
    let := k.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  -- Use the original open inclusion's comap, then the prescribed restricted measures.
  change (∫ x, f x ∂μ) = ∫ x, g x ∂ν
  calc
    _ = ∫ x in (U : Set M), f x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hfzero).symm
    _ = ∫ x : U, f x.val ∂(μ.comap (Subtype.val : U → M)) :=
      (integral_subtype_comap U.isOpen.measurableSet f).symm
    _ = ∫ x : U, g x ∂(μ.comap (Subtype.val : U → M)) :=
      integral_congr_ae (Filter.Eventually.of_forall hfg)
    _ = ∫ x in (Subtype.val : U → M) ⁻¹' K, g x
        ∂(μ.comap (Subtype.val : U → M)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hgzero).symm
    _ = ∫ x in (Subtype.val : U → M) ⁻¹' K, g x ∂ν := by rw [hνμ]
    _ = ∫ x, g x ∂ν := setIntegral_eq_integral_of_forall_compl_eq_zero hgzero

end AtiyahSinger
