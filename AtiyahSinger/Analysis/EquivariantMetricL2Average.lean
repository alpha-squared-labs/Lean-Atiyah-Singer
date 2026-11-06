/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.UnitaryOperatorAverage
public import AtiyahSinger.Analysis.EquivariantL2
public import AtiyahSinger.Analysis.EquivariantOperatorAverage
public import AtiyahSinger.Analysis.EquivariantSectionTopologyWeak
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.PseudodifferentialDistributions
public import AtiyahSinger.Analysis.SmoothSectionIntegral
public import AtiyahSinger.Geometry.SmoothInvariantMetric

import Mathlib.MeasureTheory.Integral.Prod

/-!
# The original metric L² realization of Haar averaging

Public module ID: M0539.

The smooth-section integral and the integral in the specified metric Hilbert
completion agree. Scalar pairing against the dense original smooth sections
and Fubini identify the two integrals without assigning a Banach norm to the
smooth-section space. This supplies the comparison needed to transfer the
operator-norm contraction of strong unitary averaging to actual PDO averages.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set Topology
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (h : SmoothHermitianMetric (n := n) (r := r) E)

set_option maxHeartbeats 1200000 in
-- Same-fiber integration is identified against every original dense smooth test section.
/-- A compact continuous smooth-section family has the same integral in the metric completion. -/
theorem SmoothHermitianMetric.smoothToL2_integral
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (f : Y → A.SmoothSectionSpace) (hf : Continuous f)
    (s : smoothSections (n := n) (r := r) E)
    (hs : ∀ x, s.val x = ∫ y, (A.smoothSectionEquiv (f y)).val x ∂ν) :
    h.smoothToL2 μ s = ∫ y, h.smoothToL2 μ (A.smoothSectionEquiv (f y)) ∂ν := by
  classical
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let S (y : Y) := A.smoothSectionEquiv (f y)
  -- A nonzero original partition weight recovers joint total-space evaluation locally.
  have htotal : Continuous (fun p : Y × M ↦
      (⟨p.2, (S p.1).val p.2⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) := by
    rw [continuous_iff_continuousAt]
    intro p
    obtain ⟨j, hj⟩ : ∃ j : Fin A.size, A.cutoff j p.2 ≠ 0 := by
      by_contra! hz
      have hsum := A.sum_cutoff p.2
      simp only [hz, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    let e := A.frame j
    let := A.frame_mem_atlas j
    have hx := A.support_subset j (subset_tsupport _ hj)
    apply (e.tendsto_nhds_iff (show
      (⟨p.2, (S p.1).val p.2⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E) ∈ e.source from
        e.mem_source.mpr hx.2)).mpr
    refine ⟨continuous_snd.continuousAt, ?_⟩
    have hcoord : ContinuousAt (fun z : Y × M ↦
        A.localize j (S z.1) (A.chart j z.2)) p :=
      continuous_eval.continuousAt.comp
        ((((SchwartzMap.toBoundedContinuousFunctionCLM ℝ
          (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin r))).continuous.comp
            ((A.continuous_localize j).comp hf)).comp continuous_fst).continuousAt.prodMk
          (((A.chart j).continuousOn.continuousAt
            ((A.chart j).open_source.mem_nhds hx.1)).comp continuous_snd.continuousAt))
    have hinv : ContinuousAt (fun z : Y × M ↦ (A.cutoff j z.2 : ℂ)⁻¹) p :=
      (Complex.continuous_ofReal.comp ((A.smooth_cutoff j).continuous.comp continuous_snd))
        |>.continuousAt.inv₀ (Complex.ofReal_ne_zero.mpr hj)
    have hcalc := hinv.smul hcoord
    apply hcalc.congr_of_eventuallyEq
    have hnear : ∀ᶠ z : Y × M in 𝓝 p, A.cutoff j z.2 ≠ 0 :=
      ((A.smooth_cutoff j).continuous.comp continuous_snd).continuousAt.eventually_ne hj
    filter_upwards [hnear] with z hz
    have hxz := A.support_subset j (subset_tsupport _ hz)
    have hlocal : A.localize j (S z.1) (A.chart j z.2) =
        (A.cutoff j z.2 : ℂ) • (e ⟨z.2, (S z.1).val z.2⟩).2 := by
      change A.localizedFunction j (S z.1) (A.chart j z.2) = _
      simp only [SmoothBundlePresentation.localizedFunction,
        ite_eq_left ((A.chart j).map_source hxz.1), sectionInChart,
        (A.chart j).left_inv hxz.1]
      apply congrArg (fun w : TotalSpace (EuclideanSpace ℂ (Fin r)) E ↦
        (A.cutoff j z.2 : ℂ) • (A.frame j w).2)
      exact congrArg (fun x : M ↦
        (⟨x, (S z.1).val x⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          ((A.chart j).left_inv hxz.1)
    change (e ⟨z.2, (S z.1).val z.2⟩).2 =
      (A.cutoff j z.2 : ℂ)⁻¹ • A.localize j (S z.1) (A.chart j z.2)
    rw [hlocal, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hz)]
  -- The same Sobolev-zero comparison proves continuity in the original metric L² space.
  have hL2 : Continuous (fun y ↦ h.smoothToL2 μ (S y)) := by
    have hc := (h.sobolevZeroEquivL2 (μ := μ) A).continuous.comp
      ((A.continuous_smoothToSobolev 0).comp hf)
    simpa only [Function.comp_def, h.sobolevZeroEquivL2_smooth] using hc
  have hint := hL2.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  have htest (v : smoothSections (n := n) (r := r) E) :
      inner ℂ (h.smoothToL2 μ v) (h.smoothToL2 μ s) =
        inner ℂ (h.smoothToL2 μ v) (∫ y, h.smoothToL2 μ (S y) ∂ν) := by
    let := modelTopology (EuclideanSpace ℂ (Fin r)) E
    let : TopologicalSpace (TotalSpace Unit (E ×ᵇ E)) := sumTopology
    have hv : Continuous (fun x : M ↦ (⟨x, v.val x⟩ : TotalSpace Unit E)) := by
      apply (continuous_model_section_iff (EuclideanSpace ℂ (Fin r)) E v.val).mpr
      rw [continuous_iff_continuousAt]
      intro x
      apply (FiberBundle.continuousAt_section (EuclideanSpace ℂ (Fin r)) x).mpr
      exact (v.property (trivializationAt (EuclideanSpace ℂ (Fin r)) E x)
        inferInstance).continuousOn.continuousAt
          ((trivializationAt (EuclideanSpace ℂ (Fin r)) E x).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt _ _ x))
    have htotalUnit : Continuous (fun p : Y × M ↦
        (⟨p.2, (S p.1).val p.2⟩ : TotalSpace Unit E)) := by
      exact (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin r)) E _).mpr htotal
    have hpair : Continuous (fun p : Y × M ↦
        h.pairing p.2 (v.val p.2) ((S p.1).val p.2)) := by
      have hdouble : Continuous (fun p : Y × M ↦
          (⟨p.2, (v.val p.2, (S p.1).val p.2)⟩ : TotalSpace Unit (E ×ᵇ E))) := by
        apply continuous_induced_rng.mpr
        exact (hv.comp continuous_snd).prodMk htotalUnit
      exact h.continuous_totalPairing.comp hdouble
    have hpint := hpair.integrable_of_hasCompactSupport (μ := ν.prod μ)
      (HasCompactSupport.of_compactSpace _)
    rw [h.inner_smoothToL2]
    have hcomm := (innerSL ℂ (h.smoothToL2 μ v)).integral_comp_comm hint
    change (∫ y, inner ℂ (h.smoothToL2 μ v) (h.smoothToL2 μ (S y)) ∂ν) =
      inner ℂ (h.smoothToL2 μ v) (∫ y, h.smoothToL2 μ (S y) ∂ν) at hcomm
    rw [← hcomm]
    simp_rw [h.inner_smoothToL2]
    change (∫ x, h.pairing x (v.val x) (s.val x) ∂μ) =
      ∫ y, ∫ x, h.pairing x (v.val x) ((S y).val x) ∂μ ∂ν
    rw [integral_integral_swap hpint]
    apply integral_congr_ae
    filter_upwards with x
    rw [hs]
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    let L : E x →ₗ[ℂ] ℂ := {
      toFun := h.pairing x (v.val x)
      map_add' := fun u w ↦ InnerProductSpace.Core.inner_add_right _ _ _
      map_smul' := fun z u ↦ InnerProductSpace.Core.inner_smul_right _ _ }
    have hxi : Integrable (fun y ↦ (S y).val x) ν :=
      ((A.continuous_section_evaluation x).comp hf).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact (L.toContinuousLinearMap.integral_comp_comm hxi).symm
  apply ext_inner_left ℂ
  intro v
  exact congrFun ((h.denseRange_smoothToL2 μ).equalizer
    (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
      (funext htest)) v

end AtiyahSinger

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

/-- The original PDO average realizes strong unitary averaging on the same metric L² spaces. -/
theorem metricL2Extension_average
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0) :
    let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
    let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
    (P.average IG σE σF hσE hσF).metricL2Extension h k =
      unitaryOperatorAverage ν
        (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant)
        (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant)
        (h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant)
        (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
        (P.metricL2Extension h k) := by
  classical
  dsimp only
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  let ρ := h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant
  let W := unitaryOperatorAverage ν ρ τ
    (h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant)
    (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
  -- Both bounded maps agree once evaluated on the same dense original smooth sections.
  apply DFunLike.coe_injective
  apply (h.denseRange_smoothToL2 μ).equalizer
    ((P.average IG σE σF hσE hσF).metricL2Extension h k).continuous
    (W (P.metricL2Extension h k)).continuous
  funext u
  change (P.average IG σE σF hσE hσF).metricL2Extension h k (h.smoothToL2 μ u) =
    unitaryOperatorAverage ν ρ τ _ _ (P.metricL2Extension h k) (h.smoothToL2 μ u)
  rw [metricL2Extension_smooth]
  change k.smoothToL2 μ ((P.average IG σE σF hσE hσF).toLinearMap u) =
    ∫ g, τ g (P.metricL2Extension h k (ρ g⁻¹ (h.smoothToL2 μ u))) ∂ν
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let R := σE.smoothSectionRepresentation IG hσE
  let S := σF.smoothSectionRepresentation IG hσF
  let f (g : G) := B.smoothSectionEquiv.symm (S g (P.toLinearMap (R g⁻¹ u)))
  have hf : Continuous f := by
    have hi := (A.continuous_smoothSectionAction_of_isManifold IG σE hσE).comp
      (continuous_inv.prodMk (continuous_const (y := A.smoothSectionEquiv.symm u)))
    have hp := (P.continuous_smoothSectionMap A B).comp hi
    exact (B.continuous_smoothSectionAction_of_isManifold IG σF hσF).comp
      (continuous_id.prodMk hp)
  have heval (g : G) :
      τ g (P.metricL2Extension h k (ρ g⁻¹ (h.smoothToL2 μ u))) =
        k.smoothToL2 μ (B.smoothSectionEquiv (f g)) := by
    change k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant g
      (P.metricL2Extension h k
        (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g⁻¹
          (h.smoothToL2 μ u))) = _
    rw [h.l2IsometryRepresentation_smoothToL2, P.metricL2Extension_smooth,
      k.l2IsometryRepresentation_smoothToL2]
    rfl
  rw [show (∫ g, τ g (P.metricL2Extension h k (ρ g⁻¹ (h.smoothToL2 μ u))) ∂ν) =
      ∫ g, k.smoothToL2 μ (B.smoothSectionEquiv (f g)) ∂ν from
    integral_congr_ae (Filter.Eventually.of_forall heval)]
  exact k.smoothToL2_integral μ B ν f hf
    ((P.average IG σE σF hσE hσF).toLinearMap u)
    (fun x ↦ P.average_apply IG σE σF hσE hσF u x)

end AtiyahSinger.PseudodifferentialOperator
