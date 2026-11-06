/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.HermitianMetricAdjointKernel
public import AtiyahSinger.Analysis.HermitianMetricOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Order-zero PDOs on the explicit integral L² completions

Public module ID: M0725.

A07: compare the concrete H⁰ and metric integral models, then extend the given
order-zero map. Only these actual integral inner products identify the geometric
formal adjoint with the bounded Hilbert adjoint. Sources: SG III.2.15 and III.5.2–5.3;
model comparisons and natural kernel/quotient maps are project deductions.
The bounded realization, metric transport, Hilbert-adjoint comparison and the
natural kernel/quotient maps are established. Elliptic Fredholmness and bijectivity
use the constructed full-symbol parametrix with the original specified metrics.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

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

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace SmoothHermitianMetric

omit hF

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the original smooth inclusion and integral metric L2 completion.
/-- The identity on smooth sections extends to the H⁰ versus integral L² equivalence. -/
theorem existsUnique_sobolevZeroEquivL2 :
    ∃! T : A.SobolevSpace 0 ≃L[ℂ] h.L2SectionSpace μ,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev 0 u) = h.smoothToL2 μ u := by
  /- Compare the given positive Gram forms and density with the Euclidean coordinates
  on each original compact chart support. The partition controls the squared weights
  in both directions. Extend the identity and its inverse through the same smooth
  section space; none of the original fiber norms or topologies is changed. -/
  have hcompare :
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
        c * ‖A.smoothToSobolev 0 u‖ ≤ ‖h.smoothToL2 μ u‖ ∧
          ‖h.smoothToL2 μ u‖ ≤ C * ‖A.smoothToSobolev 0 u‖ := by
    classical
    let V := EuclideanSpace ℂ (Fin r)
    let N (x : M) (u : E x) : ℝ := (h.pairing x u u).re
    have hNpos (x : M) (u : E x) : 0 ≤ N x u := (h.toCore x).re_inner_nonneg u
    have hNzero (x : M) : N x 0 = 0 := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      simp [N, SmoothHermitianMetric.pairing, InnerProductSpace.Core.inner_zero_left]
    have hNscale (x : M) (u : E x) (a : ℝ) : N x ((a : ℂ) • u) = N x u * a ^ 2 := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      rw [show N x ((a : ℂ) • u) = N x u * a * a from
        InnerProductSpace.Core.re_inner_smul_ofReal_smul_self (𝕜 := ℂ) u]
      ring
    have hnorm (u : smoothSections (n := n) (r := r) E) :
        ‖h.smoothToL2 μ u‖ ^ 2 = ∫ x, N x (u.val x) ∂μ := by
      rw [h.norm_smoothToL2_sq]
      exact (integral_re (h.integrable_pairing μ u u)).symm
    choose w hw hwpos hmap using
      (fun j : Fin A.size ↦ IsSmoothPositiveMeasure.exists_smooth_density
        (μ := μ) (A.chart j) (A.chart_mem_atlas j))
    -- Compare the given density and metric with each original coordinate norm on its support.
    have hlocal (j : Fin A.size) :
        letI := A.frame_mem_atlas j
        ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        ∀ x ∈ tsupport (A.cutoff j), ∀ z : V,
          a * ‖z‖ ^ 2 ≤ w j (A.chart j x) * N x ((A.frame j).symmL ℂ x z) ∧
            w j (A.chart j x) * N x ((A.frame j).symmL ℂ x z) ≤ b * ‖z‖ ^ 2 := by
      let e := A.frame j
      let := A.frame_mem_atlas j
      let K := tsupport (A.cutoff j)
      let S := Metric.sphere (0 : V) 1
      let Q (x : M) (z : V) : ℝ :=
        (∑ i, ∑ k, conj (z i) * h.gramMatrix e x i k * z k).re
      let R (p : M × V) := w j (A.chart j p.1) * Q p.1 p.2
      have hQeq (x : M) (hx : x ∈ e.baseSet) (z : V) :
          Q x z = N x (e.symmL ℂ x z) := by
        have hz : (e ⟨x, e.symmL ℂ x z⟩).2 = z := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact e.continuousLinearMapAt_symmL hx z
        have heq := h.pairing_eq_gramMatrix e x hx (e.symmL ℂ x z) (e.symmL ℂ x z)
        rw [hz] at heq
        dsimp only [Q]
        rw [← heq]
      have hK := A.compact_support j
      have hS : IsCompact S := isCompact_sphere _ _
      have hcoeff (i k : Fin r) : ContinuousOn
          (fun p : M × V ↦ h.gramMatrix e p.1 i k) (K ×ˢ S) :=
        (h.contMDiffOn_gram e i k).continuousOn.comp continuous_fst.continuousOn
          (fun p hp ↦ (A.support_subset j hp.1).2)
      have hQcont : ContinuousOn (fun p : M × V ↦ Q p.1 p.2) (K ×ˢ S) := by
        apply Complex.continuous_re.comp_continuousOn
        apply continuousOn_finsetSum
        intro i _
        apply continuousOn_finsetSum
        intro k _
        have hi : Continuous (fun p : M × V ↦ p.2 i) :=
          (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i).comp continuous_snd
        have hk : Continuous (fun p : M × V ↦ p.2 k) :=
          (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) k).comp continuous_snd
        exact ((hi.star.continuousOn).mul (hcoeff i k)).mul hk.continuousOn
      have hwK : ContinuousOn (fun x : M ↦ w j (A.chart j x)) K :=
        (hw j).continuousOn.comp
          ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
          (fun x hx ↦ (A.chart j).map_source (A.support_subset j hx).1)
      have hRcont : ContinuousOn R (K ×ˢ S) :=
        (hwK.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)).mul hQcont
      have hRpos (p : M × V) (hp : p ∈ K ×ˢ S) : 0 < R p := by
        have hx := A.support_subset j hp.1
        have hz : p.2 ≠ 0 := by
          intro hz
          simp [S, hz] at hp
        have hinv : e.symmL ℂ p.1 p.2 ≠ 0 := by
          intro heq
          apply hz
          have he := e.continuousLinearMapAt_symmL (R := ℂ) hx.2 p.2
          simpa [heq] using he.symm
        dsimp only [R]
        rw [hQeq p.1 hx.2]
        exact mul_pos (hwpos j _ ((A.chart j).map_source hx.1))
          (h.pairing_self_pos p.1 _ hinv)
      obtain ⟨a, ha, halower⟩ := (hK.prod hS).exists_forall_le' hRcont hRpos
      obtain ⟨b, hupper⟩ := ((hK.prod hS).image_of_continuousOn hRcont).bddAbove
      refine ⟨a, max b 1, ha, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
      intro x hx z
      have hxe := (A.support_subset j hx).2
      by_cases hz : z = 0
      · subst z
        simp [hNzero]
      let y : V := (‖z‖⁻¹ : ℂ) • z
      have hy : y ∈ S := by
        simpa [S, y, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℂ) hz
      have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hscale : (‖z‖ : ℂ) • y = z := by
        simp [y, smul_smul, hz0]
      have hRscale : w j (A.chart j x) * N x (e.symmL ℂ x z) =
          R (x, y) * ‖z‖ ^ 2 := by
        dsimp only [R]
        rw [hQeq x hxe]
        conv_lhs => rw [← hscale]
        rw [map_smul, hNscale]
        ring
      have hlo := halower (x, y) ⟨hx, hy⟩
      have hup := (hupper ⟨(x, y), ⟨hx, hy⟩, rfl⟩).trans (le_max_left b 1)
      rw [hRscale]
      exact ⟨mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖z‖),
        mul_le_mul_of_nonneg_right hup (sq_nonneg ‖z‖)⟩
    choose a b ha hb hab using hlocal
    let := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
    have hnormcont (u : smoothSections (n := n) (r := r) E) :
        Continuous (fun x : M ↦ N x (u.val x)) := by
      exact Complex.continuous_re.comp (h.contMDiff_pairing u u).continuous
    -- The defining measure equality transports the actual cutoff-weighted integral.
    have htransport (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
        (∫ x, A.cutoff j x ^ 2 * N x (u.val x) ∂μ) =
          ∫ z in (A.chart j).target, w j z *
            (A.cutoff j ((A.chart j).symm z) ^ 2 *
              N ((A.chart j).symm z) (u.val ((A.chart j).symm z))) := by
      let c := A.chart j
      let f (x : M) := A.cutoff j x ^ 2 * N x (u.val x)
      let g (z : EuclideanSpace ℝ (Fin n)) := f (c.symm z)
      have hfcont : Continuous f := ((A.smooth_cutoff j).continuous.pow 2).mul (hnormcont u)
      have hgcont : ContinuousOn g c.target := hfcont.comp_continuousOn c.symm.continuousOn
      have hgd : AEStronglyMeasurable g ((volume.restrict c.target).withDensity
          (fun z ↦ ENNReal.ofReal (w j z))) :=
        AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
          (hgcont.aestronglyMeasurable c.open_target.measurableSet)
      have hgmap : AEStronglyMeasurable g (Measure.map c (μ.restrict c.source)) := by
        change AEStronglyMeasurable g
          (Measure.map (A.chart j) (μ.restrict (A.chart j).source))
        rw [hmap j]
        exact hgd
      have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w j z))
          (volume.restrict c.target) :=
        (ENNReal.continuous_ofReal.comp_continuousOn
          (hw j).continuousOn).aemeasurable c.open_target.measurableSet
      calc
        _ = ∫ x in c.source, f x ∂μ := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have hχ : A.cutoff j x = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            exact fun hxK ↦ hx (A.support_subset j hxK).1
          simp [f, hχ]
        _ = ∫ x in c.source, g (c x) ∂μ := by
          apply setIntegral_congr_fun c.open_source.measurableSet
          intro x hx
          simp [g, c.left_inv hx]
        _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
          (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet) hgmap).symm
        _ = ∫ z, g z ∂(volume.restrict c.target).withDensity
            (fun z ↦ ENNReal.ofReal (w j z)) := by rw [hmap j]
        _ = ∫ z in c.target, w j z * g z := by
          rw [integral_withDensity_eq_integral_toReal_smul₀ hwmeas
            (Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top)]
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
          rw [ENNReal.toReal_ofReal (hwpos j z hz).le, smul_eq_mul]
    -- Pointwise bounds are integrated in the same original chart, including its zero extension.
    have hchart (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
        a j * (∫ z, ‖A.localize j u z‖ ^ 2) ≤
            ∫ x, A.cutoff j x ^ 2 * N x (u.val x) ∂μ ∧
          (∫ x, A.cutoff j x ^ 2 * N x (u.val x) ∂μ) ≤
            b j * (∫ z, ‖A.localize j u z‖ ^ 2) := by
      let := A.frame_mem_atlas j
      let c := A.chart j
      let e := A.frame j
      let G (z : EuclideanSpace ℝ (Fin n)) :=
        w j z * (A.cutoff j (c.symm z) ^ 2 * N (c.symm z) (u.val (c.symm z)))
      have hFnorm (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
          ‖A.localize j u z‖ ^ 2 =
            A.cutoff j (c.symm z) ^ 2 * ‖(e ⟨c.symm z, u.val (c.symm z)⟩).2‖ ^ 2 := by
        change ‖A.localizedFunction j u z‖ ^ 2 = _
        rw [SmoothBundlePresentation.localizedFunction, ite_eq_left hz]
        simp only [sectionInChart, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
          sq_abs]
        rfl
      have hpoint (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
          a j * ‖A.localize j u z‖ ^ 2 ≤ G z ∧ G z ≤ b j * ‖A.localize j u z‖ ^ 2 := by
        rw [hFnorm z hz]
        by_cases hχ : A.cutoff j (c.symm z) = 0
        · simp [G, hχ]
        have hxK : c.symm z ∈ tsupport (A.cutoff j) := subset_tsupport _ hχ
        have hxe := (A.support_subset j hxK).2
        have heinv : e.symmL ℂ (c.symm z) (e ⟨c.symm z, u.val (c.symm z)⟩).2 =
            u.val (c.symm z) := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hxe]
          exact e.symmL_continuousLinearMapAt hxe _
        have h := hab j (c.symm z) hxK (e ⟨c.symm z, u.val (c.symm z)⟩).2
        rw [heinv, c.right_inv hz] at h
        constructor
        · have hmul := mul_le_mul_of_nonneg_left h.1 (sq_nonneg (A.cutoff j (c.symm z)))
          dsimp only [G]
          nlinarith only [hmul]
        · have hmul := mul_le_mul_of_nonneg_left h.2 (sq_nonneg (A.cutoff j (c.symm z)))
          dsimp only [G]
          nlinarith only [hmul]
      have hFint : Integrable (fun z ↦ ‖A.localize j u z‖ ^ 2) :=
        ((A.localize j u).memLp 2 volume).integrable_norm_pow (by decide)
      have hFtarget : (∫ z in c.target, ‖A.localize j u z‖ ^ 2) =
          ∫ z, ‖A.localize j u z‖ ^ 2 := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        change z ∉ (A.chart j).target at hz
        simp [SmoothBundlePresentation.localize,
          SmoothBundlePresentation.localizedFunction, hz]
      have hGcont : ContinuousOn G c.target :=
        (hw j).continuousOn.mul
          ((((A.smooth_cutoff j).continuous.pow 2).mul (hnormcont u)).comp_continuousOn
            c.symm.continuousOn)
      have hGint : Integrable G (volume.restrict c.target) := by
        apply ((hFint.restrict (s := c.target)).const_mul (b j)).mono'
          (hGcont.aestronglyMeasurable c.open_target.measurableSet)
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        have hGpos : 0 ≤ G z := mul_nonneg (hwpos j z hz).le
          (mul_nonneg (sq_nonneg _) (hNpos _ _))
        simpa only [Real.norm_eq_abs, abs_of_nonneg hGpos] using (hpoint z hz).2
      rw [htransport j u]
      constructor
      · have hi := integral_mono_ae ((hFint.restrict (s := c.target)).const_mul (a j)) hGint
          (by
            filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
            exact (hpoint z hz).1)
        simpa only [integral_const_mul, hFtarget] using hi
      · have hi := integral_mono_ae hGint ((hFint.restrict (s := c.target)).const_mul (b j))
          (by
            filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
            exact (hpoint z hz).2)
        simpa only [integral_const_mul, hFtarget] using hi
    -- At order zero the Bessel multiplier is identity, with the original Euclidean L² norm.
    have hcoord (v : SchwartzMap (EuclideanSpace ℝ (Fin n)) V) :
        ‖schwartzSobolevCoordinate 0 v‖ ^ 2 = ∫ z, ‖v z‖ ^ 2 := by
      have hz : schwartzSobolevCoordinate 0 v = v.toLp 2 := by
        simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
          SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
      rw [hz, SchwartzMap.norm_toLp' (by simp) (by simp)]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
      exact integral_nonneg fun z ↦ sq_nonneg _
    have hSob (u : smoothSections (n := n) (r := r) E) :
        ‖A.smoothToSobolev 0 u‖ ^ 2 = ∑ j, ∫ z, ‖A.localize j u z‖ ^ 2 := by
      rw [A.norm_smoothToSobolev_sq]
      exact Finset.sum_congr rfl (fun j _ ↦ hcoord (A.localize j u))
    let α : ℝ := 1 + ∑ j, (a j)⁻¹
    let β : ℝ := 1 + ∑ j, b j
    let δ : ℝ := (A.size : ℝ) + 1
    have hα : 0 < α := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ ↦ (inv_pos.mpr (ha j)).le)
    have hβ : 0 < β := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ ↦ (hb j).le)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hαj (j : Fin A.size) : (a j)⁻¹ ≤ α := by
      have hj := Finset.single_le_sum (fun k _ ↦ (inv_pos.mpr (ha k)).le)
        (Finset.mem_univ j)
      dsimp only [α]
      linarith
    have hβj (j : Fin A.size) : b j ≤ β := by
      have hj := Finset.single_le_sum (fun k _ ↦ (hb k).le) (Finset.mem_univ j)
      dsimp only [β]
      linarith
    refine ⟨Real.sqrt α⁻¹, Real.sqrt (δ * β), Real.sqrt_pos.mpr (inv_pos.mpr hα),
      Real.sqrt_pos.mpr (mul_pos hδ hβ), ?_⟩
    intro u
    let B (j : Fin A.size) := ∫ z, ‖A.localize j u z‖ ^ 2
    let I (j : Fin A.size) := ∫ x, A.cutoff j x ^ 2 * N x (u.val x) ∂μ
    have hBpos (j : Fin A.size) : 0 ≤ B j := integral_nonneg fun z ↦ sq_nonneg _
    have hIpos (j : Fin A.size) : 0 ≤ I j :=
      integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hNpos _ _)
    have hIint (j : Fin A.size) :
        Integrable (fun x ↦ A.cutoff j x ^ 2 * N x (u.val x)) μ :=
      (((A.smooth_cutoff j).continuous.pow 2).mul (hnormcont u)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hsumint : Integrable
        (fun x ↦ (∑ j, A.cutoff j x ^ 2) * N x (u.val x)) μ := by
      simpa only [← Finset.sum_mul] using
        integrable_finsetSum Finset.univ (fun j _ ↦ hIint j)
    have hsumI : (∑ j, I j) = ∫ x, (∑ j, A.cutoff j x ^ 2) * N x (u.val x) ∂μ := by
      simpa only [Finset.sum_mul, I] using
        (integral_finsetSum Finset.univ (fun j _ ↦ hIint j)).symm
    -- The partition identity controls its squared weights without a nonempty-index assumption.
    have hcutupper (x : M) : (∑ j, A.cutoff j x ^ 2) ≤ 1 := by
      simpa only [A.sum_cutoff, one_pow] using
        Finset.sum_sq_le_sq_sum_of_nonneg
          (s := Finset.univ) (fun j _ ↦ A.cutoff_nonneg j x)
    have hcutlower (x : M) : 1 ≤ δ * ∑ j, A.cutoff j x ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j : Fin A.size ↦ A.cutoff j x) (fun _ ↦ (1 : ℝ))
      have hzero : 0 ≤ ∑ j, A.cutoff j x ^ 2 :=
        Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      have hlo : 1 ≤ (A.size : ℝ) * ∑ j, A.cutoff j x ^ 2 := by
        simpa [A.sum_cutoff, mul_comm] using hcs
      exact hlo.trans (mul_le_mul_of_nonneg_right (by dsimp only [δ]; linarith) hzero)
    have hnormint : Integrable (fun x ↦ N x (u.val x)) μ :=
      (hnormcont u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hpartupper : (∑ j, I j) ≤ ‖h.smoothToL2 μ u‖ ^ 2 := by
      rw [hsumI, hnorm]
      exact integral_mono hsumint hnormint
        (fun x ↦ by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hcutupper x) (hNpos x (u.val x)))
    have hpartlower : ‖h.smoothToL2 μ u‖ ^ 2 ≤ δ * ∑ j, I j := by
      rw [hnorm, hsumI, ← integral_const_mul]
      apply integral_mono hnormint (hsumint.const_mul δ)
      intro x
      simpa only [one_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (hcutlower x) (hNpos x (u.val x))
    have hBsum : (∑ j, B j) ≤ α * ∑ j, I j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        B j ≤ I j / a j := (le_div_iff₀ (ha j)).mpr (by
          change B j * a j ≤ I j
          rw [mul_comm]
          exact (hchart j u).1)
        _ = (a j)⁻¹ * I j := by ring
        _ ≤ α * I j := mul_le_mul_of_nonneg_right (hαj j) (hIpos j)
    have hIsum : (∑ j, I j) ≤ β * ∑ j, B j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      exact (hchart j u).2.trans (mul_le_mul_of_nonneg_right (hβj j) (hBpos j))
    have hlower : ‖A.smoothToSobolev 0 u‖ ^ 2 ≤ α * ‖h.smoothToL2 μ u‖ ^ 2 :=
      (hSob u).le.trans (hBsum.trans
        (mul_le_mul_of_nonneg_left hpartupper hα.le))
    have hupper : ‖h.smoothToL2 μ u‖ ^ 2 ≤ (δ * β) * ‖A.smoothToSobolev 0 u‖ ^ 2 := by
      calc
        _ ≤ δ * ∑ j, I j := hpartlower
        _ ≤ δ * (β * ∑ j, B j) := mul_le_mul_of_nonneg_left hIsum hδ.le
        _ = _ := by rw [hSob]; simp only [B, mul_assoc]
    -- Positive square roots turn these integral quadratic bounds into the original norms.
    constructor
    · apply (sq_le_sq₀
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt (inv_pos.mpr hα).le]
      have hdiv : ‖A.smoothToSobolev 0 u‖ ^ 2 / α ≤ ‖h.smoothToL2 μ u‖ ^ 2 :=
        (div_le_iff₀ hα).mpr (by rw [mul_comm]; exact hlower)
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
    · apply (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      simpa only [mul_pow, Real.sq_sqrt (mul_pos hδ hβ).le] using hupper
  obtain ⟨c, C, hc, _, hbound⟩ := hcompare
  let f := LinearEquiv.refl ℂ (smoothSections (n := n) (r := r) E)
  have hforward : ∃ C, ∀ u,
      ‖h.smoothToL2 μ (f u)‖ ≤ C * ‖A.smoothToSobolev 0 u‖ :=
    ⟨C, fun u ↦ (hbound u).2⟩
  have hreverse : ∃ C, ∀ u,
      ‖A.smoothToSobolev 0 (f.symm u)‖ ≤ C * ‖h.smoothToL2 μ u‖ := by
    refine ⟨c⁻¹, ?_⟩
    intro u
    calc
      _ ≤ ‖h.smoothToL2 μ u‖ / c := (le_div_iff₀ hc).mpr (by
        simpa only [f, LinearEquiv.refl_symm, LinearEquiv.refl_apply, mul_comm]
          using (hbound u).1)
      _ = c⁻¹ * ‖h.smoothToL2 μ u‖ := by ring
  -- Extend the identity in both directions along the specified dense smooth inclusions.
  let T := f.extend (A.smoothToSobolev 0) (h.smoothToL2 μ)
    (A.denseRange_smoothToSobolev 0) hforward (h.denseRange_smoothToL2 μ) hreverse
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev 0 u) = h.smoothToL2 μ u :=
    f.extend_eq _ _ _ _ _ _ u
  refine ⟨T, hT, ?_⟩
  -- Density forces equality of the actual bounded maps, hence of the equivalences.
  intro S hS
  apply ContinuousLinearEquiv.ext
  apply (A.denseRange_smoothToSobolev 0).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

/-- The canonical same-section H⁰ to metric L² comparison. -/
def sobolevZeroEquivL2 : A.SobolevSpace 0 ≃L[ℂ] h.L2SectionSpace μ :=
  Classical.choose (h.existsUnique_sobolevZeroEquivL2 (μ := μ) A).exists

/-- The H⁰ comparison retains the original smooth section. -/
theorem sobolevZeroEquivL2_smooth (u : smoothSections (n := n) (r := r) E) :
    h.sobolevZeroEquivL2 (μ := μ) A (A.smoothToSobolev 0 u) = h.smoothToL2 μ u := by
  /- Use the specifying action of the unique continuous equivalence.
  Both inclusions carry the same smooth section, so the comparison is fixed
  geometrically despite its different completed norms. -/
  exact (h.existsUnique_sobolevZeroEquivL2 (μ := μ) A).exists.choose_spec u

end SmoothHermitianMetric

namespace PseudodifferentialOperator

variable (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)

/-- An order-zero PDO has a unique bounded realization on these two integral completions. -/
theorem existsUnique_metricL2Extension :
    ∃! T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (h.smoothToL2 μ u) = k.smoothToL2 μ (P.toLinearMap u) := by
  /- Choose finite smooth presentations and conjugate the existing
  H⁰ to H^(0-0) extension by their metric L² comparisons. The smooth action
  is the required one. Density identifies any two bounded extensions.
  This argument uses order zero and asserts no positive-order L² boundedness. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  let f := k.sobolevZeroEquivL2 (μ := μ) B
  -- Conjugate the actual order-zero action using the given metrics on both ends.
  let T := f.toContinuousLinearMap.comp
    ((P.sobolevRealization A B 0 0 (by simp)).comp e.symm.toContinuousLinearMap)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (h.smoothToL2 μ u) = k.smoothToL2 μ (P.toLinearMap u) := by
    have he : e (A.smoothToSobolev 0 u) = h.smoothToL2 μ u :=
      h.sobolevZeroEquivL2_smooth A u
    change f (P.sobolevRealization A B 0 0 (by simp)
      (e.symm (h.smoothToL2 μ u))) = _
    rw [← he, e.symm_apply_apply, P.sobolevRealization_smoothToSobolev]
    exact k.sobolevZeroEquivL2_smooth B (P.toLinearMap u)
  refine ⟨T, hT, ?_⟩
  -- The original integral completion has the same dense smooth source.
  intro S hS
  apply DFunLike.coe_injective
  apply (h.denseRange_smoothToL2 μ).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

/-- The order-zero operator on the actual two metric integral Hilbert completions. -/
def metricL2Extension : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ :=
  Classical.choose (P.existsUnique_metricL2Extension h k).exists

/-- The bounded realization has exactly the original PDO action on smooth sections. -/
theorem metricL2Extension_smooth (u : smoothSections (n := n) (r := r) E) :
    P.metricL2Extension h k (h.smoothToL2 μ u) = k.smoothToL2 μ (P.toLinearMap u) := by
  /- Apply the action specification of the chosen unique extension.
  It retains all lower-order and smoothing terms in P, not merely its
  principal class or an operator conjugate to it on smooth sections. -/
  exact (P.existsUnique_metricL2Extension h k).exists.choose_spec u

/-- Changing metrics transports the same bounded realization by identity comparisons. -/
theorem metricL2Extension_change (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F) :
    P.metricL2Extension h' k' = l2MetricTransport μ h h' k k' (P.metricL2Extension h k) := by
  /- The transported map agrees with P on every smooth section because
  both identity comparisons preserve that section. Uniqueness of the new
  bounded extension gives equality on the entire new domain completion. -/
  exact eq_l2MetricTransport_of_smoothToL2 μ h h' k k' P.toLinearMap
    (P.metricL2Extension h k) (P.metricL2Extension h' k')
    (P.metricL2Extension_smooth h k) (P.metricL2Extension_smooth h' k')

/-- For these integral L² metrics the geometric adjoint realizes the Hilbert adjoint. -/
theorem metricL2Extension_metricFormalAdjoint :
    (P.metricFormalAdjoint h k).metricL2Extension k h = (P.metricL2Extension h k).adjoint := by
  /- On pairs of dense smooth vectors the two completed inner products
  equal the specified integrals. The formal-adjoint identity gives bounded
  adjunction there. Joint continuity extends it to both Hilbert spaces, and
  uniqueness of the Hilbert adjoint identifies the maps without ellipticity. -/
  let R := (P.metricFormalAdjoint h k).metricL2Extension k h
  let T := P.metricL2Extension h k
  -- Keep both specified integral Hilbert products while extending the adjunction identity.
  have hpair : (fun z : k.L2SectionSpace μ × h.L2SectionSpace μ ↦
      inner ℂ (R z.1) z.2) = fun z ↦ inner ℂ z.1 (T z.2) := by
    apply ((k.denseRange_smoothToL2 μ).prodMap (h.denseRange_smoothToL2 μ)).equalizer
      ((R.continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner (T.continuous.comp continuous_snd))
    funext z
    rcases z with ⟨v, u⟩
    change inner ℂ ((P.metricFormalAdjoint h k).metricL2Extension k h
      (k.smoothToL2 μ v)) (h.smoothToL2 μ u) =
        inner ℂ (k.smoothToL2 μ v) (P.metricL2Extension h k (h.smoothToL2 μ u))
    rw [(P.metricFormalAdjoint h k).metricL2Extension_smooth k h,
      P.metricL2Extension_smooth h k, h.inner_smoothToL2, k.inner_smoothToL2]
    exact (P.isMetricFormalAdjoint_metricFormalAdjoint h k).symm v u
  -- The actual bounded adjoint is characterized by this identity on all completed pairs.
  apply (ContinuousLinearMap.eq_adjoint_iff R T).mpr
  intro v u
  exact congrFun hpair (v, u)

/-- Ellipticity makes the order-zero integral realization Fredholm. -/
theorem isFredholm_metricL2Extension (hP : P.IsElliptic) :
    (P.metricL2Extension h k).IsFredholm := by
  /- The full-symbol parametrix makes the H⁰ realization Fredholm.
  The canonical H⁰ to metric L² comparisons conjugate that exact operator
  to this realization. Bounded equivalences preserve closed range and the
  finite dimensions of both the kernel and quotient cokernel. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  have hfExists : ∃ f : B.SobolevSpace (0 - 0) ≃L[ℂ] k.L2SectionSpace μ,
      ∀ v : smoothSections (n := n) (r := q) F,
        f (B.smoothToSobolev (0 - 0) v) = k.smoothToL2 μ v := by
    rw [sub_self]
    exact ⟨k.sobolevZeroEquivL2 (μ := μ) B, k.sobolevZeroEquivL2_smooth B⟩
  obtain ⟨f, hf⟩ := hfExists
  let T := P.sobolevExtension A B 0
  -- Extend the same-section identity to the full original completion by density.
  have hcomm (u : A.SobolevSpace 0) : P.metricL2Extension h k (e u) = f (T u) := by
    have heq : (P.metricL2Extension h k).comp e.toContinuousLinearMap =
        f.toContinuousLinearMap.comp T := by
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 0).equalizer
        ((P.metricL2Extension h k).comp e.toContinuousLinearMap).continuous
        (f.toContinuousLinearMap.comp T).continuous
      funext v
      change P.metricL2Extension h k (e (A.smoothToSobolev 0 v)) =
        f (T (A.smoothToSobolev 0 v))
      rw [P.sobolevExtension_smoothToSobolev, h.sobolevZeroEquivL2_smooth,
        P.metricL2Extension_smooth, hf]
    exact DFunLike.congr_fun heq u
  have hFred : T.IsFredholm := P.isFredholm_sobolevExtension_of_isElliptic A B hP 0
  have hconj : P.metricL2Extension h k =
      f.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap) := by
    ext u
    exact (congrArg (P.metricL2Extension h k) (e.apply_symm_apply u)).symm.trans
      (hcomm (e.symm u))
  rw [hconj]
  exact f.isFredholm.comp (hFred.comp e.symm.isFredholm)

/-- The actual smooth inclusion carries smooth kernel vectors into the L² kernel. -/
theorem smoothToL2_mem_ker_metricL2Extension (u : P.toLinearMap.ker) :
    h.smoothToL2 μ u.val ∈ (P.metricL2Extension h k).ker := by
  /- Apply the smooth-action formula to u. Its PDO output is zero by
  kernel membership, and the output smooth-to-L² linear map sends zero to zero. -/
  change P.metricL2Extension h k (h.smoothToL2 μ u.val) = 0
  rw [P.metricL2Extension_smooth h k, show P.toLinearMap u.val = 0 from u.property,
    map_zero]

/-- The original smooth inclusion restricted to the two operator kernels. -/
def metricL2KerMap : P.toLinearMap.ker →ₗ[ℂ] (P.metricL2Extension h k).ker :=
  ((h.smoothToL2 μ).comp P.toLinearMap.ker.subtype).codRestrict
    (P.metricL2Extension h k).ker (P.smoothToL2_mem_ker_metricL2Extension h k)

/-- Elliptic regularity makes the actual smooth-to-L² kernel map bijective. -/
theorem bijective_metricL2KerMap (hP : P.IsElliptic) :
    Function.Bijective (P.metricL2KerMap h k) := by
  /- Transport an L² zero to H⁰ using the identity comparison. The
  elliptic left parametrix gives a unique smooth representative solving Pu=0.
  This proves surjectivity of the displayed map; injectivity follows from
  the original integral completion's smooth embedding. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  have hfExists : ∃ f : B.SobolevSpace (0 - 0) ≃L[ℂ] k.L2SectionSpace μ,
      ∀ v : smoothSections (n := n) (r := q) F,
        f (B.smoothToSobolev (0 - 0) v) = k.smoothToL2 μ v := by
    rw [sub_self]
    exact ⟨k.sobolevZeroEquivL2 (μ := μ) B, k.sobolevZeroEquivL2_smooth B⟩
  obtain ⟨f, hf⟩ := hfExists
  let T := P.sobolevExtension A B 0
  -- Extend the same-section identity to the full original completion by density.
  have hcomm (u : A.SobolevSpace 0) : P.metricL2Extension h k (e u) = f (T u) := by
    have heq : (P.metricL2Extension h k).comp e.toContinuousLinearMap =
        f.toContinuousLinearMap.comp T := by
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 0).equalizer
        ((P.metricL2Extension h k).comp e.toContinuousLinearMap).continuous
        (f.toContinuousLinearMap.comp T).continuous
      funext v
      change P.metricL2Extension h k (e (A.smoothToSobolev 0 v)) =
        f (T (A.smoothToSobolev 0 v))
      rw [P.sobolevExtension_smoothToSobolev, h.sobolevZeroEquivL2_smooth,
        P.metricL2Extension_smooth, hf]
    exact DFunLike.congr_fun heq u
  constructor
  · intro u v huv
    apply Subtype.ext
    exact (h.smoothToL2_injective μ) (congrArg Subtype.val huv)
  · intro u
    have hzero : T (e.symm u.val) = B.smoothToSobolev (0 - 0) 0 := by
      apply f.injective
      rw [← hcomm, e.apply_symm_apply, show P.metricL2Extension h k u.val = 0 from
        u.property, map_zero, map_zero]
    -- Regularity returns a smooth vector representing this very L² kernel element.
    obtain ⟨v, ⟨hv, hPv⟩, _⟩ :=
      P.existsUnique_smooth_lift_of_isElliptic A B hP 0 (e.symm u.val) 0 hzero
    refine ⟨⟨v, hPv⟩, ?_⟩
    apply Subtype.ext
    change h.smoothToL2 μ v = u.val
    rw [← h.sobolevZeroEquivL2_smooth A v, hv]
    exact e.apply_symm_apply u.val

/-- The natural smooth versus integral L² kernel equivalence. -/
def metricL2KerEquiv (hP : P.IsElliptic) :
    P.toLinearMap.ker ≃ₗ[ℂ] (P.metricL2Extension h k).ker :=
  LinearEquiv.ofBijective (P.metricL2KerMap h k) (P.bijective_metricL2KerMap h k hP)

/-- Smooth outputs vanish in the actual L² cokernel. -/
theorem range_le_ker_metricL2Quotient :
    P.toLinearMap.range ≤
      ((P.metricL2Extension h k).range.mkQ.comp (k.smoothToL2 μ)).ker := by
  /- Write a smooth range vector as Pu. Its L² image is the bounded
  realization applied to the smooth image of u, so it belongs to the actual
  bounded range and its quotient class is zero. -/
  rintro v ⟨u, rfl⟩
  change (P.metricL2Extension h k).range.mkQ (k.smoothToL2 μ (P.toLinearMap u)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨h.smoothToL2 μ u, P.metricL2Extension_smooth h k u⟩

/-- The quotient map induced by the original smooth inclusion into integral L². -/
def metricL2CokerMap : (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) →ₗ[ℂ]
    (k.L2SectionSpace μ ⧸ (P.metricL2Extension h k).range) :=
  P.toLinearMap.range.liftQ
    ((P.metricL2Extension h k).range.mkQ.comp (k.smoothToL2 μ))
    (P.range_le_ker_metricL2Quotient h k)

/-- The induced smooth cokernel map is bijective for an elliptic order-zero PDO. -/
theorem bijective_metricL2CokerMap (hP : P.IsElliptic) :
    Function.Bijective (P.metricL2CokerMap h k) := by
  /- Transport to H⁰ to apply elliptic regularity.
  For injectivity, elliptic regularity upgrades any solution with smooth
  output to a smooth solution. For surjectivity, Fredholm closed range makes
  the quotient finite-dimensional and the dense smooth image fills it.
  The quotient is by the actual range, never its replacement by a closure. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  have hfExists : ∃ f : B.SobolevSpace (0 - 0) ≃L[ℂ] k.L2SectionSpace μ,
      ∀ v : smoothSections (n := n) (r := q) F,
        f (B.smoothToSobolev (0 - 0) v) = k.smoothToL2 μ v := by
    rw [sub_self]
    exact ⟨k.sobolevZeroEquivL2 (μ := μ) B, k.sobolevZeroEquivL2_smooth B⟩
  obtain ⟨f, hf⟩ := hfExists
  let T := P.sobolevExtension A B 0
  -- Extend the same-section identity to the full original completion by density.
  have hcomm (u : A.SobolevSpace 0) : P.metricL2Extension h k (e u) = f (T u) := by
    have heq : (P.metricL2Extension h k).comp e.toContinuousLinearMap =
        f.toContinuousLinearMap.comp T := by
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 0).equalizer
        ((P.metricL2Extension h k).comp e.toContinuousLinearMap).continuous
        (f.toContinuousLinearMap.comp T).continuous
      funext v
      change P.metricL2Extension h k (e (A.smoothToSobolev 0 v)) =
        f (T (A.smoothToSobolev 0 v))
      rw [P.sobolevExtension_smoothToSobolev, h.sobolevZeroEquivL2_smooth,
        P.metricL2Extension_smooth, hf]
    exact DFunLike.congr_fun heq u
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
    have hv : k.smoothToL2 μ v ∈ (P.metricL2Extension h k).range :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨u, hu⟩ := hv
    have hsolve : T (e.symm u) = B.smoothToSobolev (0 - 0) v := by
      apply f.injective
      rw [← hcomm, e.apply_symm_apply, hf]
      exact hu
    -- A completed preimage of this smooth output lifts to a genuine smooth preimage.
    obtain ⟨w, ⟨_, hPw⟩, _⟩ :=
      P.existsUnique_smooth_lift_of_isElliptic A B hP 0 (e.symm u) v hsolve
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hPw⟩
  · let H := k.L2SectionSpace μ
    let R : Submodule ℂ H := (P.metricL2Extension h k).range
    let C := H ⧸ R
    have hFred := P.isFredholm_metricL2Extension h k hP
    let : IsClosed (R : Set H) := hFred.isClosed_range
    let : FiniteDimensional ℂ C := hFred.finite_coker
    let proj : H →L[ℂ] C := ⟨R.mkQ, R.continuous_mkQ⟩
    -- The actual range is closed, so the dense smooth image fills its finite quotient.
    have hdense : DenseRange (fun v ↦ proj (k.smoothToL2 μ v)) :=
      R.mkQ_surjective.denseRange.comp (k.denseRange_smoothToL2 μ) proj.continuous
    have hclosed : IsClosed (Set.range (P.metricL2CokerMap h k)) :=
      (P.metricL2CokerMap h k).range.closed_of_finiteDimensional
    have hsubset : Set.range (fun v ↦ proj (k.smoothToL2 μ v)) ⊆
        Set.range (P.metricL2CokerMap h k) := by
      rintro _ ⟨v, rfl⟩
      exact ⟨P.toLinearMap.range.mkQ v, rfl⟩
    intro z
    exact hclosed.closure_subset_iff.mpr hsubset (hdense z)

/-- The Fredholm index of the integral realization equals the original smooth index. -/
theorem index_metricL2Extension (hP : P.IsElliptic) :
    (P.metricL2Extension h k).index = P.toLinearMap.index := by
  /- The preceding natural kernel and cokernel bijections identify the
  finite dimensions on both sides. Apply the kernel-minus-cokernel formula
  for each index; Fredholmness and ellipticity justify using these dimensions. -/
  let cokerEquiv := LinearEquiv.ofBijective (P.metricL2CokerMap h k)
    (P.bijective_metricL2CokerMap h k hP)
  -- Both equivalences are induced by the specified original smooth inclusions.
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    ← (P.metricL2KerEquiv h k hP).finrank_eq, ← cokerEquiv.finrank_eq]

end PseudodifferentialOperator

end AtiyahSinger
