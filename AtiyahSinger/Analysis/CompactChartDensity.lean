/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianPairing

/-!
# Comparing a positive density with volume on a compact chart support

Public module ID: M0348.

The actual chart pushforward of the supplied smooth positive measure has a density
bounded above and away from zero on each fixed compact support. Its defining
change-of-variables formula therefore compares integrals of all continuous
nonnegative functions with that support. No global compactness or orientation is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] in
/-- On a fixed compact chart support, the original positive density and coordinate volume
give uniform two-sided integral bounds for every continuous nonnegative scalar function. -/
theorem exists_integral_chart_bounds (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.source) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ f : M → ℝ,
      Continuous f → tsupport f ⊆ K → (∀ x, 0 ≤ f x) →
      a * (∫ z in c.target, f (c.symm z)) ≤ ∫ x, f x ∂μ ∧
        (∫ x, f x ∂μ) ≤ b * (∫ z in c.target, f (c.symm z)) := by
  classical
  obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c hc
  let L := c '' K
  have hL : IsCompact L := hK.image_of_continuousOn (c.continuousOn.mono hKc)
  have hLt : L ⊆ c.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hKc hx)
  -- Compactness supplies constants for this one density and this one support.
  obtain ⟨a, ha, hlow⟩ := hL.exists_forall_le' (hw.continuousOn.mono hLt)
    (fun z hz ↦ hwpos z (hLt hz))
  obtain ⟨B, hupper⟩ := (hL.image_of_continuousOn (hw.continuousOn.mono hLt)).bddAbove
  let b := max B 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨a, b, ha, hb, ?_⟩
  intro f hf hs hnonneg
  let F (z : EuclideanSpace ℝ (Fin n)) := f (c.symm z)
  have hFcont : ContinuousOn F c.target := hf.comp_continuousOn c.symm.continuousOn
  have hFzero (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) (hzL : z ∉ L) : F z = 0 := by
    change f (c.symm z) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hzL
    exact ⟨c.symm z, hs hx, c.right_inv hz⟩
  -- The zero extension has compact support in the same image of K, hence is integrable.
  let F₀ := c.target.indicator F
  have hFsupport : Function.support F₀ ⊆ L := by
    intro z hz
    by_cases hzt : z ∈ c.target
    · by_contra hzL
      exact hz (by simp only [F₀, indicator_of_mem hzt, hFzero z hzt hzL])
    · exact (hz (by simp only [F₀, indicator_of_notMem hzt])).elim
  have hFint : Integrable F (volume.restrict c.target) := by
    apply (integrable_indicator_iff c.open_target.measurableSet).mp
    apply (integrableOn_iff_integrable_of_support_subset hFsupport).mp
    have hi := (hFcont.mono hLt).integrableOn_compact (μ := volume) hL
    exact hi.congr_fun (fun z hz ↦ (indicator_of_mem (hLt hz) F).symm) hL.measurableSet
  have hpoint (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      a * F z ≤ w z * F z ∧ w z * F z ≤ b * F z := by
    by_cases hzL : z ∈ L
    · exact ⟨mul_le_mul_of_nonneg_right (hlow z hzL) (hnonneg _),
        mul_le_mul_of_nonneg_right ((hupper ⟨z, hzL, rfl⟩).trans (le_max_left _ _))
          (hnonneg _)⟩
    · simp only [hFzero z hz hzL, mul_zero, le_refl, and_self]
  have hweighted : Integrable (fun z ↦ w z * F z) (volume.restrict c.target) := by
    apply (hFint.const_mul b).mono'
      ((hw.continuousOn.mul hFcont).aestronglyMeasurable c.open_target.measurableSet)
    filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
    change |w z * F z| ≤ b * F z
    rw [abs_of_nonneg (mul_nonneg (hwpos z hz).le (hnonneg _))]
    exact (hpoint z hz).2
  -- The equality is the original chart density formula, with the original inverse chart.
  have htransport : (∫ x, f x ∂μ) = ∫ z in c.target, w z * F z := by
    have hFmeas : AEStronglyMeasurable F ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) :=
      AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
        (hFcont.aestronglyMeasurable c.open_target.measurableSet)
    have hFmap : AEStronglyMeasurable F (Measure.map c (μ.restrict c.source)) := by
      rw [hmap]
      exact hFmeas
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hw.continuousOn).aemeasurable
        c.open_target.measurableSet
    calc
      _ = ∫ x in c.source, f x ∂μ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        exact image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hKc (hs ht)))
      _ = ∫ x in c.source, F (c x) ∂μ := by
        apply setIntegral_congr_fun c.open_source.measurableSet
        intro x hx
        simp only [F, c.left_inv hx]
      _ = ∫ z, F z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet) hFmap).symm
      _ = ∫ z, F z ∂(volume.restrict c.target).withDensity
          (fun z ↦ ENNReal.ofReal (w z)) := by rw [hmap]
      _ = _ := by
        rw [integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        rw [ENNReal.toReal_ofReal (hwpos z hz).le, smul_eq_mul]
  rw [htransport]
  constructor
  · have hi := integral_mono_ae (hFint.const_mul a) hweighted (by
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (hpoint z hz).1)
    simpa only [integral_const_mul] using hi
  · have hi := integral_mono_ae hweighted (hFint.const_mul b) (by
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (hpoint z hz).2)
    simpa only [integral_const_mul] using hi

end AtiyahSinger
