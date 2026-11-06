/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PeriodicFourierSymbol
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Exact action of the localized Fourier projection symbol

Public module ID: M0851.

The frequency integral of the specified local symbol equals the positive
Fourier series of the same localized input. A uniformly bounded absolute
periodization supplies the integrable majorant; Fourier inversion identifies
each convolution coefficient. This is the exact formula of ASI I, p.525.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap Topology

set_option maxHeartbeats 800000 in

/-- The exact localized frequency integral is the positive Fourier series of the original input. -/
theorem periodicProjectionSymbol_integral (ψ φ u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ ξ : ℝ, (Real.fourierChar (x * ξ) : ℂ) *
      periodicProjectionSymbol ψ φ x ξ * (𝓕 u) ξ) =
        ψ x * ∑' n : ℕ, (Real.fourierChar (x * (n : ℝ)) : ℂ) *
          (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ u)) (n : ℝ) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  -- Absolute periodization is continuous and periodic, hence uniformly bounded.
  let f : C(ℝ, ℝ) := ⟨fun t ↦ ‖(𝓕 φ) t‖, (𝓕 φ).continuous.norm⟩
  have hf : (f : ℝ → ℝ) =O[Filter.cocompact ℝ] (fun t : ℝ ↦ |t| ^ (-(2 : ℝ))) := by
    exact ((𝓕 φ).isBigO_cocompact_rpow (-2)).norm_left
  have hnormal (K : TopologicalSpace.Compacts ℝ) :
      Summable (fun n : ℤ ↦ ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
    exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      ((isBigO_norm_restrict_cocompact f (by norm_num) hf K).comp_tendsto
        Int.tendsto_coe_cofinite)
  have hCM : Summable (fun n : ℤ ↦ f.comp (ContinuousMap.addRight (n : ℝ))) :=
    ContinuousMap.summable_of_locally_summable_norm hnormal
  let H : C(ℝ, ℝ) := ∑' n : ℤ, f.comp (ContinuousMap.addRight (n : ℝ))
  have hH (t : ℝ) : H t = ∑' n : ℤ, ‖(𝓕 φ) (t + (n : ℝ))‖ := by
    rw [show H t = (∑' n : ℤ, f.comp (ContinuousMap.addRight (n : ℝ))) t from rfl,
      ← ContinuousMap.tsum_apply hCM]
    rfl
  have hperiod : Function.Periodic (H : ℝ → ℝ) 1 := by
    simpa only [H, zsmul_eq_mul, mul_one] using f.periodic_tsum_comp_add_zsmul 1
  obtain ⟨C, hC⟩ := (hperiod.isBounded_of_continuous one_ne_zero H.continuous).exists_norm_le
  have hInt (ξ : ℝ) : Summable (fun n : ℤ ↦ ‖(𝓕 φ) ((n : ℝ) - ξ)‖) := by
    have h := (ContinuousMap.hasSum_apply hCM.hasSum (-ξ)).summable
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, f,
      ContinuousMap.coe_mk, neg_add_eq_sub] using h
  have hNat (ξ : ℝ) : Summable (fun n : ℕ ↦ ‖(𝓕 φ) ((n : ℝ) - ξ)‖) := by
    simpa only [Function.comp_def, Int.cast_natCast] using
      (hInt ξ).comp_injective (i := fun n : ℕ ↦ (n : ℤ))
      Nat.cast_injective
  have hbound (ξ : ℝ) : (∑' n : ℕ, ‖(𝓕 φ) ((n : ℝ) - ξ)‖) ≤ |C| := by
    have h := tsum_comp_le_tsum_of_inj (hInt ξ) (fun _ ↦ norm_nonneg _)
      (i := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
    simp only [Function.comp_def, Int.cast_natCast] at h
    have hfull : (∑' n : ℤ, ‖(𝓕 φ) ((n : ℝ) - ξ)‖) = H (-ξ) := by
      rw [hH]
      simp only [neg_add_eq_sub]
    exact (h.trans_eq hfull).trans ((le_abs_self _).trans ((hC _ ⟨-ξ, rfl⟩).trans
      (le_abs_self C)))
  have hCMnat : Summable (fun n : ℕ ↦ f.comp (ContinuousMap.addRight (n : ℝ))) := by
    apply ContinuousMap.summable_of_locally_summable_norm
    intro K
    simpa only [Function.comp_def, Int.cast_natCast] using
      (hnormal K).comp_injective (i := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
  let Hnat : C(ℝ, ℝ) := ∑' n : ℕ, f.comp (ContinuousMap.addRight (n : ℝ))
  have hHnat (t : ℝ) : Hnat t = ∑' n : ℕ, ‖(𝓕 φ) (t + (n : ℝ))‖ := by
    rw [show Hnat t = (∑' n : ℕ, f.comp (ContinuousMap.addRight (n : ℝ))) t from rfl,
      ← ContinuousMap.tsum_apply hCMnat]
    rfl
  -- Fourier inversion gives the actual convolution coefficient of the same product φu.
  have hconvolution (ν : ℝ) :
      (∫ ξ : ℝ, (𝓕 φ) (ν - ξ) * (𝓕 u) ξ) =
        (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ u)) ν := by
    let g (t : ℝ) : ℂ := Real.fourierChar (-(t * ν))
    have hg : g.HasTemperateGrowth := by
      have h := Complex.hasTemperateGrowth_exp_mul_I.comp
        (show (fun t : ℝ ↦ 2 * Real.pi * (-(t * ν))).HasTemperateGrowth by fun_prop)
      simpa only [g, Real.fourierChar_apply, Function.comp_def] using h
    let v := SchwartzMap.smulLeftCLM ℂ g φ
    have hv (t : ℝ) : v t = (Real.fourierChar (-(t * ν)) : ℂ) * φ t :=
      SchwartzMap.smulLeftCLM_apply_apply hg φ t
    have hvF (ξ : ℝ) : (𝓕⁻ v) ξ = (𝓕 φ) (ν - ξ) := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
        Real.fourier_real_eq, SchwartzMap.fourier_coe, Real.fourier_real_eq]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv]
      simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
        ← Real.fourierChar.map_add_eq_mul]
      rw [show -(t * -ξ) + -(t * ν) = -(t * (ν - ξ)) by ring]
    calc
      _ = ∫ ξ : ℝ, (𝓕⁻ v) ξ * (𝓕 u) ξ := by simp only [hvF]
      _ = ∫ t : ℝ, v t * u t := by
        rw [SchwartzMap.integral_fourierInv_mul_eq, FourierTransform.fourierInv_fourier_eq]
      _ = _ := by
        rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
        apply integral_congr_ae
        filter_upwards with t
        simp only [hv, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply',
          Circle.smul_def, smul_eq_mul, mul_assoc]
  let F (n : ℕ) (ξ : ℝ) : ℂ := ψ x * (Real.fourierChar (x * (n : ℝ)) : ℂ) *
    ((𝓕 φ) ((n : ℝ) - ξ) * (𝓕 u) ξ)
  let B (n : ℕ) (ξ : ℝ) : ℝ := ‖ψ x‖ * ‖(𝓕 φ) ((n : ℝ) - ξ)‖ * ‖(𝓕 u) ξ‖
  have hnorm (n : ℕ) (ξ : ℝ) : ‖F n ξ‖ = B n ξ := by
    simp only [F, B, norm_mul, Circle.norm_coe, one_mul, mul_assoc]
  have hBsum (ξ : ℝ) : Summable (fun n : ℕ ↦ B n ξ) := by
    change Summable (fun n : ℕ ↦ ‖ψ x‖ * ‖(𝓕 φ) ((n : ℝ) - ξ)‖ * ‖(𝓕 u) ξ‖)
    exact ((hNat ξ).mul_left ‖ψ x‖).mul_right ‖(𝓕 u) ξ‖
  have hFsum (ξ : ℝ) : Summable (fun n : ℕ ↦ F n ξ) := by
    apply Summable.of_norm
    have heq : (fun n : ℕ ↦ ‖F n ξ‖) = (fun n : ℕ ↦ B n ξ) :=
      funext (fun n ↦ hnorm n ξ)
    rw [heq]
    exact hBsum ξ
  have hBval (ξ : ℝ) : (∑' n : ℕ, B n ξ) = ‖ψ x‖ * Hnat (-ξ) * ‖(𝓕 u) ξ‖ := by
    simp only [B, tsum_mul_left, tsum_mul_right, hHnat, neg_add_eq_sub]
  have hBint : Integrable (fun ξ : ℝ ↦ ∑' n : ℕ, B n ξ) := by
    have hmeas : Continuous (fun ξ : ℝ ↦ ∑' n : ℕ, B n ξ) := by
      simp_rw [hBval]
      exact (continuous_const.mul (Hnat.continuous.comp continuous_neg)).mul (𝓕 u).continuous.norm
    have hui : Integrable (fun ξ : ℝ ↦ (𝓕 u) ξ) (volume : Measure ℝ) := (𝓕 u).integrable
    apply (hui.norm.const_mul (‖ψ x‖ * |C|)).mono' hmeas.aestronglyMeasurable
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ ↦ by dsimp [B]; positivity)), hBval]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [hHnat]
    simpa only [neg_add_eq_sub] using hbound ξ
  have hseries (ξ : ℝ) : (∑' n : ℕ, F n ξ) =
      (Real.fourierChar (x * ξ) : ℂ) * periodicProjectionSymbol ψ φ x ξ * (𝓕 u) ξ := by
    simp only [F, periodicProjectionSymbol, ← tsum_mul_left, ← tsum_mul_right]
    apply tsum_congr
    intro n
    have hphase : (Real.fourierChar (x * ξ) : ℂ) *
        Real.fourierChar (x * ((n : ℝ) - ξ)) = Real.fourierChar (x * (n : ℝ)) := by
      rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul,
        show x * ξ + x * ((n : ℝ) - ξ) = x * (n : ℝ) by ring]
    calc
      _ = ψ x * ((Real.fourierChar (x * ξ) : ℂ) *
          Real.fourierChar (x * ((n : ℝ) - ξ))) *
            ((𝓕 φ) ((n : ℝ) - ξ) * (𝓕 u) ξ) := by rw [hphase]
      _ = _ := by ring
  have hint := hasSum_integral_of_dominated_convergence B
    (fun n ↦ (show Continuous (F n) by
      exact continuous_const.mul (((𝓕 φ).continuous.comp (continuous_const.sub continuous_id)).mul
        (𝓕 u).continuous)).aestronglyMeasurable)
    (fun n ↦ Filter.Eventually.of_forall (fun ξ ↦ (hnorm n ξ).le))
    (Filter.Eventually.of_forall hBsum) hBint
    (Filter.Eventually.of_forall (fun ξ ↦ (hseries ξ) ▸ (hFsum ξ).hasSum))
  rw [← hint.tsum_eq]
  simp only [F, integral_const_mul, hconvolution, mul_assoc, tsum_mul_left]

end AtiyahSinger
