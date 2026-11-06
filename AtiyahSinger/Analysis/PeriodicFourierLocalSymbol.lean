/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PeriodicFourierProjection
public import AtiyahSinger.Analysis.SchwartzKernel
public import AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Local Fourier formulas for the circle projection

Public module ID: M0852.

Poisson summation identifies the full translated lattice with the translated
spatial cutoff. Together with the half-lattice estimates this recovers the
positive and negative principal branches in ASI I, section 8, p.525.
The Fourier convention in this module is mathlib's period-one convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap

/-- The shifted Poisson formula retains the exact modulation and translation phases. -/
theorem fourierPeriodization_eq (φ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    (∑' n : ℤ, (Real.fourierChar (x * ((n : ℝ) - ξ)) : ℂ) *
      (𝓕 φ) ((n : ℝ) - ξ)) =
        ∑' k : ℤ, (Real.fourierChar ((k : ℝ) * ξ) : ℂ) * φ (x + (k : ℝ)) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  -- Translate the original cutoff and modulate it before applying the same Poisson theorem.
  let g (t : ℝ) : ℂ := Real.fourierChar (t * ξ)
  have hg : g.HasTemperateGrowth := by
    have h := Complex.hasTemperateGrowth_exp_mul_I.comp
      (show (fun t : ℝ ↦ 2 * Real.pi * (t * ξ)).HasTemperateGrowth by fun_prop)
    simpa only [g, Real.fourierChar_apply, Function.comp_def] using h
  let h : 𝓢(ℝ, ℂ) := SchwartzMap.smulLeftCLM ℂ g (φ.compSubConstCLM ℂ (-x))
  have hval (t : ℝ) : h t = (Real.fourierChar (t * ξ) : ℂ) * φ (t + x) := by
    simp only [h, SchwartzMap.smulLeftCLM_apply_apply hg,
      SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, g]
  have htransform (ν : ℝ) :
      (𝓕 h) ν = (Real.fourierChar (x * (ν - ξ)) : ℂ) * (𝓕 φ) (ν - ξ) := by
    -- Modulation shifts the same frequency; right translation contributes its positive phase.
    have hmod : (𝓕 h) ν = 𝓕 (fun t : ℝ ↦ φ (t + x)) (ν - ξ) := by
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq, Real.fourier_real_eq]
      apply integral_congr_ae
      filter_upwards with t
      rw [hval]
      simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
        ← Real.fourierChar.map_add_eq_mul]
      rw [show -(t * ν) + t * ξ = -(t * (ν - ξ)) by ring]
    rw [hmod]
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq, Real.fourier_real_eq]
    have hs := congrFun (Fourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (φ : ℝ → ℂ) x) (ν - ξ)
    simpa only [Fourier.fourierIntegral_def, Function.comp_apply,
      Circle.smul_def, smul_eq_mul] using hs
  have hP := h.tsum_eq_tsum_fourier 0
  have hzero (n : ℤ) : _root_.fourier n ((0 : ℝ) : UnitAddCircle) = 1 :=
    fourier_eval_zero n
  simpa only [zero_add, hval, htransform, hzero,
    mul_one, add_comm x] using hP.symm

/-- The exact local scalar symbol of the positive Fourier projection, with period one. -/
def periodicProjectionSymbol (ψ φ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : ℂ :=
  ∑' n : ℕ, ψ x * (Real.fourierChar (x * ((n : ℝ) - ξ)) : ℂ) *
    (𝓕 φ) ((n : ℝ) - ξ)

/-- The localized projection symbol has its two principal branches with rapid jet remainders. -/
theorem periodicProjectionSymbol_estimates (ψ φ : 𝓢(ℝ, ℂ))
    (hsep : ∀ (x : ℝ) (n : ℤ), n ≠ 0 → ψ x * φ (x + (n : ℝ)) = 0) :
    ContDiff ℝ ∞ (Function.uncurry (periodicProjectionSymbol ψ φ)) ∧
      ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ,
        (z.2 ≤ 0 → (1 + |z.2|) ^ N *
          ‖iteratedFDeriv ℝ k (Function.uncurry (periodicProjectionSymbol ψ φ)) z‖ ≤ C) ∧
        (0 ≤ z.2 → (1 + |z.2|) ^ N *
          ‖iteratedFDeriv ℝ k (fun z : ℝ × ℝ ↦
            periodicProjectionSymbol ψ φ z.1 z.2 - ψ z.1 * φ z.1) z‖ ≤ C) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  -- The existing tensor construction and a temperate phase give one actual Schwartz kernel.
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toContinuousLinearEquiv
  let ψ₁ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm ψ
  let φ₁ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm (𝓕 φ)
  let H := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (e.prodCongr e)
    (schwartzTensor ψ₁ φ₁)
  let phase (z : (ℝ × ℝ)) : ℂ := Real.fourierChar (z.1 * z.2)
  have hphase : phase.HasTemperateGrowth := by
    have hf : (fun z : (ℝ × ℝ) ↦ z.1).HasTemperateGrowth :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
    have hs : (fun z : (ℝ × ℝ) ↦ z.2).HasTemperateGrowth :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
    have h := Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const (E := (ℝ × ℝ)) (2 * Real.pi)).mul (hf.mul hs))
    simpa only [phase, Real.fourierChar_apply, Function.comp_def, Pi.mul_apply] using h
  let h : 𝓢((ℝ × ℝ), ℂ) := SchwartzMap.smulLeftCLM ℂ phase H
  have hval (z : (ℝ × ℝ)) :
      h z = ψ z.1 * (Real.fourierChar (z.1 * z.2) : ℂ) * (𝓕 φ) z.2 := by
    rw [show h z = phase z * H z from SchwartzMap.smulLeftCLM_apply_apply hphase H z]
    change phase z * schwartzTensor ψ₁ φ₁ (e z.1, e z.2) = _
    rw [schwartzTensor_apply]
    change phase z * (ψ (e.symm (e z.1)) * (𝓕 φ) (e.symm (e z.2))) = _
    simp only [ContinuousLinearEquiv.symm_apply_apply, phase]
    ring
  let L : (ℝ × ℝ) ≃ₗᵢ[ℝ] (ℝ × ℝ) :=
    { toLinearEquiv := (LinearEquiv.refl ℝ ℝ).prodCongr
        (LinearIsometryEquiv.neg ℝ (E := ℝ)).toLinearEquiv
      norm_map' := by
        intro z
        change ‖(z.1, -z.2)‖ = ‖z‖
        simp only [Prod.norm_def, norm_neg] }
  have hL (z : ℝ × ℝ) : L z = (z.1, -z.2) := rfl
  let hneg := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.toContinuousLinearEquiv h
  have hnegVal (z : ℝ × ℝ) : hneg z = h (L z) := rfl
  let A (z : (ℝ × ℝ)) := ∑' n : ℕ, h (z + (0, (n : ℝ)))
  let B (z : (ℝ × ℝ)) := ∑' n : ℕ, hneg (z + (0, (n : ℝ)))
  obtain ⟨hA, hAdecay⟩ := schwartz_halfPeriodization_properties h
  obtain ⟨hB, hBdecay⟩ := schwartz_halfPeriodization_properties hneg
  have hp : Function.uncurry (periodicProjectionSymbol ψ φ) = A ∘ L := by
    funext z
    apply tsum_congr
    intro n
    rw [hval]
    rw [hL]
    simp only [Prod.mk_add_mk, add_zero]
    rw [neg_add_eq_sub]
  have hpSmooth : ContDiff ℝ ∞ (Function.uncurry (periodicProjectionSymbol ψ φ)) := by
    rw [hp]
    exact hA.comp L.toContinuousLinearEquiv.contDiff
  -- Split the integer lattice, using actual absolute convergence of the same Fourier cutoff.
  have hsum (x ξ : ℝ) : Summable (fun n : ℤ ↦ h (x, (n : ℝ) - ξ)) := by
    let F := (𝓕 φ).compSubConstCLM ℂ ξ
    have hF : Summable (fun n : ℤ ↦ F (n : ℝ)) :=
      summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
        ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
    apply Summable.of_norm
    simpa only [hval, norm_mul, Circle.norm_coe, mul_one, F,
      SchwartzMap.compSubConstCLM_apply] using hF.norm.mul_left ‖ψ x‖
  have hparts (x ξ : ℝ) : periodicProjectionSymbol ψ φ x ξ + B (x, ξ + 1) = ψ x * φ x := by
    have hnat : Summable (fun n : ℕ ↦ h (x, ((n : ℤ) : ℝ) - ξ)) :=
      (hsum x ξ).comp_injective Nat.cast_injective
    have hnegInj : Function.Injective (fun n : ℕ ↦ -((n : ℤ) + 1)) := by
      intro i j hij
      exact Nat.cast_injective (add_right_cancel (neg_injective hij))
    have hnegNat := (hsum x ξ).comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) hnegInj
    calc
      _ = ∑' n : ℤ, h (x, (n : ℝ) - ξ) := by
        rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ ↦ h (x, (n : ℝ) - ξ)) hnat hnegNat]
        congr 1
        · apply tsum_congr
          intro n
          rw [hval]
          simp only [Int.cast_natCast]
        · apply tsum_congr
          intro n
          rw [hnegVal, hL]
          simp only [Prod.mk_add_mk, add_zero]
          simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
          congr 2
          ring
      _ = ψ x * ∑' n : ℤ, (Real.fourierChar (x * ((n : ℝ) - ξ)) : ℂ) *
          (𝓕 φ) ((n : ℝ) - ξ) := by simp_rw [hval, mul_assoc, tsum_mul_left]
      _ = ψ x * ∑' n : ℤ, (Real.fourierChar ((n : ℝ) * ξ) : ℂ) * φ (x + (n : ℝ)) := by
        rw [fourierPeriodization_eq]
      _ = ψ x * φ x := by
        rw [← tsum_mul_left]
        rw [tsum_eq_single 0]
        · simp
        · intro n hn
          calc
            _ = (Real.fourierChar ((n : ℝ) * ξ) : ℂ) * (ψ x * φ (x + (n : ℝ))) := by ring
            _ = 0 := by rw [hsep x n hn, mul_zero]
  have hrem : (fun z : (ℝ × ℝ) ↦ periodicProjectionSymbol ψ φ z.1 z.2 - ψ z.1 * φ z.1) =
      fun z : (ℝ × ℝ) ↦ -B (z + (0, 1)) := by
    funext z
    have h := hparts z.1 z.2
    rw [show z + (0, 1) = (z.1, z.2 + 1) from Prod.ext (add_zero z.1) rfl]
    change periodicProjectionSymbol ψ φ z.1 z.2 - ψ z.1 * φ z.1 = -B (z.1, z.2 + 1)
    linear_combination h
  refine ⟨hpSmooth, ?_⟩
  intro k N
  obtain ⟨C₁, hC₁, hd₁⟩ := hAdecay k N
  obtain ⟨C₂, hC₂, hd₂⟩ := hBdecay k N
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun z ↦ ⟨?_, ?_⟩⟩
  · intro hz
    rw [hp, L.norm_iteratedFDeriv_comp_right, abs_of_nonpos hz]
    exact (hd₁ (L z) (by change 0 ≤ -z.2; linarith)).trans (le_add_of_nonneg_right hC₂)
  · intro hz
    rw [hrem]
    have hnorm : ‖iteratedFDeriv ℝ k (fun z : (ℝ × ℝ) ↦ -B (z + (0, 1))) z‖ =
        ‖iteratedFDeriv ℝ k B (z + (0, 1))‖ := by
      change ‖iteratedFDeriv ℝ k ((LinearIsometryEquiv.neg ℝ (E := ℂ)) ∘
        fun z : (ℝ × ℝ) ↦ B (z + (0, 1))) z‖ = _
      rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, iteratedFDeriv_comp_add_right]
    rw [hnorm, abs_of_nonneg hz]
    have hdec := hd₂ (z + (0, 1)) (by change 0 ≤ z.2 + 1; linarith)
    apply (le_trans ?_ hdec).trans (le_add_of_nonneg_left hC₁)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_pow_left₀ (by linarith)
    change 1 + z.2 ≤ 1 + (z.2 + 1)
    linarith

end AtiyahSinger
