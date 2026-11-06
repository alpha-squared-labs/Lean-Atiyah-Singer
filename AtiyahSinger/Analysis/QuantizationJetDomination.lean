/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Quantization
public import AtiyahSinger.Analysis.SymbolQuotient
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local integrable domination of the actual quantization jets

Public module ID: M0910.

On a compact subset of an open symbol domain, every spatial jet of the original
Fourier integrand has a common integrable frequency majorant. Only local symbol
estimates are required; the symbol need not have compact spatial support.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 25

/-- Every spatial derivative of the original quantization integrand has an integrable
frequency majorant uniform on a specified compact subset of the open symbol domain. -/
theorem exists_integrable_bound_quantization_base_jet
    {n r q : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol U m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) (hK : IsCompact K)
    (k : ℕ) (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ∃ B : EuclideanSpace ℝ (Fin n) → ℝ, Integrable B ∧
      ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ k
          (fun y ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) •
            a y ξ (fourierSG u ξ)) x‖ ≤ B ξ := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  let H := V →L[ℂ] W
  -- The compact base window controls the phase and all its required spatial derivatives.
  have hphase : ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ : X,
      ‖iteratedFDeriv ℝ i
        (fun y ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))) x‖ ≤
          C * (1 + ‖ξ‖) ^ d := by
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨d, C, hC, hder⟩ :=
      Complex.hasTemperateGrowth_exp_mul_I.norm_iteratedFDeriv_le_uniform k
    refine ⟨d + k, C * (1 + max R 0) ^ d, by positivity, ?_⟩
    intro i hi x hx ξ
    let L : X →L[ℝ] ℝ := innerSL ℝ ξ
    let e : ℝ → ℂ := fun t ↦ Complex.exp (t * Complex.I)
    have he : ContDiff ℝ ∞ e := Complex.hasTemperateGrowth_exp_mul_I.1
    have hfun : (fun y : X ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))) = e ∘ L := by
      funext y
      simp [e, L, real_inner_comm, mul_comm]
    rw [hfun, L.iteratedFDeriv_comp_right he x (by simp)]
    have hbase : 1 + ‖L x‖ ≤ (1 + max R 0) * (1 + ‖ξ‖) := by
      have hnorm : ‖L x‖ ≤ ‖ξ‖ * max R 0 :=
        (norm_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_left
          ((hR x hx).trans (le_max_left _ _)) (norm_nonneg _))
      nlinarith [norm_nonneg ξ, le_max_right R 0]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i e (L x)‖ * ‖L‖ ^ i := by
        simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ i e (L x)) (fun _ ↦ L)
      _ ≤ (C * (1 + ‖L x‖) ^ d) * ‖L‖ ^ i := by
        gcongr
        exact hder i hi (L x)
      _ ≤ (C * ((1 + max R 0) * (1 + ‖ξ‖)) ^ d) * (1 + ‖ξ‖) ^ k := by
        gcongr
        calc
          ‖L‖ ^ i = ‖ξ‖ ^ i := by rw [innerSL_apply_norm]
          _ ≤ (1 + ‖ξ‖) ^ i := by gcongr; linarith [norm_nonneg ξ]
          _ ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hi
      _ = _ := by rw [mul_pow, pow_add]; ring
  -- Only zero frequency-derivative estimates of the same symbol are needed here.
  have hsymbol : ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun y ↦ a y ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    choose C hC hbound using fun i ↦ ha.2 K hKU hK i 0
    refine ⟨∑ j ∈ Finset.range (k + 1), C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
    intro i hi x hx ξ
    have hb := hbound i x hx ξ
    have hzero : (fun y ↦ iteratedFDeriv ℝ 0 (a y) ξ) =
        (continuousMultilinearCurryFin0 ℝ X H).symm ∘ (fun y ↦ a y ξ) := by
      funext y
      exact congrFun iteratedFDeriv_zero_eq_comp ξ
    simp only [symbolDerivative, hzero, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.cast_zero, sub_zero] at hb
    calc
      _ ≤ C i * (1 + ‖ξ‖) ^ m := hb
      _ ≤ (∑ j ∈ Finset.range (k + 1), C j) * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := by
        apply mul_le_mul
        · exact Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_range.mpr (by omega))
        · exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)
        · positivity
        · exact Finset.sum_nonneg (fun j _ ↦ hC j)
      _ = _ := by rw [Real.rpow_natCast]
  obtain ⟨d₀, A, hA, hphase⟩ := hphase
  obtain ⟨C₀, hC₀, hsymbol⟩ := hsymbol
  let d : ℕ := d₀ + ⌈m⌉₊
  let C : ℝ := 2 ^ k * A * C₀
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkernel (x : X) (hx : x ∈ K) (ξ : X) :
      ‖iteratedFDeriv ℝ k
        (fun y ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) • a y ξ) x‖ ≤
          C * (1 + ‖ξ‖) ^ d := by
    let e : X → ℂ := fun y ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))
    have he : ContDiff ℝ ∞ e := by
      simpa [e, Function.comp_def, real_inner_comm, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.1.comp (innerSL ℝ ξ).contDiff
    have hax : ContDiffOn ℝ ∞ (fun y ↦ a y ξ) U :=
      ha.1.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy ↦ ⟨hy, Set.mem_univ _⟩)
    have hproduct := norm_iteratedFDerivWithin_smul_le he.contDiffOn hax
      hU.uniqueDiffOn (hKU hx) (n := k) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at hproduct
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i e x‖ * ‖iteratedFDeriv ℝ (k - i) (fun y ↦ a y ξ) x‖ := hproduct
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          (A * (1 + ‖ξ‖) ^ d₀) * (C₀ * (1 + ‖ξ‖) ^ ⌈m⌉₊) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · exact hphase i (by simpa using hi) x hx ξ
        · exact hsymbol (k - i) (Nat.sub_le _ _) x hx ξ
      _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) *
          (A * C₀ * (1 + ‖ξ‖) ^ d) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [d]
        rw [pow_add]
        ring
      _ = C * (1 + ‖ξ‖) ^ d := by
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
        dsimp [C]
        ring
  -- SG's frequency rescaling preserves the actual Schwartz Fourier transform.
  have hπ : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let e : X ≃L[ℝ] X :=
    (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
  let v : 𝓢(X, V) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
  have hv (ξ : X) : v ξ = fourierSG u ξ := rfl
  let w : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ d
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  have hw0 (ξ : X) : 0 ≤ w ξ := by dsimp [w]; positivity
  have hint : Integrable (fun ξ : X ↦ w ξ * ‖fourierSG u ξ‖) := by
    simpa only [SchwartzMap.smulLeftCLM_apply_apply hw, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hw0 _), hv] using (SchwartzMap.smulLeftCLM V w v).integrable.norm
  have hweight : Integrable (fun ξ : X ↦ (1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) := by
    apply (hint.const_mul (2 ^ d)).mono'
      ((((continuous_const.add continuous_norm).pow d).mul v.continuous.norm).aestronglyMeasurable)
    filter_upwards [] with ξ
    change ‖(1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (2 * (1 + ‖ξ‖ ^ 2)) ^ d * ‖fourierSG u ξ‖ := by
        gcongr
        nlinarith [sq_nonneg (‖ξ‖ - 1)]
      _ = 2 ^ d * (w ξ * ‖fourierSG u ξ‖) := by simp only [w, mul_pow]; ring
  refine ⟨fun ξ ↦ C * ((1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖), hweight.const_mul C, ?_⟩
  intro x hx ξ
  -- Evaluation at this fixed Fourier vector is a continuous linear map of the matrix jet.
  let T : H →L[ℝ] W := (ContinuousLinearMap.apply ℂ W (fourierSG u ξ)).restrictScalars ℝ
  have hT : ‖T‖ ≤ ‖fourierSG u ξ‖ := by
    apply T.opNorm_le_bound (norm_nonneg _)
    intro b
    change ‖b (fourierSG u ξ)‖ ≤ ‖fourierSG u ξ‖ * ‖b‖
    simpa only [mul_comm] using b.le_opNorm (fourierSG u ξ)
  let g : X → H := fun y ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) • a y ξ
  have hg : ContDiffAt ℝ ∞ g x := by
    have he : ContDiff ℝ ∞ (fun y : X ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))) := by
      simpa [Function.comp_def, real_inner_comm, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.1.comp (innerSL ℝ ξ).contDiff
    have hax : ContDiffOn ℝ ∞ (fun y ↦ a y ξ) U :=
      ha.1.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy ↦ ⟨hy, Set.mem_univ _⟩)
    exact he.contDiffAt.smul (hax.contDiffAt (hU.mem_nhds (hKU hx)))
  change ‖iteratedFDeriv ℝ k (T ∘ g) x‖ ≤ _
  calc
    _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ k g x‖ := T.norm_iteratedFDeriv_comp_left hg (by simp)
    _ ≤ ‖fourierSG u ξ‖ * (C * (1 + ‖ξ‖) ^ d) :=
      mul_le_mul hT (hkernel x hx ξ) (norm_nonneg _) (norm_nonneg _)
    _ = C * ((1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) := by ring

end AtiyahSinger
