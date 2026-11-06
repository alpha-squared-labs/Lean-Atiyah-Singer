/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductCutoffRealization

import AtiyahSinger.Analysis.FiniteAtlasProductCutoff
import all AtiyahSinger.Analysis.ProductSymbolCutoff

/-!
# Vertical graph norm bound for the actual low-cone cutoff error

Public module ID: M0794.

A measurable function of position and frequency whose spatial jets grow at most
linearly in the vertical frequency has its actual quantization bounded by the
original vertical graph norm.
For a fixed positive cutoff parameter, the difference between the full lifted
first-factor symbol and its product regularization is controlled by the input
L² norm and its original vertical first derivatives. Only spatial symbol
estimates are used. The lifted symbol need not be an isotropic joint symbol.

This is the low-cone part of the horizontal change-of-trivialization estimate.
It does not prove the high-cone conjugation estimate or a vanishing error in
the vertical graph norm as the parameter tends to zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

variable {n m r q : ℕ}

set_option maxHeartbeats 2400000 in
-- The exact spatial Schur realization is compared with all original vertical derivative norms.
/-- Linear vertical-frequency growth of spatial jets gives the vertical H1 quantization bound. -/
theorem exists_quantize_vertical_estimate_of_spatial_bounds
    (a : SymbolFunction (n + m) r q)
    (ham : StronglyMeasurable (Function.uncurry a))
    (has : ∀ ξ, ContDiff ℝ ∞ (fun x ↦ a x ξ))
    (K : Set (EuclideanSpace ℝ (Fin (n + m)))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0)
    (hder : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun y ↦ a y ξ) x‖ ≤
        C * (1 + ‖(EuclideanSpace.finAddEquivProd (n := n) (m := m) ξ).2‖)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q))),
        (∀ x, v x = quantize a u x) →
        ‖v.toLp 2‖ ^ 2 ≤ C * (‖u.toLp 2‖ ^ 2 +
          ∑ j : Fin m,
            ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))
              u).toLp 2‖ ^ 2) := by
  classical
  have hfinish {A B D G : ℝ} (hbound : A ≤ B * D) (henergy : D ^ 2 = G)
      (hA : 0 ≤ A) : A ^ 2 ≤ B ^ 2 * G := by
    calc
      A ^ 2 ≤ (B * D) ^ 2 := pow_le_pow_left₀ hA hbound 2
      _ = B ^ 2 * G := (mul_pow B D 2).trans (congrArg (fun t : ℝ ↦ B ^ 2 * t) henergy)
  let X := EuclideanSpace ℝ (Fin (n + m))
  let Y := EuclideanSpace ℝ (Fin m)
  let U := EuclideanSpace ℂ (Fin r)
  let V := EuclideanSpace ℂ (Fin q)
  let split : X ≃L[ℝ] EuclideanSpace ℝ (Fin n) × Y := EuclideanSpace.finAddEquivProd
  let p : X →L[ℝ] Y :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) Y).comp split.toContinuousLinearMap
  let w : X → ℝ := fun ξ ↦ (1 + ‖p ξ‖ ^ 2) ^ ((1 : ℝ) / 2)
  have hw : w.HasTemperateGrowth := by
    exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow Y ((1 : ℝ) / 2)).comp
      p.hasTemperateGrowth
  have hwpos (ξ : X) : 0 < w ξ := by dsimp [w]; positivity
  have hw2 (ξ : X) : w ξ ^ 2 = 1 + ‖p ξ‖ ^ 2 := by
    dsimp [w]
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    norm_num
  have hwone (ξ : X) : 1 ≤ w ξ := by
    have h := hw2 ξ
    nlinarith [sq_nonneg ‖p ξ‖, hwpos ξ]
  have hwp (ξ : X) : ‖p ξ‖ ≤ w ξ := by
    have h := hw2 ξ
    nlinarith [norm_nonneg (p ξ), hwpos ξ]
  have hweight (ξ : X) : 1 + ‖p ξ‖ ≤ 2 * w ξ := by
    linarith [hwone ξ, hwp ξ]
  -- Dividing by the vertical weight leaves all spatial jets uniformly bounded.
  let b : X → X → U →L[ℂ] V := fun x ξ ↦
    (w ξ)⁻¹ • a x ξ
  have hbs (ξ : X) : ContDiff ℝ ∞ (fun x ↦ b x ξ) :=
    (has ξ).const_smul _
  have hbK (x : X) (hx : x ∉ K) (ξ : X) : b x ξ = 0 := by
    simp only [b, hsupp x hx ξ, smul_zero]
  have hwi : Continuous (fun ξ : X ↦ (w ξ)⁻¹) :=
    hw.1.continuous.inv₀ (fun ξ ↦ ne_of_gt (hwpos ξ))
  have hbm : StronglyMeasurable (Function.uncurry b) :=
    (hwi.comp continuous_snd).stronglyMeasurable.smul ham
  have hbder (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun y ↦ b y ξ) x‖ ≤ C * (1 : ℝ) := by
    obtain ⟨C, hC, hb⟩ := hder i
    refine ⟨C * 2, by positivity, ?_⟩
    intro ξ x hx
    dsimp only [b]
    rw [iteratedFDeriv_const_smul_apply' ((has ξ).contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hwpos ξ).le)]
    calc
      _ ≤ (w ξ)⁻¹ * (C * (1 + ‖p ξ‖)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hwpos ξ).le)
        exact hb ξ x hx
      _ ≤ (w ξ)⁻¹ * (C * (2 * w ξ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hweight ξ) hC)
          (inv_nonneg.mpr (hwpos ξ).le)
      _ = C * 2 * 1 := by field_simp [ne_of_gt (hwpos ξ)]
  -- Spatial Fourier decay gives an L² operator for the normalized, non-isotropic amplitude.
  obtain ⟨C₀, hC₀, hF₀⟩ := spatial_fourier_decay_of_spatial_bounds b hbs K hK hbK
    (fun _ ↦ 1) (fun _ ↦ zero_le_one) hbder 0
  obtain ⟨C₁, hC₁, hF₁⟩ := spatial_fourier_decay_of_spatial_bounds b hbs K hK hbK
    (fun _ ↦ 1) (fun _ ↦ zero_le_one) hbder (n + m + 1)
  obtain ⟨C₂, hC₂, hV⟩ := hbder 0
  have hbval : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖b x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (0 : ℝ) := by
    refine ⟨C₂, hC₂, ?_⟩
    intro x ξ
    by_cases hx : x ∈ K
    · simpa only [norm_iteratedFDeriv_zero, Real.rpow_zero, mul_one] using hV ξ x hx
    · rw [hbK x hx ξ, norm_zero, Real.rpow_zero, mul_one]
      exact hC₂
  have hbFourier : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ ζ,
      ‖𝓕 (fun x ↦ b x ξ) ζ‖ ≤ C * (1 + ‖ξ‖) ^ (0 : ℝ) := by
    refine ⟨C₀, hC₀, ?_⟩
    intro ξ ζ
    simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hF₀ ξ ζ
  let d : X → ℝ := fun ζ ↦ C₁ * (1 + ‖ζ‖) ^ (-((n + m : ℕ) : ℝ) - 1)
  have hd : Continuous d := by
    have hd' : Continuous (fun ζ : X ↦ (1 + ‖ζ‖) ^ (-((n + m : ℕ) : ℝ) - 1)) := by
      apply Continuous.rpow_const (continuous_const.add continuous_norm)
      intro ζ
      left
      exact ne_of_gt (show 0 < 1 + ‖ζ‖ from by positivity)
    exact hd'.const_mul C₁
  have hd0 (ζ : X) : 0 ≤ d ζ := by dsimp [d]; positivity
  have hdi : Integrable d := by
    have hdim : (Module.finrank ℝ X : ℝ) < ((n + m : ℕ) : ℝ) + 1 := by simp [X]
    have hi := integrable_one_add_norm (E := X) (μ := volume) hdim
    simpa only [d, neg_add, sub_eq_add_neg] using hi.const_mul C₁
  have hde (ζ : X) : d (-ζ) = d ζ := by simp only [d, norm_neg]
  have hbound (ξ η : X) :
      ‖((1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - 0) / 2) * (1 + ‖η‖ ^ 2) ^ (-((0 : ℝ) / 2))) •
        𝓕 (fun x ↦ b x ((2 * Real.pi) • η)) (ξ - η)‖ ≤ d (ξ - η) := by
    have h := hF₁ ((2 * Real.pi) • η) (ξ - η)
    have hexp : -((n + m + 1 : ℕ) : ℝ) = -((n + m : ℕ) : ℝ) - 1 := by
      push_cast
      ring
    simpa only [sub_self, zero_div, neg_zero, Real.rpow_zero, one_mul, one_smul,
      mul_one, hexp, d] using h
  obtain ⟨T, hTnorm, hT⟩ := exists_quantize_sobolev_extension_of_spatial_bounds
    0 0 b hbm hbs hbval hbFourier K hK hbK d hd hd0 hdi hde
      (by simpa only [neg_div] using hbound)
  let cBound : ℝ := ∫ ξ : X, d ξ
  refine ⟨cBound ^ 2, sq_nonneg _, ?_⟩
  intro u v hv
  let uv : Lp U 2 (volume : Measure X) := u.toLp 2 volume
  let vv : Lp V 2 (volume : Measure X) := v.toLp 2 volume
  change ‖vv‖ ^ 2 ≤ cBound ^ 2 * (‖uv‖ ^ 2 + _)
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by dsimp [c]; positivity
  let w' : X → ℝ := fun ξ ↦ w (c • ξ)
  have hw' : w'.HasTemperateGrowth :=
    hw.comp (by fun_prop : (fun ξ : X ↦ c • ξ).HasTemperateGrowth)
  let f : 𝓢(X, U) := SchwartzMap.fourierMultiplierCLM U w' u
  let fv : Lp U 2 (volume : Measure X) := f.toLp 2 volume
  have hf (ξ : X) : fourierSG f ξ = w ξ • fourierSG u ξ := by
    dsimp only [fourierSG, f]
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.smulLeftCLM_apply_apply hw']
    dsimp only [w', c]
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hquantize (x : X) : quantize b f x = quantize (a) u x := by
    unfold quantize
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [hf]
    simp only [b, smul_apply, ContinuousLinearMap.map_smul_of_tower, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (hwpos ξ)), one_smul]
  have hzero {k : ℕ} (z : 𝓢(X, EuclideanSpace ℂ (Fin k))) :
      schwartzSobolevCoordinate 0 z = z.toLp 2 := by
    simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
      SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
  have hTv : T fv = vv := by
    change T (f.toLp 2 volume) = v.toLp 2 volume
    rw [← hzero f, ← hzero v]
    apply besselRealization_injective (n + m) q 0
    ext1 φ
    have ht := hT f φ
    simp only [sub_self] at ht
    rw [ht, besselRealization_schwartzSobolevCoordinate, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hquantize, hv]
  have hnorm : ‖vv‖ ≤ cBound * ‖fv‖ := by
    rw [← hTv]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _))
  -- The normalized input has exactly the L² energy plus the original vertical derivatives.
  let D (j : Fin m) : 𝓢(X, U) :=
    LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) u
  let F : 𝓢(X, U) := SchwartzMap.smulLeftCLM U w' (𝓕 u)
  have hL2 {k : ℕ} (z : 𝓢(X, EuclideanSpace ℂ (Fin k))) :
      ‖z.toLp 2‖ ^ 2 = ∫ ξ, ‖z ξ‖ ^ 2 := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (integral_nonneg fun ξ ↦ sq_nonneg _)
  have hFourierNorm (z : 𝓢(X, U)) :
      ‖z.toLp 2‖ ^ 2 = ∫ ξ, ‖𝓕 z ξ‖ ^ 2 := by
    rw [hL2, SchwartzMap.integral_norm_sq_fourier]
  have hfNorm : ‖fv‖ ^ 2 = ∫ ξ, ‖F ξ‖ ^ 2 := by
    change ‖f.toLp 2 volume‖ ^ 2 = _
    rw [hFourierNorm]
    simp only [f, SchwartzMap.fourierMultiplierCLM_apply,
      FourierTransform.fourier_fourierInv_eq, F]
  have hFder (j : Fin m) (ξ : X) :
      𝓕 (D j) ξ = (c * Complex.I) • ((ξ (Fin.natAdd n j) : ℝ) • 𝓕 u ξ) := by
    dsimp only [D]
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have hj : (fun η : X ↦ inner ℝ η
        (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))).HasTemperateGrowth := by
      fun_prop
    change (2 * Real.pi * Complex.I) •
      (SchwartzMap.smulLeftCLM U (fun η : X ↦
        inner ℝ η (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))) (𝓕 u)) ξ = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hj]
    have hcoord := EuclideanSpace.inner_single_right (Fin.natAdd n j) (1 : ℝ) ξ
    simp only [one_mul, conj_trivial] at hcoord
    rw [hcoord]
    simp only [c, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hcNorm : ‖(c * Complex.I : ℂ)‖ = c := by
    simp [c, abs_of_pos Real.pi_pos]
  have hderNorm (j : Fin m) (ξ : X) :
      ‖𝓕 (D j) ξ‖ ^ 2 = c ^ 2 * (ξ (Fin.natAdd n j)) ^ 2 * ‖𝓕 u ξ‖ ^ 2 := by
    rw [hFder, norm_smul, hcNorm, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hpoint (ξ : X) : ‖F ξ‖ ^ 2 = ‖𝓕 u ξ‖ ^ 2 + ∑ j : Fin m, ‖𝓕 (D j) ξ‖ ^ 2 := by
    have hpcoord (j : Fin m) : p ξ j = ξ (Fin.natAdd n j) := rfl
    have hpNorm : ‖p ξ‖ ^ 2 = ∑ j : Fin m, (ξ (Fin.natAdd n j)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [hpcoord]
    have hweight : w' ξ ^ 2 = 1 + c ^ 2 * ‖p ξ‖ ^ 2 := by
      change w (c • ξ) ^ 2 = _
      rw [hw2, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    dsimp only [F]
    rw [SchwartzMap.smulLeftCLM_apply_apply hw', norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hweight]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ ↦ hderNorm j ξ)
    rw [hsum, ← Finset.sum_mul, ← Finset.mul_sum, ← hpNorm]
    ring
  have henergy : ‖fv‖ ^ 2 = ‖uv‖ ^ 2 + ∑ j : Fin m, ‖(D j).toLp 2‖ ^ 2 := by
    have huNorm : ‖uv‖ ^ 2 = ∫ ξ, ‖𝓕 u ξ‖ ^ 2 := hFourierNorm u
    rw [hfNorm, huNorm]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ ↦ hFourierNorm (D j))
    rw [hsum]
    have hi (z : 𝓢(X, U)) : Integrable (fun ξ ↦ ‖𝓕 z ξ‖ ^ 2) :=
      ((𝓕 z).memLp 2).integrable_norm_pow (by norm_num)
    rw [← integral_finsetSum Finset.univ (fun j _ ↦ hi (D j)),
      ← integral_add (hi u) (integrable_finsetSum Finset.univ (fun j _ ↦ hi (D j)))]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  -- The established norm and energy identities suffice for this numerical conclusion.
  have hfinal := hfinish hnorm henergy (norm_nonneg _)
  have hDsum : (∑ j : Fin m, ‖(D j).toLp 2‖ ^ 2) =
      ∑ j : Fin m,
        ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) u).toLp 2‖ ^ 2 :=
    Finset.sum_congr rfl (fun _ _ ↦ rfl)
  exact hfinal.trans_eq
    (congrArg (fun t : ℝ ↦ cBound ^ 2 * (‖uv‖ ^ 2 + t)) hDsum)

set_option maxHeartbeats 800000 in
-- The proof retains the exact Fourier realization and all original vertical derivative norms.
/-- At a fixed positive parameter, the original cutoff error is bounded by vertical H1 energy. -/
theorem exists_productCutoffError_vertical_estimate (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q))),
        (∀ x, v x = quantize (productCutoffErrorSymbol a χ δ) u x) →
        ‖v.toLp 2‖ ^ 2 ≤ C * (‖u.toLp 2‖ ^ 2 +
          ∑ j : Fin m,
            ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))
              u).toLp 2‖ ^ 2) := by
  classical
  let X := EuclideanSpace ℝ (Fin (n + m))
  let split : X ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  -- The error is zero whenever the horizontal frequency dominates the scaled vertical one.
  have hcone (ξ : X) :
      (1 - productFrequencyCutoff δ ‖(split ξ).1‖ ‖(split ξ).2‖) *
        (1 + ‖(split ξ).1‖) ≤ (1 + δ) * (1 + ‖(split ξ).2‖) := by
    let t := 1 - productFrequencyCutoff δ ‖(split ξ).1‖ ‖(split ξ).2‖
    have ht := productCutoffError_scalar_bound δ ‖(split ξ).1‖ ‖(split ξ).2‖
      (norm_nonneg _) (norm_nonneg _)
    change t * (1 + ‖(split ξ).1‖) ≤ _
    by_cases ht0 : t = 0
    · rw [ht0, zero_mul]
      positivity
    have hr : ‖(split ξ).1‖ < δ * ‖(split ξ).2‖ := by
      by_contra h
      have heq := productFrequencyCutoff_eq_one_of_mul_le δ
        ‖(split ξ).1‖ ‖(split ξ).2‖ hδ (norm_nonneg _) (norm_nonneg _) (le_of_not_gt h)
      exact ht0 (by simp only [t, heq, sub_self])
    calc
      t * (1 + ‖(split ξ).1‖) ≤ 1 + ‖(split ξ).1‖ := by
        nlinarith [norm_nonneg (split ξ).1, ht.2.1]
      _ ≤ (1 + δ) * (1 + ‖(split ξ).2‖) := by
        nlinarith [norm_nonneg (split ξ).2]
  obtain ⟨K, hK, hsupp, hmeas, hsmooth, hder⟩ :=
    productCutoffError_spatial_data a ha haK χ hχ hχK
  -- All constants may depend on the fixed delta; the original quantization is unchanged.
  apply exists_quantize_vertical_estimate_of_spatial_bounds
    (productCutoffErrorSymbol a χ δ) (hmeas δ) (hsmooth δ) K hK (hsupp δ)
  intro i
  obtain ⟨C, hC, hb⟩ := hder i
  refine ⟨C * (1 + δ), by positivity, ?_⟩
  intro ξ x hx
  calc
    _ ≤ C * ((1 - productFrequencyCutoff δ ‖(split ξ).1‖ ‖(split ξ).2‖) *
        (1 + ‖(split ξ).1‖)) := hb δ ξ x hx
    _ ≤ C * ((1 + δ) * (1 + ‖(split ξ).2‖)) :=
      mul_le_mul_of_nonneg_left (hcone ξ) hC
    _ = C * (1 + δ) * (1 + ‖(split ξ).2‖) := (mul_assoc _ _ _).symm

end AtiyahSinger
