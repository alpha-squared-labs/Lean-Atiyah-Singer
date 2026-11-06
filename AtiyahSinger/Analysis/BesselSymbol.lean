/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Quantization
public import AtiyahSinger.Analysis.SymbolQuotient

import AtiyahSinger.Analysis.SymbolCoordinateEstimates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Bessel symbols in the original Fourier normalization

Public module ID: M0320.

The symbol of the existing Bessel multiplier uses the frequency scaling from
SG quantization to mathlib Fourier transform. Uniform derivative bounds hold at
every real order. The exact multiplier and positive quadratic-form identities
provide the local input to real-order coordinate Sobolev estimates.
-/

@[expose] public noncomputable section

open Set Filter FourierTransform MeasureTheory
open scoped ContDiff SchwartzMap

namespace AtiyahSinger

set_option maxSynthPendingDepth 20 in
/-- Freezing the frequency scale bounds each derivative of the real Bessel weight. -/
private theorem norm_iteratedFDeriv_besselWeight_le (n : ℕ) (s c : ℝ) (hc : c ≠ 0)
    (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ j (fun η ↦ (1 + ‖c • η‖ ^ 2) ^ (s / 2)) ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (s - (j : ℝ)) := by
  let V := EuclideanSpace ℝ (Fin n)
  -- Regularize near the origin so the real-power profile is globally smooth and positive.
  let τ : ContDiffBump (0 : ℝ × V) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let b (z : ℝ × V) : ℝ := z.1 ^ 2 + ‖c • z.2‖ ^ 2 + τ z
  have hbpos (z : ℝ × V) : 0 < b z := by
    by_cases hz : z = 0
    · subst z
      have hτ : τ (0 : ℝ × V) = 1 :=
        τ.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [τ]))
      simp [b, hτ]
    · have hbase : 0 < z.1 ^ 2 + ‖c • z.2‖ ^ 2 := by
        by_contra h
        have hsum : z.1 ^ 2 + ‖c • z.2‖ ^ 2 = 0 :=
          le_antisymm (le_of_not_gt h) (by positivity)
        have hfirst : z.1 = 0 := by nlinarith [sq_nonneg ‖c • z.2‖]
        have hsecond : c • z.2 = 0 := by
          apply norm_eq_zero.mp
          nlinarith [sq_nonneg z.1, norm_nonneg (c • z.2)]
        have hz₂ : z.2 = 0 := (smul_eq_zero.mp hsecond).resolve_left hc
        exact hz (Prod.ext hfirst hz₂)
      exact add_pos_of_pos_of_nonneg hbase τ.nonneg
  have hb : ContDiff ℝ ∞ b := by
    have hlinear : ContDiff ℝ ∞ (fun z : ℝ × V ↦ c • z.2) :=
      contDiff_snd.const_smul c
    exact ((contDiff_fst.pow 2).add (hlinear.norm_sq ℝ)).add τ.contDiff
  let F (z : ℝ × V) : ℝ := b z ^ (s / 2)
  have hF : ContDiff ℝ ∞ F := hb.rpow_const_of_ne (fun z ↦ (hbpos z).ne')
  -- All derivatives of this profile are uniformly bounded on one fixed compact set.
  let K : Set (ℝ × V) := Icc 0 1 ×ˢ Metric.closedBall (0 : V) 1
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hD : Continuous (fun z : ℝ × V ↦ ‖iteratedFDeriv ℝ j F z‖) :=
    (hF.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hD.continuousOn).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ξ
  -- The normalized point has t + ‖y‖ = 1, lies in K, and avoids the regularizing bump.
  let R : ℝ := 1 + ‖ξ‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hRone : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg ξ)
  let t : ℝ := R⁻¹
  let y : V := R⁻¹ • ξ
  have ht : 0 < t := inv_pos.mpr hR
  have hy_norm : ‖y‖ = R⁻¹ * ‖ξ‖ := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have hty : t + ‖y‖ = 1 := by
    rw [hy_norm]
    change R⁻¹ + R⁻¹ * ‖ξ‖ = 1
    calc
      _ = R⁻¹ * R := by dsimp [R]; ring
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hpoint : (t, y) ∈ K := by
    refine ⟨⟨ht.le, inv_le_one_of_one_le₀ hRone⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hbig : (1 / 4 : ℝ) < ‖(t, y)‖ := by
    change (1 / 4 : ℝ) < max ‖t‖ ‖y‖
    have h₁ := le_max_left ‖t‖ ‖y‖
    have h₂ := le_max_right ‖t‖ ‖y‖
    rw [Real.norm_eq_abs, abs_of_pos ht] at h₁ h₂ ⊢
    linarith
  have hnear : (fun z : V ↦ F (t, z)) =ᶠ[nhds y]
      (fun z ↦ (t ^ 2 + ‖c • z‖ ^ 2) ^ (s / 2)) := by
    have hcont : ContinuousAt (fun z : V ↦ ‖(t, z)‖) y := by fun_prop
    filter_upwards [hcont.eventually (lt_mem_nhds hbig)] with z hz
    have hτ : τ (t, z) = 0 := τ.zero_of_le_dist (by simpa [τ] using hz.le)
    simp [F, b, hτ]
  have hslice : ‖iteratedFDeriv ℝ j
      (fun z : V ↦ (t ^ 2 + ‖c • z‖ ^ 2) ^ (s / 2)) y‖ ≤ max C 0 := by
    rw [← (hnear.iteratedFDeriv ℝ j).eq_of_nhds]
    have hrestrict := norm_mixed_iteratedFDeriv_le
      (fun a : ℝ ↦ fun z : V ↦ F (a, z)) hF 0 j t y
    have heq : Function.uncurry (fun a : ℝ ↦ fun z : V ↦ F (a, z)) = F := rfl
    rw [norm_iteratedFDeriv_zero, Nat.zero_add, heq] at hrestrict
    exact hrestrict.trans ((hC ⟨(t, y), hpoint, rfl⟩).trans (le_max_left C 0))
  -- Freeze R when differentiating: all derivatives now fall on a uniformly smooth profile.
  let f : V → ℝ := fun z ↦ (1 + ‖c • z‖ ^ 2) ^ (s / 2)
  let g : V → ℝ := fun z ↦ (t ^ 2 + ‖c • z‖ ^ 2) ^ (s / 2)
  have hscale (z : V) : f (R • z) = R ^ s * g z := by
    have hnorm : ‖c • (R • z)‖ = R * ‖c • z‖ := by
      rw [smul_comm c R, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hbase : 1 + ‖c • (R • z)‖ ^ 2 = R ^ 2 * (t ^ 2 + ‖c • z‖ ^ 2) := by
      rw [hnorm]
      dsimp [t]
      field_simp
    change _ = _
    dsimp [f, g]
    rw [hbase, Real.mul_rpow (sq_nonneg R) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
  have hder : iteratedFDeriv ℝ j (fun z ↦ f (R • z)) y =
      R ^ j • iteratedFDeriv ℝ j f ξ := by
    have hd := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
      (x := y) (mem_univ _) j
    simp only [preimage_univ, iteratedFDerivWithin_univ] at hd
    change iteratedFDeriv ℝ j (f ∘ e) y = _
    rw [hd]
    ext v
    change iteratedFDeriv ℝ j f (R • y) (fun i ↦ R • v i) = _
    have hRy : R • y = ξ := by simp [y, smul_smul, hR.ne']
    rw [hRy, ContinuousMultilinearMap.map_smul_univ]
    simp
  let L : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (R ^ s)
    (Real.rpow_pos_of_pos hR s).ne')
  have hder' : iteratedFDeriv ℝ j (fun z ↦ f (R • z)) y =
      R ^ s • iteratedFDeriv ℝ j g y := by
    simp_rw [hscale]
    exact L.iteratedFDeriv_comp_left
  have hnorm : R ^ j * ‖iteratedFDeriv ℝ j f ξ‖ =
      R ^ s * ‖iteratedFDeriv ℝ j g y‖ := by
    have hh := congrArg norm (hder.symm.trans hder')
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR j),
      abs_of_pos (Real.rpow_pos_of_pos hR s)] using hh
  have hbound : R ^ j * ‖iteratedFDeriv ℝ j f ξ‖ ≤ R ^ s * max C 0 := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hslice (Real.rpow_nonneg hR.le s)
  have hpower : R ^ j * (max C 0 * R ^ (s - (j : ℝ))) = R ^ s * max C 0 := by
    rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hR,
      show (j : ℝ) + (s - (j : ℝ)) = s by ring]
    ring
  rw [← hpower] at hbound
  exact (mul_le_mul_iff_right₀ (pow_pos hR j)).mp hbound

/-- The Bessel multiplier symbol, using SG's unnormalized frequency variable. -/
def besselSymbol (n r : ℕ) (s : ℝ) : SymbolFunction n r r :=
  fun _ ξ ↦ (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (s / 2) •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))

/-- The exact Bessel multiplier has its prescribed real symbol order. -/
theorem isSymbol_besselSymbol (n r : ℕ) (s : ℝ) :
    IsSymbol univ s (besselSymbol n r s) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : c ≠ 0 := by dsimp [c]; positivity
  let w : X → ℝ := fun ξ ↦ (1 + ‖c • ξ‖ ^ 2) ^ (s / 2)
  have hw : ContDiff ℝ ∞ w := by
    apply (contDiff_const.add ((contDiff_id.const_smul c).norm_sq ℝ)).rpow_const_of_ne
    intro ξ
    positivity
  let L : ℝ →L[ℝ] (V →L[ℂ] V) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℂ V)
  have heq : besselSymbol n r s = fun _ ξ ↦ L (w ξ) := rfl
  rw [heq]
  refine ⟨(L.contDiff.comp (hw.comp contDiff_snd)).contDiffOn, ?_⟩
  intro K hKU hK i j
  obtain ⟨C, hC, hbound⟩ := norm_iteratedFDeriv_besselWeight_le n s c hc j
  cases i with
  | zero =>
    refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, fun x hx ξ ↦ ?_⟩
    change ‖iteratedFDeriv ℝ 0 (fun _ : X ↦ iteratedFDeriv ℝ j (L ∘ w) ξ) x‖ ≤ _
    rw [norm_iteratedFDeriv_zero]
    have hL := L.norm_iteratedFDeriv_comp_left hw.contDiffAt (n := j) (x := ξ) (by simp)
    exact hL.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound ξ) (norm_nonneg L))
  | succ i =>
    refine ⟨0, le_rfl, fun x hx ξ ↦ ?_⟩
    change ‖iteratedFDeriv ℝ (i + 1)
      (fun _ : X ↦ iteratedFDeriv ℝ j (L ∘ w) ξ) x‖ ≤ _
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i)]
    simp

/-- SG quantization of the Bessel symbol is the already defined Schwartz multiplier. -/
theorem quantize_besselSymbol (n r : ℕ) (s : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (besselSymbol n r s) u x =
      SchwartzMap.fourierMultiplierCLM (EuclideanSpace ℂ (Fin r))
        (fun ξ : EuclideanSpace ℝ (Fin n) ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)) u x := by
  let w : EuclideanSpace ℝ (Fin n) → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  dsimp only [w] at hw
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [quantize_rescaled, SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [besselSymbol, inv_smul_smul₀ hc, smul_apply, ContinuousLinearMap.id_apply,
    SchwartzMap.smulLeftCLM_apply_apply hw]
  rw [real_inner_comm ξ x]
  congr 2
  push_cast
  ring

/-- The squared Bessel norm is the positive quadratic form of the order-2s symbol. -/
theorem norm_schwartzSobolevCoordinate_sq_eq_integral (n r : ℕ) (s : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ((‖schwartzSobolevCoordinate s u‖ ^ 2 : ℝ) : ℂ) =
      ∫ x, inner ℂ (u x) (quantize (besselSymbol n r (2 * s)) u x) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let w (t : ℝ) : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (t / 2)
  have hw (t : ℝ) : (w t).HasTemperateGrowth := by dsimp [w]; fun_prop
  let v := SchwartzMap.fourierMultiplierCLM V (w (2 * s)) u
  have hweights : w (-s) * w (2 * s) = w s := by
    funext ξ
    dsimp [w]
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hcoordinate : schwartzSobolevCoordinate (-s) v = schwartzSobolevCoordinate s u := by
    change (SchwartzMap.fourierMultiplierCLM V (w (-s))
      (SchwartzMap.fourierMultiplierCLM V (w (2 * s)) u)).toLp 2 = _
    rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (hw (-s)) (hw (2 * s)),
      hweights]
    rfl
  have hpair := sobolev_pairing_schwartz s u v
  rw [hcoordinate, inner_self_eq_norm_sq_to_K] at hpair
  rw [Complex.ofReal_pow]
  exact hpair.trans (integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ by
    dsimp only
    rw [quantize_besselSymbol])))

end AtiyahSinger
