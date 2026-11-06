/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The scalar principal term with the original fractional-power normalization

Public module ID: M0937.

The same constant that normalizes the CFC fractional-power integral normalizes
the positive scalar resolvent integral. The substitution `t = s⁻¹` is performed
on the scalar CFC kernel at `a⁻¹`, retaining the absolute Jacobian. Only `a > 0`
is needed; there is no uniform lower bound on the principal scalar.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set

/-- The positive scalar resolvent integral has the same normalization as the CFC power formula. -/
theorem scalar_resolvent_integral_normalization
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (a : ℝ) (ha : 0 < a) :
    let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    0 < C ∧
      IntegrableOn (fun s : ℝ ↦ s ^ (-p) / (a + s)) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (-p) / (a + s)) = a ^ (-p) * C := by
  let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  let f : ℝ → ℝ := fun t ↦ Real.rpowIntegrand₀₁ p t a⁻¹
  let g : ℝ → ℝ := fun s ↦ s ^ (-p) / (a + s)
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨hp, hp1⟩
  have hC : 0 < C := Real.integral_rpowIntegrand₀₁_one_pos hpI
  have hf : IntegrableOn f (Ioi 0) :=
    Real.integrableOn_rpowIntegrand₀₁_Ioi hpI (inv_nonneg.mpr ha.le)
  -- Inversion of the parameter turns the scalar CFC quotient into the original resolvent.
  have hratio (s : ℝ) (hs : 0 < s) : a⁻¹ / (s⁻¹ + a⁻¹) = s / (a + s) := by
    apply (div_eq_div_iff
      (add_pos (inv_pos.mpr hs) (inv_pos.mpr ha)).ne' (add_pos ha hs).ne').mpr
    rw [mul_add, mul_add, inv_mul_cancel₀ ha.ne', mul_inv_cancel₀ hs.ne', mul_comm a⁻¹ s]
  have hweight (s : ℝ) (hs : 0 < s) :
      s ^ ((-1 : ℝ) - 1) * (s⁻¹) ^ (p - 1) * s = s ^ (-p) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    calc
      s ^ ((-1 : ℝ) - 1) * s ^ (-(p - 1)) * s =
          s ^ (((-1 : ℝ) - 1 + -(p - 1)) + 1) := by
        rw [Real.rpow_add hs, Real.rpow_add hs, Real.rpow_one]
      _ = s ^ (-p) := by
        congr 1
        ring
  have hsame : (fun s : ℝ ↦ (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
      f (s ^ (-1 : ℝ))) =ᵐ[volume.restrict (Ioi 0)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [f, g]
    simp only [abs_neg, abs_one, one_mul, Real.rpow_neg_one, smul_eq_mul]
    rw [Real.rpowIntegrand₀₁_eq_pow_div hpI (inv_nonneg.mpr hs.le)
      (inv_nonneg.mpr ha.le)]
    calc
      s ^ ((-1 : ℝ) - 1) * ((s⁻¹) ^ (p - 1) * a⁻¹ / (s⁻¹ + a⁻¹)) =
          (s ^ ((-1 : ℝ) - 1) * (s⁻¹) ^ (p - 1) * s) / (a + s) := by
        rw [mul_div_assoc, hratio s hs]
        ring
      _ = s ^ (-p) / (a + s) := by rw [hweight s hs]
  -- The same Jacobian identity transports integrability and the exact scalar integral.
  have hweighted : IntegrableOn (fun s : ℝ ↦
      (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) • f (s ^ (-1 : ℝ))) (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff f (by norm_num : (-1 : ℝ) ≠ 0)).mpr hf
  refine ⟨hC, Integrable.congr hweighted hsame, ?_⟩
  calc
    (∫ s in Ioi (0 : ℝ), g s) = ∫ t in Ioi (0 : ℝ), f t :=
      (integral_congr_ae hsame).symm.trans
        (integral_comp_rpow_Ioi f (by norm_num : (-1 : ℝ) ≠ 0))
    _ = (a⁻¹) ^ p * C :=
      Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hpI (inv_nonneg.mpr ha.le)
    _ = a ^ (-p) * C := by rw [← Real.rpow_neg_eq_inv_rpow]

end AtiyahSinger
