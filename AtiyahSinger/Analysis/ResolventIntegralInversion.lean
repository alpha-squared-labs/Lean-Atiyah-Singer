/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Inversion of the positive resolvent parameter

Public module ID: M0925.

The substitution `t = s⁻¹` sends the fractional-power kernel for the same bounded
operator `B` to the parameter kernel `B * (1 + s • B)⁻¹`. The absolute Jacobian
is `s⁻²`, which combines with the original scalar weight and the resolvent
rescaling to give `s⁻ᵖ`.

The algebraic rescaling uses only that a nonzero real scalar is a unit. It never
requires `B` to be a unit. Both the equality of Lebesgue integrals and equivalence
of integrability are established, independently of a normalization formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set

/-- Inverting the positive parameter preserves the original resolvent integral and integrability. -/
theorem resolvent_integral_inv_parameter
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (p : ℝ) :
    (IntegrableOn (fun t : ℝ ↦ t ^ (p - 1) •
        (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))) (Ioi 0) ↔
      IntegrableOn (fun s : ℝ ↦ s ^ (-p) •
        (B * Ring.inverse ((1 : H →L[ℂ] H) + s • B))) (Ioi 0)) ∧
    (∫ t in Ioi (0 : ℝ), t ^ (p - 1) •
        (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))) =
      ∫ s in Ioi (0 : ℝ), s ^ (-p) •
        (B * Ring.inverse ((1 : H →L[ℂ] H) + s • B)) := by
  let f : ℝ → (H →L[ℂ] H) := fun t ↦ t ^ (p - 1) •
    (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))
  let g : ℝ → (H →L[ℂ] H) := fun s ↦ s ^ (-p) •
    (B * Ring.inverse ((1 : H →L[ℂ] H) + s • B))
  -- Scalar rescaling of the total ring inverse does not assume the operator is invertible.
  have hscale (A : H →L[ℂ] H) (c : ℝ) (hc : c ≠ 0) :
      Ring.inverse (c • A) = c⁻¹ • Ring.inverse A := by
    have hunit : IsUnit (algebraMap ℝ (H →L[ℂ] H) c) :=
      (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ (H →L[ℂ] H))
    calc
      Ring.inverse (c • A) =
          Ring.inverse (algebraMap ℝ (H →L[ℂ] H) c * A) := by
        rw [Algebra.smul_def]
      _ = Ring.inverse A * Ring.inverse (algebraMap ℝ (H →L[ℂ] H) c) :=
        Ring.inverse_mul (Or.inl hunit)
      _ = c⁻¹ • Ring.inverse A := by
        rw [← map_inv_eq_ringInverse_map (algebraMap ℝ (H →L[ℂ] H)) c,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hkernel (s : ℝ) (hs : 0 < s) :
      B * Ring.inverse (s⁻¹ • (1 : H →L[ℂ] H) + B) =
        s • (B * Ring.inverse ((1 : H →L[ℂ] H) + s • B)) := by
    have hden : s⁻¹ • (1 : H →L[ℂ] H) + B =
        s⁻¹ • ((1 : H →L[ℂ] H) + s • B) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [hden, hscale _ _ (inv_ne_zero hs.ne'), inv_inv, mul_smul_comm]
  -- Combine the absolute Jacobian, the original weight, and the resolvent's scalar factor.
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
    simp only [abs_neg, abs_one, one_mul, Real.rpow_neg_one]
    rw [hkernel s hs, smul_smul, smul_smul, hweight s hs]
  -- Apply the same change of variables to integrability and to the Bochner integral.
  change (IntegrableOn f (Ioi 0) ↔ IntegrableOn g (Ioi 0)) ∧
    (∫ t in Ioi (0 : ℝ), f t) = ∫ s in Ioi (0 : ℝ), g s
  constructor
  · exact (integrableOn_Ioi_comp_rpow_iff f
      (by norm_num : (-1 : ℝ) ≠ 0)).symm.trans (integrable_congr hsame)
  · exact (integral_comp_rpow_Ioi f (by norm_num : (-1 : ℝ) ≠ 0)).symm.trans
      (integral_congr_ae hsame)

end AtiyahSinger
