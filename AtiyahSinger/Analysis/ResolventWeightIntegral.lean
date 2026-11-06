/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The joint weight integral for fractional resolvents

Public module ID: M0926.

For `0 < p < 1`, integration of the joint frequency and resolvent weight
`t ^ (-p) * (ρ ^ 2 + t) ^ (-1 - k / 2)` has the exact order `ρ ^ (-2 * p - k)`.
The coefficient is the convergent integral at `ρ = 1`, and is independent of `ρ`.

This is an elementary scalar input for A09's parameter-dependent symbol
estimates. It asserts no estimate for a pseudodifferential operator or its
derivatives. The proof splits the normalized integral at one, and then uses
the substitution `t = ρ ^ 2 * u` in the original Lebesgue integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set

/-- The scalar fractional-resolvent weight is integrable and has its exact scaling order.
The nonnegative coefficient is the displayed normalized integral, independent of `ρ`. -/
theorem resolvent_weight_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    let C : ℝ := ∫ u in Ioi (0 : ℝ),
      u ^ (-p) * (1 + u) ^ (-1 - (k : ℝ) / 2)
    0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun t : ℝ ↦ t ^ (-p) * (ρ ^ 2 + t) ^ (-1 - (k : ℝ) / 2))
        (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t ^ (-p) * (ρ ^ 2 + t) ^ (-1 - (k : ℝ) / 2)) =
        C * ρ ^ (-2 * p - (k : ℝ)) := by
  let d : ℝ := -1 - (k : ℝ) / 2
  let F : ℝ → ℝ := fun u ↦ u ^ (-p) * (1 + u) ^ d
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : d ≤ 0 := by
    dsimp [d]
    linarith
  have hFnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ F u :=
    mul_nonneg (Real.rpow_nonneg hu.le _)
      (Real.rpow_nonneg (by linarith : 0 ≤ 1 + u) _)
  have hFcontinuous : ContinuousOn F (Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun u hu ↦ Or.inl (ne_of_gt hu))
    · exact (continuousOn_const.add continuousOn_id).rpow_const
        (fun u hu ↦ Or.inl (ne_of_gt (add_pos zero_lt_one (show 0 < u from hu))))
  -- Near zero, the denominator factor is at most one, and -p is greater than -1.
  have hsmall : IntegrableOn F (Ioo 0 1) := by
    have hmajorant : IntegrableOn (fun u : ℝ ↦ u ^ (-p)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
    apply hmajorant.mono'
      ((hFcontinuous.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo)
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu ↦ ?_
    rw [Real.norm_of_nonneg (hFnonneg u hu.1)]
    calc
      F u = u ^ (-p) * (1 + u) ^ d := rfl
      _ ≤ u ^ (-p) * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hu.1]) hd)
        (Real.rpow_nonneg hu.1.le _)
      _ = u ^ (-p) := mul_one _
  -- At infinity, the combined exponent -p-1-k/2 is strictly less than -1.
  have hlarge : IntegrableOn F (Ioi 1) := by
    have hdecay : -p + d < -1 := by
      dsimp [d]
      linarith
    have hmajorant : IntegrableOn (fun u : ℝ ↦ u ^ (-p + d)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt hdecay zero_lt_one
    apply hmajorant.mono'
      ((hFcontinuous.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi)
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ ?_
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [Real.norm_of_nonneg (hFnonneg u hu0)]
    calc
      F u = u ^ (-p) * (1 + u) ^ d := rfl
      _ ≤ u ^ (-p) * u ^ d := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hu0 (by linarith) hd)
        (Real.rpow_nonneg hu0.le _)
      _ = u ^ (-p + d) := (Real.rpow_add hu0 (-p) d).symm
  have hnormalized : IntegrableOn F (Ioi 0) := by
    have hsmall' : IntegrableOn F (Ioc 0 1) :=
      hsmall.congr_set_ae Ioo_ae_eq_Ioc.symm
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hsmall'.union hlarge
  have hcoefficient : 0 ≤ ∫ u in Ioi (0 : ℝ), F u :=
    setIntegral_nonneg measurableSet_Ioi (fun u hu ↦ hFnonneg u hu)
  refine ⟨hcoefficient, ?_⟩
  intro ρ hρ
  let f : ℝ → ℝ := fun t ↦ t ^ (-p) * (ρ ^ 2 + t) ^ d
  have hρsq : 0 < ρ ^ 2 := pow_pos hρ 2
  -- The same change of variables factors the original integrand at every positive point.
  have hscale (u : ℝ) (hu : 0 < u) :
      f (ρ ^ 2 * u) = (ρ ^ 2) ^ (-p + d) * F u := by
    dsimp [f, F]
    rw [show ρ ^ 2 + ρ ^ 2 * u = ρ ^ 2 * (1 + u) by ring,
      Real.mul_rpow hρsq.le hu.le,
      Real.mul_rpow hρsq.le (by linarith : 0 ≤ 1 + u),
      Real.rpow_add hρsq (-p) d]
    ring
  have hscaled : IntegrableOn (fun u : ℝ ↦ f (ρ ^ 2 * u)) (Ioi 0) :=
    IntegrableOn.congr_fun (hnormalized.const_mul ((ρ ^ 2) ^ (-p + d)))
      (fun u hu ↦ (hscale u hu).symm) measurableSet_Ioi
  have hintegrable : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff f 0 hρsq).mp hscaled
    simpa only [mul_zero] using h
  -- Include the Jacobian ρ² before combining real powers; no uniformity is assumed.
  have hfactor : ρ ^ 2 * (ρ ^ 2) ^ (-p + d) = ρ ^ (-2 * p - (k : ℝ)) := by
    calc
      ρ ^ 2 * (ρ ^ 2) ^ (-p + d) = (ρ ^ 2) ^ (1 + (-p + d)) := by
        rw [Real.rpow_add hρsq 1 (-p + d), Real.rpow_one]
      _ = ρ ^ ((2 : ℝ) * (1 + (-p + d))) :=
        (Real.rpow_natCast_mul hρ.le 2 (1 + (-p + d))).symm
      _ = ρ ^ (-2 * p - (k : ℝ)) := by
        congr 1
        dsimp [d]
        ring
  have hchange : ρ ^ 2 * (∫ u in Ioi (0 : ℝ), f (ρ ^ 2 * u)) =
      ∫ t in Ioi (0 : ℝ), f t := by
    simpa only [smul_eq_mul, mul_zero] using integral_comp_mul_left_Ioi' f 0 hρsq
  refine ⟨hintegrable, ?_⟩
  calc
    (∫ t in Ioi (0 : ℝ), f t) = ρ ^ 2 * (∫ u in Ioi (0 : ℝ), f (ρ ^ 2 * u)) :=
      hchange.symm
    _ = ρ ^ 2 * (∫ u in Ioi (0 : ℝ), (ρ ^ 2) ^ (-p + d) * F u) := by
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ hscale u hu)
    _ = (ρ ^ 2 * (ρ ^ 2) ^ (-p + d)) * (∫ u in Ioi (0 : ℝ), F u) := by
      rw [integral_const_mul]
      ring
    _ = (∫ u in Ioi (0 : ℝ), F u) * ρ ^ (-2 * p - (k : ℝ)) := by
      rw [hfactor, mul_comm]

end AtiyahSinger
