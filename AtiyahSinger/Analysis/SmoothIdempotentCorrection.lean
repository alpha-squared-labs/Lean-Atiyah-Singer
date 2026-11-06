/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Smooth correction of approximate idempotents

Public module ID: M0971.

The inverse square-root binomial series gives a smooth retraction onto the
idempotents in a real Banach algebra, near the set of exact idempotents. This
applies to finite complex matrices without self-adjointness and supports the
smooth realization of the original continuous finite bundles.

The construction is the standard power-series correction of an almost
idempotent. All identities concern the original multiplication and unit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Topology NNReal ENNReal ContDiff

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
private theorem one_le_binomialSeries_radius (t : ℝ) :
    1 ≤ (binomialSeries A t).radius := by
  -- Positive-degree coefficient norms are bounded by the scalar coefficient norms.
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  obtain ⟨C, _, hC⟩ := (binomialSeries ℝ t).norm_mul_pow_le_of_lt_radius
    (hr.trans_le binomialSeries_radius_ge_one)
  apply (binomialSeries A t).le_radius_of_eventually_le C
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hb : ‖binomialSeries A t n‖ ≤ ‖binomialSeries ℝ t n‖ := by
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_norm] using
      FormalMultilinearSeries.ofScalars_norm_le A (Ring.choose t) n hn
  exact (mul_le_mul_of_nonneg_right hb (pow_nonneg r.coe_nonneg _)).trans (hC n)

omit [CompleteSpace A] in
private theorem binomial_norm_summable (t : ℝ) (x : A) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ ↦ ‖Ring.choose t n • x ^ n‖) := by
  have hball : x ∈ Metric.eball (0 : A) (binomialSeries A t).radius := by
    rw [mem_eball_zero_iff]
    exact (show (‖x‖₊ : ℝ≥0∞) < 1 from by exact_mod_cast hx).trans_le
      (one_le_binomialSeries_radius t)
  simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq] using
    (binomialSeries A t).summable_norm_apply hball

private theorem binomial_mul (s t : ℝ) (x : A) (hx : ‖x‖ < 1) :
    (∑' n : ℕ, Ring.choose s n • x ^ n) * (∑' n : ℕ, Ring.choose t n • x ^ n) =
      ∑' n : ℕ, Ring.choose (s + t) n • x ^ n := by
  -- Absolute convergence permits the Cauchy product; Vandermonde identifies its coefficients.
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (binomial_norm_summable s x hx) (binomial_norm_summable t x hx)]
  apply tsum_congr
  intro n
  rw [Ring.add_choose_eq n (Commute.all s t), Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [smul_mul_smul_comm, ← pow_add, Finset.mem_antidiagonal.mp hij]

omit [CompleteSpace A] in
private theorem binomial_neg_one (x : A) :
    (∑' n : ℕ, Ring.choose (-1 : ℝ) n • x ^ n) = ∑' n : ℕ, (-x) ^ n := by
  apply tsum_congr
  intro n
  rw [Ring.choose_neg', Ring.multichoose_one]
  simp only [Units.smul_def, mul_one, Algebra.smul_def]
  change (algebraMap ℝ A) (((n : ℤ).negOnePow : ℤ) : ℝ) * x ^ n = (-x) ^ n
  rw [Int.cast_negOnePow_natCast, map_pow, map_neg, map_one]
  exact (neg_pow x n).symm

/-- Correct an approximate idempotent using the original Banach-algebra product. -/
def idempotentCorrection (a : A) : A :=
  (1 / 2 : ℝ) • (1 + ((2 : ℝ) • a - 1) *
    ∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • ((4 : ℝ) • (a * a - a)) ^ n)

/-- The correction is an actual idempotent whenever the original defect is small. -/
theorem isIdempotentElem_idempotentCorrection (a : A)
    (ha : ‖(4 : ℝ) • (a * a - a)‖ < 1) :
    IsIdempotentElem (idempotentCorrection a) := by
  let x := (4 : ℝ) • (a * a - a)
  let v := (2 : ℝ) • a - 1
  let b : A := ∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • x ^ n
  -- Vandermonde gives the inverse square, and the geometric series supplies its inverse identity.
  have hb : (b * b) * (1 + x) = 1 := by
    change ((∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • x ^ n) *
      (∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • x ^ n)) * (1 + x) = 1
    rw [binomial_mul _ _ x ha, show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num,
      binomial_neg_one]
    simpa only [sub_neg_eq_add] using geom_series_mul_neg (-x) (by simpa using ha)
  have hv : v * v = 1 + x := by
    dsimp only [v, x]
    simp only [Algebra.smul_def, map_ofNat]
    noncomm_ring
  have hvx : Commute v x := by
    rw [show x = v * v - 1 by rw [hv]; abel]
    exact ((Commute.refl v).mul_right (Commute.refl v)).sub_right (Commute.one_right v)
  have hvb : Commute v b :=
    Commute.tsum_right v (fun n ↦ (hvx.pow_right n).smul_right (Ring.choose (-1 / 2 : ℝ) n))
  -- The normalized odd part is an involution; its positive half is therefore a projection.
  have hz : (v * b) * (v * b) = 1 := by
    rw [hvb.eq, ← pow_two, hvb.symm.mul_pow, pow_two, pow_two, hv, hb]
  change ((1 / 2 : ℝ) • (1 + v * b)) * ((1 / 2 : ℝ) • (1 + v * b)) =
    (1 / 2 : ℝ) • (1 + v * b)
  rw [smul_mul_smul_comm]
  have hsum : (1 + v * b) * (1 + v * b) = (2 : ℝ) • (1 + v * b) := by
    rw [two_smul]
    noncomm_ring [hz]
  rw [hsum, smul_smul]
  norm_num

omit [CompleteSpace A] in
/-- The retraction fixes every original idempotent. -/
theorem idempotentCorrection_eq (a : A) (ha : IsIdempotentElem a) :
    idempotentCorrection a = a := by
  have hdefect : a * a - a = 0 := sub_eq_zero.mpr ha
  have hsum : (∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • (0 : A) ^ n) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  simp only [idempotentCorrection, hdefect, smul_zero, hsum, mul_one]
  module

/-- Smoothness holds on the open neighborhood measured by the original idempotency defect. -/
theorem contDiffAt_idempotentCorrection (a : A)
    (ha : ‖(4 : ℝ) • (a * a - a)‖ < 1) :
    ContDiffAt ℝ ∞ (idempotentCorrection (A := A)) a := by
  let x := (4 : ℝ) • (a * a - a)
  let B : A → A := fun y ↦ ∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • y ^ n
  have hball : x ∈ Metric.eball (0 : A) (binomialSeries A (-1 / 2 : ℝ)).radius := by
    rw [mem_eball_zero_iff]
    have hx : ‖x‖ < 1 := ha
    exact (show (‖x‖₊ : ℝ≥0∞) < 1 from by exact_mod_cast hx).trans_le
      (one_le_binomialSeries_radius (-1 / 2))
  -- The convergent formal power series is analytic on its original Banach-algebra ball.
  have hB : ContDiffAt ℝ ∞ B x := by
    have heq : (binomialSeries A (-1 / 2 : ℝ)).sum = B :=
      FormalMultilinearSeries.ofScalarsSum_eq_tsum _
    rw [← heq]
    exact ((binomialSeries A (-1 / 2 : ℝ)).analyticOnNhd x hball).contDiffAt
  have hdefect : ContDiffAt ℝ ∞ (fun y : A ↦ (4 : ℝ) • (y * y - y)) a :=
    (contDiffAt_id.mul contDiffAt_id |>.sub contDiffAt_id).const_smul 4
  -- Compose with the polynomial defect and the specified original multiplication.
  exact (contDiffAt_const.add
    (((contDiffAt_id.const_smul (2 : ℝ)).sub contDiffAt_const).mul
      (hB.comp a hdefect))).const_smul (1 / 2 : ℝ)

end AtiyahSinger
