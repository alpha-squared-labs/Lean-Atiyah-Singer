/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.PSeries

/-!
# Half-periodization estimates for localized Fourier projection

Public module ID: M0853.

The positive lattice sum of a Schwartz function is smooth and rapidly
decreases, together with every derivative, towards the positive end of
the translated coordinate. Applied to a localized Fourier kernel, this
controls the unwanted frequency tail in the circle Hardy projection.
The opposite tail is obtained by reflection; Poisson summation identifies
the sum of the two tails. This is the analytic estimate underlying the
local Fourier formula in ASI I, section 8, printed p.525.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap Topology

/-- A half-lattice sum is smooth and retains rapid decay at the end away from its translates. -/
theorem schwartz_halfPeriodization_properties (f : 𝓢(ℝ × ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ ∑' n : ℕ, f (z + (0, (n : ℝ)))) ∧
      ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ, 0 ≤ z.2 →
        (1 + z.2) ^ N *
          ‖iteratedFDeriv ℝ k (fun z : ℝ × ℝ ↦ ∑' n : ℕ, f (z + (0, (n : ℝ)))) z‖ ≤ C := by
  classical
  let P := ℝ × ℝ
  let S (N k : ℕ) := 2 ^ N * (Finset.Iic (N, k)).sup
    (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hS (N k : ℕ) : 0 ≤ S N k := by
    dsimp only [S]
    positivity
  have hbound (N k : ℕ) (z : P) :
      (1 + ‖z‖) ^ N * ‖iteratedFDeriv ℝ k f z‖ ≤ S N k :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
      (m := (N, k)) le_rfl le_rfl f z
  let w (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2
  have hw : Summable w := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa only [w, Real.rpow_two, sq_abs] using h
  have hwpos (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  -- On each bounded strip, one inverse-square sequence dominates every translated jet.
  have hlocal (k : ℕ) (R : ℝ) (hR : 0 ≤ R) (z : P) (hz : |z.2| ≤ R) (n : ℕ) :
      ‖iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))‖ ≤ S 2 k * (1 + R) ^ 2 * w n := by
    let y : P := z + (0, (n : ℝ))
    have hy : |z.2 + n| ≤ ‖y‖ := by
      exact norm_snd_le y
    have hn : (n : ℝ) ≤ ‖y‖ + R := by
      have h₁ := le_abs_self (z.2 + n)
      have h₂ := neg_le_abs z.2
      linarith
    have hh : (n : ℝ) + 1 ≤ (1 + R) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg y]
    have hp : ((n : ℝ) + 1) ^ 2 ≤ (1 + R) ^ 2 * (1 + ‖y‖) ^ 2 := by
      nlinarith [sq_nonneg ((1 + R) * (1 + ‖y‖) - ((n : ℝ) + 1))]
    have hd := hbound 2 k y
    have hscaled : ((n : ℝ) + 1) ^ 2 * ‖iteratedFDeriv ℝ k f y‖ ≤
        S 2 k * (1 + R) ^ 2 := by
      calc
        _ ≤ ((1 + R) ^ 2 * (1 + ‖y‖) ^ 2) * ‖iteratedFDeriv ℝ k f y‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
        _ = (1 + R) ^ 2 * ((1 + ‖y‖) ^ 2 * ‖iteratedFDeriv ℝ k f y‖) := by ring
        _ ≤ (1 + R) ^ 2 * S 2 k := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
        _ = _ := by ring
    dsimp only [w]
    rw [← div_eq_mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hscaled)
  let J (k : ℕ) (z : P) := ∑' n : ℕ, iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))
  have hsum (k : ℕ) (z : P) :
      Summable (fun n : ℕ ↦ iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))) :=
    Summable.of_norm_bounded ((hw.mul_left ((S 2 k) * (1 + |z.2|) ^ 2)))
      (fun n ↦ hlocal k |z.2| (abs_nonneg _) z le_rfl n)
  have hsumNorm (k : ℕ) (z : P) :
      Summable (fun n : ℕ ↦ ‖iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ hlocal k |z.2| (abs_nonneg _) z le_rfl n)
      (hw.mul_left ((S 2 k) * (1 + |z.2|) ^ 2))
  have hfd (k : ℕ) (z : P) : HasFDerivAt (J k)
      (∑' n : ℕ, fderiv ℝ (iteratedFDeriv ℝ k f) (z + (0, (n : ℝ)))) z := by
    let R := ‖z‖ + 1
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hstrip (y : P) (hy : y ∈ Metric.ball z 1) : |y.2| ≤ R := by
      have hdist : ‖y - z‖ < 1 := by
        change dist y z < 1 at hy
        rw [dist_eq_norm] at hy
        exact hy
      have hnorm : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (y - z) z
      have hcoord := norm_snd_le y
      change |y.2| ≤ ‖y‖ at hcoord
      dsimp only [R]
      linarith
    apply hasFDerivAt_tsum_of_isPreconnected
      (hw.mul_left (S 2 (k + 1) * (1 + R) ^ 2)) Metric.isOpen_ball
      (convex_ball z 1).isPreconnected
      (f := fun (n : ℕ) y ↦ iteratedFDeriv ℝ k f (y + (0, (n : ℝ))))
      (f' := fun (n : ℕ) y ↦ fderiv ℝ (iteratedFDeriv ℝ k f) (y + (0, (n : ℝ))))
      (x₀ := z) ?_ ?_ (Metric.mem_ball_self (by norm_num)) (hsum k z)
      (Metric.mem_ball_self (by norm_num))
    · intro n y _
      have hd := ((f.smooth ⊤).differentiable_iteratedFDeriv (m := k)
        (mod_cast ENat.natCast_lt_top k)
        (y + (0, (n : ℝ)))).hasFDerivAt
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        hd.comp y ((hasFDerivAt_id y).add_const (0, (n : ℝ)))
    · intro n y hy
      rw [norm_fderiv_iteratedFDeriv]
      exact hlocal (k + 1) R hR y (hstrip y hy) n
  let p (z : P) := ∑' n : ℕ, f (z + (0, (n : ℝ)))
  -- The locally summable derivatives identify every actual derivative of this same sum.
  have hjet (k : ℕ) : iteratedFDeriv ℝ k p = J k := by
    induction k with
    | zero =>
      funext z
      change (continuousMultilinearCurryFin0 ℝ P ℂ).symm (∑' n : ℕ, f (z + (0, (n : ℝ)))) =
        ∑' n : ℕ, (continuousMultilinearCurryFin0 ℝ P ℂ).symm (f (z + (0, (n : ℝ))))
      apply (continuousMultilinearCurryFin0 ℝ P ℂ).symm.toContinuousLinearEquiv.map_tsum
    | succ k ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext z
      dsimp only [Function.comp_apply]
      rw [(hfd k z).fderiv]
      change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P) ℂ).symm
        (∑' n : ℕ, fderiv ℝ (iteratedFDeriv ℝ k f) (z + (0, (n : ℝ)))) =
          ∑' n : ℕ, (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (k + 1) ↦ P) ℂ).symm
              (fderiv ℝ (iteratedFDeriv ℝ k f) (z + (0, (n : ℝ))))
      apply (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (k + 1) ↦ P) ℂ).symm.toContinuousLinearEquiv.map_tsum
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ p
    rw [contDiff_iff_continuous_differentiable]
    constructor
    · intro k _
      rw [hjet]
      exact continuous_iff_continuousAt.mpr (fun z ↦ (hfd k z).continuousAt)
    · intro k _
      rw [hjet]
      exact fun z ↦ (hfd k z).differentiableAt
  · intro k N
    refine ⟨S (N + 2) k * ∑' n : ℕ, w n,
      mul_nonneg (hS _ _) (tsum_nonneg hwpos), ?_⟩
    intro z hz
    have hterm (n : ℕ) : (1 + z.2) ^ N *
        ‖iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))‖ ≤ S (N + 2) k * w n := by
      let y := z + (0, (n : ℝ))
      have hnorm : z.2 + n ≤ ‖y‖ :=
        (le_abs_self _).trans (norm_snd_le y)
      have ha : 1 + z.2 ≤ 1 + ‖y‖ := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hb : (n : ℝ) + 1 ≤ 1 + ‖y‖ := by linarith
      have hpower : ((n : ℝ) + 1) ^ 2 * (1 + z.2) ^ N ≤ (1 + ‖y‖) ^ (N + 2) := by
        rw [pow_add]
        calc
          _ = (1 + z.2) ^ N * ((n : ℝ) + 1) ^ 2 := mul_comm _ _
          _ ≤ (1 + ‖y‖) ^ N * (1 + ‖y‖) ^ 2 := by gcongr
      have hscaled : ((n : ℝ) + 1) ^ 2 *
          ((1 + z.2) ^ N * ‖iteratedFDeriv ℝ k f y‖) ≤ S (N + 2) k := by
        rw [← mul_assoc]
        exact (mul_le_mul_of_nonneg_right hpower (norm_nonneg _)).trans (hbound (N + 2) k y)
      dsimp only [w]
      rw [← div_eq_mul_one_div]
      exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hscaled)
    change (1 + z.2) ^ N * ‖iteratedFDeriv ℝ k p z‖ ≤ _
    rw [hjet]
    calc
      _ ≤ (1 + z.2) ^ N * ∑' n : ℕ,
          ‖iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hsumNorm k z)) (by positivity)
      _ = ∑' n : ℕ, (1 + z.2) ^ N *
          ‖iteratedFDeriv ℝ k f (z + (0, (n : ℝ)))‖ := tsum_mul_left.symm
      _ ≤ ∑' n : ℕ, S (N + 2) k * w n :=
        Summable.tsum_le_tsum hterm ((hsumNorm k z).mul_left _) (hw.mul_left _)
      _ = _ := tsum_mul_left

end AtiyahSinger
