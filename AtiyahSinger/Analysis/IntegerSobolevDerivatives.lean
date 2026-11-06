/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Quantization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Derivative recursion for the original Bessel norms

Public module ID: M0761.

Plancherel identifies one additional Sobolev order with the original norm
and the norms of all coordinate derivatives. The coefficient retains the
actual period-one Fourier convention. Iteration supplies the integer
derivative characterization used in SG III.2 (2.1) and Proposition 2.14.
All functions and norms remain the existing Schwartz and Bessel objects.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory FourierTransform
open scoped BigOperators LineDeriv SchwartzMap

set_option maxSynthPendingDepth 30

variable (n r : ℕ)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin r)

set_option maxHeartbeats 800000 in

/-- One higher Bessel norm is the sum of the original squared norm and all derivative norms.
The factor accounts for the original period-one Fourier transform. -/
theorem norm_schwartzSobolevCoordinate_add_one_sq (s : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ‖schwartzSobolevCoordinate (s + 1) u‖ ^ 2 =
      ‖schwartzSobolevCoordinate s u‖ ^ 2 + (2 * Real.pi)⁻¹ ^ 2 *
        ∑ a : Fin n, ‖schwartzSobolevCoordinate s
          (LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) u)‖ ^ 2 := by
  let w (t : ℝ) : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (t / 2)
  have hw (t : ℝ) : (w t).HasTemperateGrowth := by
    dsimp [w]
    fun_prop
  let F (t : ℝ) (v : 𝓢(X, V)) : 𝓢(X, V) :=
    SchwartzMap.smulLeftCLM V (w t) (𝓕 v)
  let D (a : Fin n) : 𝓢(X, V) := LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) u
  -- Every integral is the squared L² norm of an actual Schwartz function.
  have hL2 (v : 𝓢(X, V)) : ‖v.toLp 2‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖v x‖))
  have hnorm (t : ℝ) (v : 𝓢(X, V)) :
      ‖schwartzSobolevCoordinate t v‖ ^ 2 = ∫ ξ, ‖F t v ξ‖ ^ 2 := by
    unfold schwartzSobolevCoordinate
    rw [hL2, ← SchwartzMap.integral_norm_sq_fourier]
    simp only [SchwartzMap.fourierMultiplierCLM_apply,
      FourierTransform.fourier_fourierInv_eq, F, w]
  have hint (t : ℝ) (v : 𝓢(X, V)) : Integrable (fun ξ ↦ ‖F t v ξ‖ ^ 2) :=
    ((F t v).memLp 2).integrable_norm_pow (by norm_num)
  -- A coordinate derivative has multiplier 2πi times that original frequency coordinate.
  have hfourier (a : Fin n) (ξ : X) :
      F s (D a) ξ = (2 * Real.pi * Complex.I) • ((ξ a : ℝ) • F s u ξ) := by
    dsimp only [D, F]
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have ha : (fun η : X ↦ inner ℝ η (EuclideanSpace.single a (1 : ℝ))).HasTemperateGrowth := by
      fun_prop
    simp only [SchwartzMap.smulLeftCLM_apply_apply (hw s), smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ha]
    have hcoord : inner ℝ ξ (EuclideanSpace.single a (1 : ℝ)) = ξ a := by
      simp [EuclideanSpace.inner_single_right]
    rw [hcoord, smul_comm (w s ξ) (2 * Real.pi * Complex.I),
      smul_comm (w s ξ) (ξ a)]
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have hd (a : Fin n) (ξ : X) :
      ‖F s (D a) ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (ξ a) ^ 2 * ‖F s u ξ‖ ^ 2 := by
    rw [hfourier, norm_smul, hc, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  -- Summing the squared coordinate multipliers gives exactly the Euclidean frequency norm.
  have hpoint (ξ : X) : ‖F (s + 1) u ξ‖ ^ 2 =
      ‖F s u ξ‖ ^ 2 + (2 * Real.pi)⁻¹ ^ 2 * ∑ a : Fin n, ‖F s (D a) ξ‖ ^ 2 := by
    have hw2 (t : ℝ) : w t ξ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ t := by
      dsimp [w]
      rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    have hwnorm (t : ℝ) : ‖F t u ξ‖ ^ 2 = w t ξ ^ 2 * ‖𝓕 u ξ‖ ^ 2 := by
      dsimp only [F]
      rw [SchwartzMap.smulLeftCLM_apply_apply (hw t), norm_smul]
      simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [hd]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [hwnorm (s + 1), hwnorm s, hw2 (s + 1), hw2 s,
      Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
  -- Finite additivity transports this pointwise identity through the same frequency integral.
  simp_rw [hnorm]
  change _ = _ + (2 * Real.pi)⁻¹ ^ 2 * ∑ a : Fin n, ∫ ξ, ‖F s (D a) ξ‖ ^ 2
  rw [← integral_finsetSum Finset.univ (fun a _ ↦ hint s (D a)), ← integral_const_mul]
  rw [← integral_add (hint s u)
    ((integrable_finsetSum Finset.univ (fun a _ ↦ hint s (D a))).const_mul _)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- Integer Bessel norms and all coordinate derivatives through that order are equivalent.
The constants allow the original Fourier convention; the zeroth derivative is included. -/
theorem exists_schwartzSobolevCoordinate_sq_derivatives_comparison (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : 𝓢(X, V),
      c * (∑ j : Fin (k + 1), ∑ a : Fin j.val → Fin n,
        ‖(LineDeriv.iteratedLineDerivOp
          (fun b ↦ EuclideanSpace.single (a b) (1 : ℝ)) u).toLp 2‖ ^ 2) ≤
        ‖schwartzSobolevCoordinate (k : ℝ) u‖ ^ 2 ∧
      ‖schwartzSobolevCoordinate (k : ℝ) u‖ ^ 2 ≤
        C * (∑ j : Fin (k + 1), ∑ a : Fin j.val → Fin n,
          ‖(LineDeriv.iteratedLineDerivOp
            (fun b ↦ EuclideanSpace.single (a b) (1 : ℝ)) u).toLp 2‖ ^ 2) := by
  classical
  let Q (j : ℕ) (u : 𝓢(X, V)) : ℝ := ∑ a : Fin j → Fin n,
    ‖(LineDeriv.iteratedLineDerivOp
      (fun b ↦ EuclideanSpace.single (a b) (1 : ℝ)) u).toLp 2‖ ^ 2
  let H (j : ℕ) (u : 𝓢(X, V)) : ℝ := ∑ l : Fin (j + 1), Q l.val u
  let D (a : Fin n) (u : 𝓢(X, V)) : 𝓢(X, V) :=
    LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) u
  let N (j : ℕ) (u : 𝓢(X, V)) : ℝ := ‖schwartzSobolevCoordinate (j : ℝ) u‖ ^ 2
  let d : ℝ := (2 * Real.pi)⁻¹ ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hQ (j : ℕ) (u : 𝓢(X, V)) : 0 ≤ Q j u :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hH (j : ℕ) (u : 𝓢(X, V)) : 0 ≤ H j u :=
    Finset.sum_nonneg (fun _ _ ↦ hQ _ _)
  have hzero (u : 𝓢(X, V)) : Q 0 u = ‖u.toLp 2‖ ^ 2 := by simp [Q]
  -- Removing the last coordinate direction enumerates every ordered derivative once.
  have hQsucc (j : ℕ) (u : 𝓢(X, V)) : Q (j + 1) u = ∑ a : Fin n, Q j (D a u) := by
    dsimp only [Q]
    rw [← (Fin.snocEquiv (fun _ : Fin (j + 1) ↦ Fin n)).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 2
    rw [LineDeriv.iteratedLineDerivOp_succ_right]
    simp only [Fin.snocEquiv_apply, Fin.init_def, Fin.snoc_castSucc, Fin.snoc_last, D]
  have hHsucc (j : ℕ) (u : 𝓢(X, V)) :
      H (j + 1) u = ‖u.toLp 2‖ ^ 2 + ∑ a : Fin n, H j (D a u) := by
    dsimp only [H]
    rw [Fin.sum_univ_succ, Fin.val_zero, hzero]
    congr 1
    simp_rw [Fin.val_succ, hQsucc]
    rw [Finset.sum_comm]
  have hHmono (j : ℕ) (u : 𝓢(X, V)) : H j u ≤ H (j + 1) u := by
    dsimp only [H]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (hQ _ _)
  have hbase (j : ℕ) (u : 𝓢(X, V)) : ‖u.toLp 2‖ ^ 2 ≤ H j u := by
    induction j with
    | zero => simp [H, hzero]
    | succ j ih => exact ih.trans (hHmono j u)
  have hNzero (u : 𝓢(X, V)) : N 0 u = ‖u.toLp 2‖ ^ 2 := by
    simp only [N, Nat.cast_zero, schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
      SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
  have hNsucc (j : ℕ) (u : 𝓢(X, V)) : N (j + 1) u = N j u + d * ∑ a, N j (D a u) := by
    simpa only [N, D, d, Nat.cast_add, Nat.cast_one] using
      norm_schwartzSobolevCoordinate_add_one_sq n r (j : ℝ) u
  -- The positive zeroth term and the one-step Fourier formula propagate both bounds.
  change ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u, c * H k u ≤ N k u ∧ N k u ≤ C * H k u
  induction k with
  | zero =>
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro u
    simp [H, hzero, hNzero]
  | succ k ih =>
    obtain ⟨c, C, hc, hC, hi⟩ := ih
    refine ⟨min 1 d * c, (1 + d) * C, mul_pos (lt_min (by norm_num) hd) hc,
      mul_pos (by positivity) hC, ?_⟩
    intro u
    have hslo : c * ∑ a, H k (D a u) ≤ ∑ a, N k (D a u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ ↦ (hi (D a u)).1)
    have hsup : (∑ a, N k (D a u)) ≤ C * ∑ a, H k (D a u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ ↦ (hi (D a u)).2)
    have hsnonneg : 0 ≤ ∑ a, H k (D a u) := Finset.sum_nonneg (fun _ _ ↦ hH _ _)
    have hsmall : 0 ≤ min 1 d := le_of_lt (lt_min (by norm_num) hd)
    constructor
    · have hfirst : min 1 d * c * ‖u.toLp 2‖ ^ 2 ≤ N k u := by
        have hcoef : min 1 d * c ≤ c := by nlinarith [min_le_left 1 d]
        exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
          ((mul_le_mul_of_nonneg_left (hbase k u) hc.le).trans (hi u).1)
      have hsecond : min 1 d * c * (∑ a, H k (D a u)) ≤ d * ∑ a, N k (D a u) := by
        have hcoef : min 1 d * c ≤ d * c :=
          mul_le_mul_of_nonneg_right (min_le_right 1 d) hc.le
        exact (mul_le_mul_of_nonneg_right hcoef hsnonneg).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hslo hd.le)
      rw [hHsucc, hNsucc, mul_add]
      exact add_le_add hfirst hsecond
    · have hfirst : N k u ≤ C * H (k + 1) u :=
        (hi u).2.trans (mul_le_mul_of_nonneg_left (hHmono k u) hC.le)
      have hsecond : d * ∑ a, N k (D a u) ≤ d * C * H (k + 1) u := by
        apply (mul_le_mul_of_nonneg_left hsup hd.le).trans
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hd.le
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [hHsucc]
        exact le_add_of_nonneg_left (sq_nonneg _)
      rw [hNsucc]
      calc
        _ ≤ C * H (k + 1) u + d * C * H (k + 1) u := add_le_add hfirst hsecond
        _ = (1 + d) * C * H (k + 1) u := by ring

end AtiyahSinger
