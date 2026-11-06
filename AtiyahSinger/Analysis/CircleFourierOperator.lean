/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.Holder

/-!
# The actual Fourier operator used for circle normalization

Public module ID: M0324.

AR02: the circle is `AddCircle (2 * Real.pi)`, with its normalized Haar measure.
Its L² space and Fourier coefficient isometry are mathlib's original objects.
The nonnegative-frequency projection is the conjugate of the literal coefficient
cutoff. Multiplication by the first character is the existing Hölder extension
of pointwise complex multiplication, with the character in L∞. Thus the operator
`A = M₁ Π₊ + (I - Π₊)` is an actual continuous linear endomorphism of this L²
space; its definition does not select an unspecified operator from a theorem.

Source: Atiyah--Singer I, section 8, printed pp.525--526, the operator immediately
before equation (8.2) and its displayed action on Fourier modes. Period 2π makes
mathlib's character `exp(2π i n x / T)` exactly the source's `exp(i n x)`.
Normalized Haar measure replaces dx by dx/(2π); this constant rescaling leaves
the projection, multiplication operator, kernel and range unchanged. The basis
and coefficient conclusions below use this one normalization throughout.

This module defines the L² operator and computes its Fourier action.
CircleFourierIndex determines its Fredholm index; CircleFourierPseudodifferential
identifies its smooth restriction in the local PDO calculus. The Figure 3
negative point Thom-class comparison then gives the positive point-pushforward
normalization. The operator's index -1 and the point normalization +1 refer
to these distinct, explicitly compared classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ENNReal lp

/-- The fixed period is positive, selecting the same normalized circle Haar measure. -/
instance circlePeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos zero_lt_two Real.pi_pos⟩

/-- The original complex L² space on the circle of period 2π, with probability Haar measure. -/
abbrev CircleFourierL2 : Type :=
  Lp ℂ 2 (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive)

/-- Orthogonal projection onto the modes with nonnegative integer frequency. -/
def circleNonnegativeFourierProjection : CircleFourierL2 →L[ℂ] CircleFourierL2 :=
  let e := (fourierBasis (T := 2 * Real.pi)).repr.toContinuousLinearEquiv
  let cutoff : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
    lp.mapCLM 2 (fun n : ℤ ↦ if 0 ≤ n then ContinuousLinearMap.id ℂ ℂ else 0)
      (K := 1) zero_le_one (by
        intro n
        split_ifs <;> simp)
  e.symm.toContinuousLinearMap.comp (cutoff.comp e.toContinuousLinearMap)

/-- Multiplication by the actual character x ↦ exp(i x), using L∞ times L². -/
def circleFourierModeMultiplication : CircleFourierL2 →L[ℂ] CircleFourierL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL
    (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive) ∞ 2 2
    (fourierLp (T := 2 * Real.pi) ∞ 1)

/-- ASI's circle operator shifts the nonnegative modes and keeps the negative modes fixed. -/
def circleFourierIndexOperator : CircleFourierL2 →L[ℂ] CircleFourierL2 :=
  circleFourierModeMultiplication.comp circleNonnegativeFourierProjection +
    (ContinuousLinearMap.id ℂ CircleFourierL2 - circleNonnegativeFourierProjection)

/-- The nonnegative-frequency projection has the specified original Fourier coefficients. -/
theorem circleNonnegativeFourierProjection_fourierCoeff (f : CircleFourierL2) (n : ℤ) :
    fourierCoeff (circleNonnegativeFourierProjection f) n =
      if 0 ≤ n then fourierCoeff f n else 0 := by
  -- Use the original Fourier isometry and its exact identity-or-zero coefficient map.
  rw [← fourierBasis_repr, ← fourierBasis_repr]
  change ((fourierBasis (T := 2 * Real.pi)).repr
    ((fourierBasis (T := 2 * Real.pi)).repr.symm
      ((lp.mapCLM 2 (fun n : ℤ ↦ if 0 ≤ n then ContinuousLinearMap.id ℂ ℂ else 0)
        (K := 1) zero_le_one (by intro n; split_ifs <;> simp))
        ((fourierBasis (T := 2 * Real.pi)).repr f)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  split_ifs with hn
  · simp [lp.mapCLM, hn]
  · simp [lp.mapCLM, hn]

/-- The original ASI operator has the displayed action on every Fourier basis vector. -/
theorem circleFourierIndexOperator_fourierLp (n : ℤ) :
    circleFourierIndexOperator (fourierLp (T := 2 * Real.pi) 2 n) =
      if 0 ≤ n then fourierLp (T := 2 * Real.pi) 2 (n + 1)
      else fourierLp (T := 2 * Real.pi) 2 n := by
  -- The coefficient isometry detects the original Fourier modes and their cutoff.
  have hcoeff (j k : ℤ) : fourierCoeff (fourierLp (T := 2 * Real.pi) 2 j) k =
      if k = j then 1 else 0 := by
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 j), fourierCoeff_fourier]
    simp [Pi.single_apply]
  have hproj : circleNonnegativeFourierProjection (fourierLp (T := 2 * Real.pi) 2 n) =
      if 0 ≤ n then fourierLp (T := 2 * Real.pi) 2 n else 0 := by
    apply (fourierBasis (T := 2 * Real.pi)).repr.injective
    apply lp.ext
    funext k
    simp only [fourierBasis_repr]
    rw [circleNonnegativeFourierProjection_fourierCoeff]
    by_cases hn : 0 ≤ n
    · rw [ite_eq_left hn]
      by_cases hk : k = n
      · subst k
        simp only [hcoeff, hn, ite_true]
      · simp only [hcoeff, hk, ite_false, ite_self]
    · rw [ite_eq_right hn]
      have hzero : fourierCoeff (0 : CircleFourierL2) k = 0 := by
        rw [← fourierBasis_repr]
        simp
      rw [hzero, hcoeff]
      by_cases hk : k = n
      · subst k
        rw [if_neg hn]
      · simp only [hk, ite_false, ite_self]
  -- The actual Hölder extension multiplies these modes almost everywhere.
  have hmul : circleFourierModeMultiplication (fourierLp (T := 2 * Real.pi) 2 n) =
      fourierLp (T := 2 * Real.pi) 2 (n + 1) := by
    apply Lp.ext
    have hh := ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ)
      (fourierLp (T := 2 * Real.pi) ∞ 1) (fourierLp (T := 2 * Real.pi) 2 n) (r := 2)
    filter_upwards [hh, coeFn_fourierLp (T := 2 * Real.pi) ∞ 1,
      coeFn_fourierLp (T := 2 * Real.pi) 2 n,
      coeFn_fourierLp (T := 2 * Real.pi) 2 (n + 1)] with x hx h1 hn hnext
    refine hx.trans ?_
    change (fourierLp (T := 2 * Real.pi) ∞ 1 x) * (fourierLp (T := 2 * Real.pi) 2 n x) = _
    rw [h1, hn, hnext]
    rw [← fourier_add, add_comm 1 n]
  -- Substitute the same projection and multiplication into the specified ASI operator.
  change circleFourierModeMultiplication
      (circleNonnegativeFourierProjection (fourierLp (T := 2 * Real.pi) 2 n)) +
    (fourierLp (T := 2 * Real.pi) 2 n -
      circleNonnegativeFourierProjection (fourierLp (T := 2 * Real.pi) 2 n)) = _
  rw [hproj]
  by_cases hn : 0 ≤ n
  · simp only [ite_eq_left hn, hmul, sub_self, add_zero]
  · simp only [ite_eq_right hn, map_zero, sub_zero, zero_add]

/-- On arbitrary L² inputs, the operator inserts a zero constant Fourier coefficient. -/
theorem circleFourierIndexOperator_fourierCoeff (f : CircleFourierL2) (n : ℤ) :
    fourierCoeff (circleFourierIndexOperator f) n =
      if n < 0 then fourierCoeff f n
      else if n = 0 then 0 else fourierCoeff f (n - 1) := by
  -- Multiplication by the first character shifts the integral coefficient by one.
  have multiplication_coeff (f : CircleFourierL2) (n : ℤ) :
      fourierCoeff (circleFourierModeMultiplication f) n = fourierCoeff f (n - 1) := by
    have hmul : (circleFourierModeMultiplication f : AddCircle (2 * Real.pi) → ℂ) =ᵐ[
        AddCircle.haarAddCircle] fun x ↦ fourier (T := 2 * Real.pi) 1 x * f x := by
      have hh := ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ)
        (fourierLp (T := 2 * Real.pi) ∞ 1) f (r := 2)
      filter_upwards [hh, coeFn_fourierLp (T := 2 * Real.pi) ∞ 1] with x hx hchar
      exact hx.trans (congrArg (· * f x) hchar)
    rw [fourierCoeff]
    trans ∫ x : AddCircle (2 * Real.pi), fourier (-(n - 1)) x • f x
        ∂AddCircle.haarAddCircle
    · apply integral_congr_ae
      filter_upwards [hmul] with x hx
      rw [hx, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← fourier_add]
      have hfreq : -n + 1 = -(n - 1) := by omega
      rw [hfreq]
    · rfl
  -- Fourier coordinates are linear on the original L² space, independently of representatives.
  have hlinear (g h k : CircleFourierL2) : fourierCoeff (g + (h - k)) n =
      fourierCoeff g n + (fourierCoeff h n - fourierCoeff k n) := by
    simp only [← fourierBasis_repr, map_add, map_sub, lp.coeFn_add, lp.coeFn_sub,
      Pi.add_apply, Pi.sub_apply]
  change fourierCoeff (circleFourierModeMultiplication (circleNonnegativeFourierProjection f) +
    (f - circleNonnegativeFourierProjection f)) n = _
  rw [hlinear, multiplication_coeff, circleNonnegativeFourierProjection_fourierCoeff,
    circleNonnegativeFourierProjection_fourierCoeff]
  -- Separate negative output frequencies, the missing constant mode, and positive outputs.
  by_cases hn : n < 0
  · have hn₁ : ¬ 0 ≤ n - 1 := by omega
    have hn₂ : ¬ 0 ≤ n := by omega
    simp only [ite_eq_right hn₁, ite_eq_right hn₂, ite_eq_left hn, sub_zero, zero_add]
  · by_cases hz : n = 0
    · subst n
      simp
    · have hn₁ : 0 ≤ n - 1 := by omega
      have hn₂ : 0 ≤ n := by omega
      simp only [ite_eq_left hn₁, ite_eq_left hn₂, ite_eq_right hn, ite_eq_right hz,
        sub_self, add_zero]

end AtiyahSinger
