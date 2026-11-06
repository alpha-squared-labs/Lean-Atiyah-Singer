/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum

import Mathlib.Tactic.FieldSimp

/-!
# Finite convolution of factorial-normalized power sums

Public module ID: M0017.

The binomial theorem gives the degreewise exponential identity in a commutative
rational algebra. Summing over two finite root families proves the tensor
Chern-character convolution. The identity is finite, includes degree zero and
empty root families, and assumes no convergence or nilpotence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

/-- Factorial-normalized power sums on pairwise sums satisfy finite convolution. -/
theorem sum_add_pow_inv_factorial
    {A : Type*} [CommRing A] [Algebra ℚ A] {r s : ℕ}
    (x : Fin r → A) (y : Fin s → A) (k : ℕ) :
    (k.factorial : ℚ)⁻¹ • ∑ a : Fin r, ∑ b : Fin s, (x a + y b) ^ k =
      ∑ i : Fin (k + 1),
        ((i.val.factorial : ℚ)⁻¹ • ∑ a : Fin r, x a ^ i.val) *
          (((k - i.val).factorial : ℚ)⁻¹ • ∑ b : Fin s, y b ^ (k - i.val)) := by
  -- First normalize each binomial coefficient in the coefficient field.
  have hcoeff (i : Fin (k + 1)) :
      (k.factorial : ℚ)⁻¹ * (k.choose i.val : ℚ) =
        (i.val.factorial : ℚ)⁻¹ * ((k - i.val).factorial : ℚ)⁻¹ := by
    have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
    rw [Nat.cast_choose ℚ hi]
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  have hterm (a b : A) :
      (k.factorial : ℚ)⁻¹ • (a + b) ^ k =
        ∑ i : Fin (k + 1),
          ((i.val.factorial : ℚ)⁻¹ • a ^ i.val) *
            (((k - i.val).factorial : ℚ)⁻¹ • b ^ (k - i.val)) := by
    rw [add_pow, ← Fin.sum_univ_eq_sum_range, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm (a ^ i.val * b ^ (k - i.val)), ← nsmul_eq_mul,
      ← Nat.cast_smul_eq_nsmul ℚ]
    rw [smul_smul, hcoeff]
    simp only [smul_mul_smul_comm]
  -- Distribute over the two root families and interchange only finite sums.
  simp only [Finset.smul_sum]
  simp_rw [hterm]
  calc
    _ = ∑ a : Fin r, ∑ i : Fin (k + 1), ∑ b : Fin s,
        ((i.val.factorial : ℚ)⁻¹ • x a ^ i.val) *
          (((k - i.val).factorial : ℚ)⁻¹ • y b ^ (k - i.val)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i : Fin (k + 1), ∑ a : Fin r, ∑ b : Fin s,
        ((i.val.factorial : ℚ)⁻¹ • x a ^ i.val) *
          (((k - i.val).factorial : ℚ)⁻¹ • y b ^ (k - i.val)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul_sum]

end AtiyahSinger
