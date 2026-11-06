/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The sign of grouped-to-interleaved coordinates

Public module ID: M1474.

A permutation sending the first block to even positions and the second block
to odd positions has one inversion for each pair of distinct original indices
in decreasing order. The sign is therefore the parity of the triangular number.
The empty permutation is included. The coordinate hypotheses allow the actual
native tangent coordinate equivalence to be used without defining a replacement.

Source: the permutation convention in Lawson--Michelsohn, Spin Geometry, III.13.
-/

public section

namespace AtiyahSinger

open scoped BigOperators

/-- Interleaving two ordered blocks has the triangular-number sign, including empty blocks. -/
theorem sign_of_interleaved_coordinates (n : ℕ) (σ : Equiv.Perm (Fin (n + n)))
    (hleft : ∀ i : Fin n, (σ (i.castAdd n)).val = 2 * i.val)
    (hright : ∀ i : Fin n, (σ (i.natAdd n)).val = 2 * i.val + 1) :
    (σ.sign : ℤ) = (-1 : ℤ) ^ (n * (n - 1) / 2) := by
  classical
  -- Write the sign as the product of the contributions of all ordered pairs.
  let factor (i j : Fin (n + n)) : ℤˣ :=
    if i < j then if σ i < σ j then 1 else -1 else 1
  have hsign : σ.sign = ∏ i, ∏ j, factor i j := by
    rw [σ.sign_eq_prod_prod_Ioi]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have hLL (i j : Fin n) : factor (i.castAdd n) (j.castAdd n) = 1 := by
    dsimp [factor]
    split_ifs with h hij
    · rfl
    · have hh : (σ (i.castAdd n)).val < (σ (j.castAdd n)).val := by
        rw [hleft, hleft]
        exact Nat.mul_lt_mul_of_pos_left (show i.val < j.val from h) (by omega)
      exact (hij hh).elim
    · rfl
  have hRL (i j : Fin n) : factor (i.natAdd n) (j.castAdd n) = 1 := by
    have h : ¬ i.natAdd n < j.castAdd n := by
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
      omega
    simp only [factor, ite_eq_right h]
  have hRR (i j : Fin n) : factor (i.natAdd n) (j.natAdd n) = 1 := by
    dsimp [factor]
    split_ifs with h hij
    · rfl
    · have hh : (σ (i.natAdd n)).val < (σ (j.natAdd n)).val := by
        rw [hright, hright]
        have hh : n + i.val < n + j.val := h
        omega
      exact (hij hh).elim
    · rfl
  have hLR (i j : Fin n) :
      factor (i.castAdd n) (j.natAdd n) = if j < i then -1 else 1 := by
    have hij : i.castAdd n < j.natAdd n := by
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
      omega
    have hσ : σ (i.castAdd n) < σ (j.natAdd n) ↔ ¬ j < i := by
      simp only [Fin.lt_def, hleft, hright]
      omega
    simp only [factor, ite_eq_left hij, hσ, ite_not]
  -- Within-block order is preserved. Only earlier odd positions contribute inversions.
  have hrow (i : Fin n) : ∏ j, factor (i.castAdd n) j = (-1 : ℤˣ) ^ i.val := by
    rw [Fin.prod_univ_add]
    simp only [hLL, Finset.prod_const_one, one_mul, hLR]
    rw [← Finset.prod_filter]
    have hs : Finset.univ.filter (fun j : Fin n ↦ j < i) = Finset.Iio i := by
      ext j
      simp
    rw [hs, Finset.prod_const, Fin.card_Iio]
  have hrow' (i : Fin n) : ∏ j, factor (i.natAdd n) j = 1 := by
    rw [Fin.prod_univ_add]
    simp only [hRL, hRR, Finset.prod_const_one, mul_one]
  have hunit : σ.sign = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
    rw [hsign, Fin.prod_univ_add]
    simp only [hrow, hrow', Finset.prod_const_one, mul_one]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    calc
      ∑ i : Fin n, i.val = ∑ i ∈ Finset.range n, i :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n
      _ = _ := Finset.sum_range_id n
  exact congrArg (fun x : ℤˣ ↦ (x : ℤ)) hunit

end AtiyahSinger
