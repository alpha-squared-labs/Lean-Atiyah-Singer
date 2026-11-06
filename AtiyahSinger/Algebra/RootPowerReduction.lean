/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Reduction of a power by its split characteristic relation

Public module ID: M0057.

Vieta's formula rewrites a vanishing product of linear factors as a formula
for the leading power in terms of lower powers and signed elementary
symmetric coefficients. The ordering is by increasing powers, as required
for projective Leray--Hirsch coefficients. Rank zero is retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- A split characteristic relation expresses its leading power in the lower-power basis. -/
theorem pow_eq_sum_esymm_of_prod_sub_eq_zero {R : Type*} [CommRing R]
    (r : ℕ) (x : Fin r → R) (t : R) (h : ∏ i, (t - x i) = 0) :
    t ^ r = ∑ i : Fin r,
      (-1) ^ (r - i.val + 1) * (Finset.univ.val.map x).esymm (r - i.val) * t ^ i.val := by
  classical
  let s : Multiset R := Finset.univ.val.map x
  have hs : s.card = r := by simp [s]
  -- Evaluate the ordinary polynomial Vieta identity in the same commutative ring.
  have hv := congrArg (Polynomial.evalRingHom t) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  have hvieta : ∏ i : Fin r, (t - x i) =
      ∑ j ∈ Finset.range (r + 1), (-1) ^ j * s.esymm j * t ^ (r - j) := by
    simpa only [map_multiset_prod, Multiset.map_map, map_sub, Polynomial.coe_evalRingHom,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_sum, map_mul, map_pow,
      map_neg, map_one,
      hs, s, Function.comp_def, mul_assoc, Finset.prod] using hv
  -- Reverse the finite order so the final summand is exactly the leading power.
  have hreverse :
      (∑ j ∈ Finset.range (r + 1), (-1 : R) ^ j * s.esymm j * t ^ (r - j)) =
        ∑ i ∈ Finset.range (r + 1), (-1) ^ (r - i) * s.esymm (r - i) * t ^ i := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hir]
  rw [hreverse, Finset.sum_range_succ] at hvieta
  simp only [Nat.sub_self, pow_zero, Multiset.esymm_zero, one_mul] at hvieta
  have hsum : (∑ i : Fin r, (-1 : R) ^ (r - i.val) * s.esymm (r - i.val) * t ^ i.val) +
      t ^ r = 0 := by
    have hfinite := Fin.sum_univ_eq_sum_range
      (fun i ↦ (-1 : R) ^ (r - i) * s.esymm (r - i) * t ^ i) r
    rw [hfinite]
    exact hvieta.symm.trans h
  -- Moving those lower powers to the other side changes the alternating sign once.
  have hsign :
      (∑ i : Fin r, (-1 : R) ^ (r - i.val + 1) * s.esymm (r - i.val) * t ^ i.val) =
        -(∑ i : Fin r, (-1) ^ (r - i.val) * s.esymm (r - i.val) * t ^ i.val) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  change t ^ r = ∑ i : Fin r,
    (-1) ^ (r - i.val + 1) * s.esymm (r - i.val) * t ^ i.val
  rw [hsign]
  exact eq_neg_of_add_eq_zero_right hsum

end AtiyahSinger
