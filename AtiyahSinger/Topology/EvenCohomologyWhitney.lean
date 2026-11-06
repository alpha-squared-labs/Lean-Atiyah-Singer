/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomialEvaluation
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The elementary symmetric convolution in actual even cohomology

Public module ID: M1836.

Concatenating two finite root lists multiplies their elementary symmetric series.
Homogeneous inclusion transfers this standard polynomial identity to the original
cup product, with the precise degree transports used by the Whitney formula.
This is the algebraic comparison needed for a common geometric splitting space;
it does not assert that any bundle has such a splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Concatenated root lists give the finite elementary symmetric cup convolution. -/
theorem singularCohomologyElementarySymmetric_append
    (xs ys : List (singularCohomology R X 2)) (k : ℕ) :
    singularCohomologyElementarySymmetric R X (xs ++ ys) k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology R X (2 * (i.val + (k - i.val))) ≅
            singularCohomology R X (2 * k)).hom
          (singularCohomologyEvenCup R X i.val (k - i.val)
            (singularCohomologyElementarySymmetric R X xs i.val)
            (singularCohomologyElementarySymmetric R X ys (k - i.val))) := by
  classical
  let S := SingularEvenCohomology R X
  -- The elementary symmetric coefficients are those of the finite product ∏(1 + a t).
  have hcoeff (zs : List S) (n : ℕ) :
      PowerSeries.coeff n ((zs.map (fun a ↦ PowerSeries.C a * PowerSeries.X + 1)).prod) =
        (zs : Multiset S).esymm n := by
    have hcons (a : S) (s : Multiset S) (m : ℕ) :
        (a ::ₘ s).esymm (m + 1) = s.esymm (m + 1) + a * s.esymm m := by
      simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
        Multiset.sum_add, Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
      rw [Multiset.sum_map_mul_left]
    induction zs generalizing n with
    | nil =>
      cases n <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
    | cons a zs ih =>
      cases n with
      | zero =>
        rw [List.map_cons, List.prod_cons, add_mul, one_mul, mul_assoc, map_add,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, ih]
        simp
      | succ n =>
        rw [List.map_cons, List.prod_cons, add_mul, one_mul, mul_assoc, map_add,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, ih, ih]
        change a * (zs : Multiset S).esymm n + (zs : Multiset S).esymm (n + 1) =
          (a ::ₘ (zs : Multiset S)).esymm (n + 1)
        rw [hcons, add_comm]
  -- Including a homogeneous class is injective and preserves the same transported cup.
  apply singularEvenCohomologyOf_injective R X k
  rw [singularEvenCohomologyOf_elementarySymmetric, map_sum]
  have hterm (i : Fin (k + 1)) :
      singularEvenCohomologyOf R X k
          ((eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology R X (2 * (i.val + (k - i.val))) ≅
              singularCohomology R X (2 * k)).hom
            (singularCohomologyEvenCup R X i.val (k - i.val)
              (singularCohomologyElementarySymmetric R X xs i.val)
              (singularCohomologyElementarySymmetric R X ys (k - i.val)))) =
        ((xs : Multiset _).map (singularEvenCohomologyOf R X 1)).esymm i.val *
          ((ys : Multiset _).map (singularEvenCohomologyOf R X 1)).esymm (k - i.val) := by
    rw [singularEvenCohomologyOf_eqToIso R X
      (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup,
      singularEvenCohomologyOf_elementarySymmetric, singularEvenCohomologyOf_elementarySymmetric]
  simp_rw [hterm]
  let as := xs.map (singularEvenCohomologyOf R X 1)
  let bs := ys.map (singularEvenCohomologyOf R X 1)
  simp_rw [Multiset.map_coe, List.map_append]
  change ((as ++ bs : List S) : Multiset S).esymm k =
    ∑ i : Fin (k + 1), (as : Multiset S).esymm i.val *
      (bs : Multiset S).esymm (k - i.val)
  simp_rw [← hcoeff]
  rw [List.map_append, List.prod_append, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact (Fin.sum_univ_eq_sum_range (fun n ↦
    PowerSeries.coeff n ((as.map (fun a ↦ PowerSeries.C a * PowerSeries.X + 1)).prod) *
      PowerSeries.coeff (k - n) ((bs.map (fun a ↦ PowerSeries.C a * PowerSeries.X + 1)).prod))
    (k + 1)).symm

end AtiyahSinger
