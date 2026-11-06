/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyRing
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Evaluation of the original cohomology polynomials

Public module ID: M1831.

Homogeneous inclusion identifies the original degree-two cup powers and the
original recursively defined elementary symmetric classes with ordinary
polynomial evaluation in the even cohomology ring. The proofs retain all
canonical degree transports, including degree zero and an empty list of roots.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Canonical transport of a homogeneous degree does not change its included class. -/
theorem singularEvenCohomologyOf_eqToIso {p q : ℕ} (h : p = q)
    (a : singularCohomology R X (2 * p)) :
    singularEvenCohomologyOf R X q
        ((eqToIso (congrArg (fun k ↦ singularCohomology R X (2 * k)) h)).hom a) =
      singularEvenCohomologyOf R X p a := by
  subst q
  rfl

/-- The original recursive cup powers become ordinary powers of the same degree-two class. -/
theorem singularEvenCohomologyOf_degreeTwoPow (a : singularCohomology R X 2) (k : ℕ) :
    singularEvenCohomologyOf R X k (singularCohomologyDegreeTwoPow R X a k) =
      singularEvenCohomologyOf R X 1 a ^ k := by
  induction k with
  | zero => exact singularEvenCohomologyOf_one R X
  | succ k hk =>
    -- The recursive definition changes only the notation for the total degree.
    rw [singularCohomologyDegreeTwoPow]
    rw [singularEvenCohomologyOf_eqToIso R X (Nat.add_comm 1 k),
      singularEvenCohomologyOf_cup, hk, pow_succ']

/-- The original elementary symmetric class evaluates the same roots in the cup ring. -/
theorem singularEvenCohomologyOf_elementarySymmetric
    (xs : List (singularCohomology R X 2)) (k : ℕ) :
    singularEvenCohomologyOf R X k (singularCohomologyElementarySymmetric R X xs k) =
      (Multiset.map (singularEvenCohomologyOf R X 1) (xs : Multiset _)).esymm k := by
  have hcons (a : SingularEvenCohomology R X) (s : Multiset (SingularEvenCohomology R X))
      (k : ℕ) : (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
    simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
      Multiset.sum_add, Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
    rw [Multiset.sum_map_mul_left]
  -- Both sides obey the elementary-symmetric recursion on the same list of roots.
  induction xs generalizing k with
  | nil =>
    cases k with
    | zero =>
      rw [singularCohomologyElementarySymmetric, Multiset.esymm_zero]
      exact singularEvenCohomologyOf_one R X
    | succ k =>
      simp [singularCohomologyElementarySymmetric, Multiset.esymm,
        Multiset.powersetCard_zero_right]
  | cons a xs ih =>
    cases k with
    | zero =>
      rw [singularCohomologyElementarySymmetric, Multiset.esymm_zero]
      exact singularEvenCohomologyOf_one R X
    | succ k =>
      rw [singularCohomologyElementarySymmetric, map_add]
      rw [singularEvenCohomologyOf_eqToIso R X (Nat.add_comm 1 k),
        singularEvenCohomologyOf_cup, ih, ih]
      exact (hcons _ _ k).symm

end AtiyahSinger
