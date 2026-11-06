/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyCup

/-!
# Symmetric polynomials in actual degree-two cohomology classes

Public module ID: M1832.

The ordinary cup product, with only canonical degree transports, evaluates powers
and elementary symmetric polynomials in degree-two classes. These are standard
polynomial formulas used for Chern classes and the Chern character (SG III.11).
They do not supply characteristic classes or assume that classes descend from
a flag bundle. The empty list and degree zero retain the ordinary unit class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The original cup product in even degrees, with the canonical total-degree transport. -/
def singularCohomologyEvenCup (p q : ℕ) :
    singularCohomology R X (2 * p) →ₗ[R] singularCohomology R X (2 * q) →ₗ[R]
      singularCohomology R X (2 * (p + q)) :=
  (singularCohomologyCup R X (2 * p) (2 * q)).compr₂
    (eqToIso (by rw [Nat.mul_add]) :
      singularCohomology R X (2 * p + 2 * q) ≅
        singularCohomology R X (2 * (p + q))).hom.hom

/-- The k-th cup power of an actual degree-two class; the zeroth power is the unit. -/
def singularCohomologyDegreeTwoPow (a : singularCohomology R X 2) :
    (k : ℕ) → singularCohomology R X (2 * k)
  | 0 => singularCohomologyOne R X
  | k + 1 =>
    (eqToIso (by rw [Nat.add_comm 1 k]) : singularCohomology R X (2 * (1 + k)) ≅
      singularCohomology R X (2 * (k + 1))).hom
      (singularCohomologyEvenCup R X 1 k a (singularCohomologyDegreeTwoPow a k))

/-- Elementary symmetric polynomials evaluated in the original even singular cohomology. -/
def singularCohomologyElementarySymmetric :
    List (singularCohomology R X 2) → (k : ℕ) → singularCohomology R X (2 * k)
  | [], 0 => singularCohomologyOne R X
  | [], _ + 1 => 0
  | _ :: _, 0 => singularCohomologyOne R X
  | a :: xs, k + 1 => singularCohomologyElementarySymmetric xs (k + 1) +
      (eqToIso (by rw [Nat.add_comm 1 k]) : singularCohomology R X (2 * (1 + k)) ≅
        singularCohomology R X (2 * (k + 1))).hom
        (singularCohomologyEvenCup R X 1 k a (singularCohomologyElementarySymmetric xs k))

end AtiyahSinger
