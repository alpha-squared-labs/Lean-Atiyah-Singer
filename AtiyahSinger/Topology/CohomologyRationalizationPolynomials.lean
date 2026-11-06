/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyRationalization
public import AtiyahSinger.Topology.EvenCohomologyPolynomials

/-!
# Rationalization of the original cohomology polynomials

Public module ID: M1627.

The actual integral-to-rational coefficient map preserves the original even
cup product and elementary symmetric classes. Only canonical degree transports
are used; no tensor-product description of rational cohomology is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (X : Type u) [TopologicalSpace X]

private theorem rationalization_transport (n m : ℕ) (h : n = m)
    (a : singularCohomology ℤ X n) :
    singularCohomologyRationalization X m
        ((eqToIso (congrArg (singularCohomology ℤ X) h)).hom a) =
      (eqToIso (congrArg (singularCohomology ℚ X) h)).hom
        (singularCohomologyRationalization X n a) := by
  subst m
  rfl

/-- The coefficient map preserves the original even cup product in its specified degree. -/
theorem singularCohomologyRationalization_evenCup (p q : ℕ)
    (a : singularCohomology ℤ X (2 * p)) (b : singularCohomology ℤ X (2 * q)) :
    singularCohomologyRationalization X (2 * (p + q))
        (singularCohomologyEvenCup ℤ X p q a b) =
      singularCohomologyEvenCup ℚ X p q
        (singularCohomologyRationalization X (2 * p) a)
        (singularCohomologyRationalization X (2 * q) b) := by
  -- The coefficient map commutes with the same total-degree identification.
  change singularCohomologyRationalization X (2 * (p + q))
      ((eqToIso (congrArg (singularCohomology ℤ X) (Nat.mul_add 2 p q).symm)).hom
        (singularCohomologyCup ℤ X (2 * p) (2 * q) a b)) =
    (eqToIso (congrArg (singularCohomology ℚ X) (Nat.mul_add 2 p q).symm)).hom
      (singularCohomologyCup ℚ X (2 * p) (2 * q)
        (singularCohomologyRationalization X (2 * p) a)
        (singularCohomologyRationalization X (2 * q) b))
  rw [rationalization_transport X _ _ (Nat.mul_add 2 p q).symm,
    singularCohomologyRationalization_cup]

/-- Rationalization evaluates elementary symmetric classes in the same rationalized roots. -/
theorem singularCohomologyRationalization_elementarySymmetric
    (xs : List (singularCohomology ℤ X 2)) (k : ℕ) :
    singularCohomologyRationalization X (2 * k)
        (singularCohomologyElementarySymmetric ℤ X xs k) =
      singularCohomologyElementarySymmetric ℚ X
        (xs.map (singularCohomologyRationalization X 2)) k := by
  -- The two recursions agree because the original coefficient map preserves unit, sum and cup.
  induction xs generalizing k with
  | nil =>
    cases k with
    | zero => exact singularCohomologyRationalization_one X
    | succ k => exact (singularCohomologyRationalization X (2 * (k + 1))).hom.map_zero
  | cons a xs ih =>
    cases k with
    | zero => exact singularCohomologyRationalization_one X
    | succ k =>
      simp only [singularCohomologyElementarySymmetric]
      rw [map_add, ih, rationalization_transport X _ _
        (congrArg (fun j ↦ 2 * j) (Nat.add_comm 1 k)),
        singularCohomologyRationalization_evenCup, ih]
      rfl

end AtiyahSinger
