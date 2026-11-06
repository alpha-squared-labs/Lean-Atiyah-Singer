/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomials

/-!
# Homogeneous combinations of a degree-two cohomology class

Public module ID: M2136.

Coefficients in the original cohomology groups multiply the specified powers
of one degree-two class after pullback. This is the ordinary degreewise form
of the finite Leray--Hirsch comparison, used to recover projective Chern
coefficients. Only the canonical equality of total degrees is transported.
The construction alone asserts no basis or uniqueness theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual homogeneous sum of pulled-back coefficients times powers of the given class. -/
def singularCohomologyPowerCombination (π : C(Y, X)) (t : singularCohomology R Y 2)
    (r n : ℕ) (hn : ∀ i : Fin r, i.val ≤ n) :
    (∀ i : Fin r, singularCohomology R X (2 * (n - i.val))) →ₗ[R]
      singularCohomology R Y (2 * n) :=
  ∑ i : Fin r,
    ((eqToIso (congrArg (fun k ↦ singularCohomology R Y (2 * k))
      (Nat.sub_add_cancel (hn i)))).hom.hom).comp
      (((singularCohomologyEvenCup R Y (n - i.val) i.val).flip
        (singularCohomologyDegreeTwoPow R Y t i.val)).comp
          ((singularCohomologyPullback R π (2 * (n - i.val))).hom.comp (LinearMap.proj i)))

/-- Evaluation retains the same ordered pullback, cup power and total-degree transport. -/
theorem singularCohomologyPowerCombination_apply (π : C(Y, X))
    (t : singularCohomology R Y 2) (r n : ℕ) (hn : ∀ i : Fin r, i.val ≤ n)
    (a : ∀ i : Fin r, singularCohomology R X (2 * (n - i.val))) :
    singularCohomologyPowerCombination R π t r n hn a =
      ∑ i : Fin r, (eqToIso (congrArg (fun k ↦ singularCohomology R Y (2 * k))
        (Nat.sub_add_cancel (hn i)))).hom
        (singularCohomologyEvenCup R Y (n - i.val) i.val
          (singularCohomologyPullback R π (2 * (n - i.val)) (a i))
          (singularCohomologyDegreeTwoPow R Y t i.val)) := by
  simp only [singularCohomologyPowerCombination, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, LinearMap.proj_apply]

end AtiyahSinger
