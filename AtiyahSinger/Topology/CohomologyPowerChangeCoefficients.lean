/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomials
public import AtiyahSinger.Topology.SingularCohomologyChangeCoefficients

/-!
# Coefficient change of the original degree-two powers

Public module ID: M1624.

The integral power of a specified class maps to the same power of its image
over any commutative coefficient ring. The proof keeps the original cup
product and both canonical degree transports. This is used for the actual
tautological class in the projective bundle theorem over arbitrary rings.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Normalized coefficient change preserves every original degree-two cup power. -/
theorem singularCohomologyChangeCoefficients_degreeTwoPow (R : Type) [CommRing R]
    (X : Type u) [TopologicalSpace X] (t : singularCohomology ℤ X 2) (n : ℕ) :
    singularCohomologyChangeCoefficients R X (2 * n)
        (singularCohomologyDegreeTwoPow ℤ X t n) =
      singularCohomologyDegreeTwoPow R X (singularCohomologyChangeCoefficients R X 2 t) n := by
  have htransport (p q : ℕ) (h : p = q) (a : singularCohomology ℤ X p) :
      singularCohomologyChangeCoefficients R X q
          ((eqToIso (congrArg (singularCohomology ℤ X) h)).hom a) =
        (eqToIso (congrArg (singularCohomology R X) h)).hom
          (singularCohomologyChangeCoefficients R X p a) := by
    subst q
    rfl
  induction n with
  | zero => exact singularCohomologyChangeCoefficients_one R X
  | succ n ih =>
    -- The cup comparison preserves the same two factors before changing their total degree.
    simp only [singularCohomologyDegreeTwoPow, singularCohomologyEvenCup,
      LinearMap.compr₂_apply]
    rw [htransport, htransport, singularCohomologyChangeCoefficients_cup, ih] <;> omega

end AtiyahSinger
