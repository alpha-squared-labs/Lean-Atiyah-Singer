/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyPowerChangeCoefficients
public import AtiyahSinger.Topology.ProjectiveChernTopClass
public import AtiyahSinger.Topology.RelativeSingularCohomologyChangeCoefficients

/-!
# The specified projective top class over an arbitrary coefficient ring

Public module ID: M2009.

Normalized coefficient change retains the actual point support, the original
affine chart and the original tautological power. No flatness, characteristic
or nontriviality assumption on the coefficient ring is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open CategoryTheory

universe u

variable (R : Type) [CommRing R]
  (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Forgetting the point support after coefficient change gives the same tautological power. -/
theorem projectiveTopSectionClass_changeCoefficients_toOrdinary
    (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker) :
    relativeSingularCohomologyToOrdinary R {P | P ≠ ofVector e hne} (2 * m)
        (relativeSingularCohomologyChangeCoefficients R {P | P ≠ ofVector e hne} (2 * m)
          (projectiveTopSectionClass V m e he hne b)) =
      singularCohomologyDegreeTwoPow R (HermitianProjectiveSpace V InnerProductSpace.toCore)
        (singularCohomologyChangeCoefficients R
          (HermitianProjectiveSpace V InnerProductSpace.toCore) 2 (tautologicalChernRoot V)) m := by
  rw [← relativeSingularCohomologyChangeCoefficients_toOrdinary,
    projectiveTopSectionClass_toOrdinary, singularCohomologyChangeCoefficients_degreeTwoPow]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same affine chart identifies the class with the same coordinate cup over any ring. -/
theorem projectiveTopSectionClass_changeCoefficients_pullback [FiniteDimensional ℂ V]
    (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker) :
    relativeSingularCohomologyPullback R (chartEmbedding e he)
        (A := {v | v ≠ 0}) (B := {P | P ≠ ofVector e hne})
        (fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)) (2 * m)
        (relativeSingularCohomologyChangeCoefficients R {P | P ≠ ofVector e hne} (2 * m)
          (projectiveTopSectionClass V m e he hne b)) =
      relativeSingularCohomologyChangeCoefficients R {v | v ≠ 0} (2 * m)
        (complexCoordinateCup m b) := by
  rw [← relativeSingularCohomologyChangeCoefficients_naturality,
    projectiveTopSectionClass_pullback]

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
