/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HalfSpinorKCharacter

/-!
# The ordinary half-spinor formula on a compact Hausdorff base

Public module ID: M1638.

This is the compact Hausdorff case of the original ordinary half-spinor formula
in SR05, with the same spin structure, geometric Euler normalization and actual
inverse A-hat class. It follows from the proved formula for the original virtual
half-spin K class and the bundle-value theorem for its Chern character.

The latter comparison uses the two specified metrics on the original associated
bundles. Compactness is used only in this separate compact-base theorem; the
arbitrary-base formula in `HalfSpinorCharacter` uses the independently proved
compact-Hausdorff test-source detection theorem.

Source: Lawson--Michelsohn, Spin Geometry, III.11, Proposition 11.24, p.238.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

universe u v

variable {m : ℕ} {B : Type u} {P : Type v} {E : B → Type u}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [CompactSpace B] [T2Space B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

/-- The original ordinary half-spinor formula on a compact Hausdorff base. -/
theorem TopologicalSpinStructure.halfSpinorCharacterComponent_add_of_compactSpace
    (S : TopologicalSpinStructure m E o hm hP)
    (hPlus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 0))
    (hMinus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 1))
    (hV : letI := (ComplexBundle.complexificationTopology
        (EuclideanSpace ℝ (Fin (2 * m))) E)
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (j : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle
      (EuclideanSpace ℝ (Fin (2 * m))) E
    halfSpinorCharacterComponent m hP hPlus hMinus (m + j) =
      (-1 : ℚ) ^ m • singularCohomologyEvenCup ℚ B m j S.rationalEulerClass
        (RealBundle.inverseAHatEvenComponent
          (EuclideanSpace ℝ (Fin (2 * m))) E hV j) := by
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  let := RealBundle.isFiniteRank_of_vectorBundle
    (EuclideanSpace ℝ (Fin (2 * m))) E
  -- Use the proved virtual-class formula with the same spin structure and complexification.
  have h := S.chernCharacter_halfSpinor_difference_add hV j
  -- Evaluate its two original bundle classes using the supplied metrics, preserving parity.
  rw [map_sub,
    chernCharacterKZeroComponent_bundle (HalfSpinorBundle m hP 0) hPlus,
    chernCharacterKZeroComponent_bundle (HalfSpinorBundle m hP 1) hMinus] at h
  exact h

end AtiyahSinger
