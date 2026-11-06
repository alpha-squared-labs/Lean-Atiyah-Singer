/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacterKZero
public import AtiyahSinger.Topology.EvenCohomologyWeightedComponents
public import AtiyahSinger.Topology.InverseAhat
public import AtiyahSinger.Topology.ZeroHalfSpinorCharacter
public import AtiyahSinger.Topology.ZeroRankEuler

/-!
# The rank-zero endpoint of the half-spinor character formula

Public module ID: M2274.

SR05. The existing positive-rank theorem uses a geometric spin frame lift.
At rank zero the native unit-vector-generated Spin(0) is trivial instead.
The original associated positive bundle has its normalized vacuum
trivialization and the negative bundle is zero. The original real rank-zero
bundle has the canonical empty-basis orientation, whose normalized Euler
class is the unit. Its actual inverse A-hat class is the degreewise unit.

These statements give the ordinary and compact-base K character formulas
using the same original principal certificate, associated quotient fibers,
real bundle topology and tensor complexification. They are the degenerate
extension of SG III.11, Proposition 11.24, not an additional numbered lemma
in the book. The canonical rank-zero orientation is explicit: a negative
native orientation ray is not identified with a positive empty basis.
The alternative stable two-sheeted Spin(0) convention is not used.

The ordinary theorem supplies metrics on the three original complex bundles;
the compact Hausdorff K statement eliminates the two half-spin metrics by
their existing existence theorem. All three comparisons retain the original objects.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

universe u v

variable {B : Type u} [TopologicalSpace B]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]

local notation "RealModel" => EuclideanSpace ℝ (Fin 0)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual inverse A-hat class of a rank-zero real bundle is the degreewise unit. -/
theorem RealBundle.inverseAHatEvenComponent_rank_zero
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) (k : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    RealBundle.inverseAHatEvenComponent RealModel E hV k =
      singularCohomologyDegreeTwoPow ℚ B (0 : singularCohomology ℚ B 2) k := by
  classical
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let := complexificationTopology RealModel E
  let := RealBundle.isFiniteRank_complexification RealModel E
  let V := fun x ↦ ℂ ⊗[ℝ] E x
  -- Native charts force every real fiber vector, hence its scalar extension, to vanish.
  let : ∀ x, Subsingleton (E x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ RealModel E x).injective.subsingleton
  let : ∀ x, Subsingleton (V x) := fun x ↦ by
    have hz (v : V x) : v = 0 := by
      induction v using TensorProduct.inductionOn with
      | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩
  have hr (x : B) : Module.finrank ℂ (V x) = 0 := Module.finrank_zero_of_subsingleton
  have hchern (j : ℕ) (hj : 0 < j) : globalChernClass V hV j = 0 := by
    have hc := globalChernClass_pullback_eq_chernClass V hV (ContinuousMap.id B)
      V hV 0 hr (pullbackIdIso (E := V)).symm j
    have hid : singularCohomologyPullback ℤ (ContinuousMap.id B) (2 * j) =
        𝟙 (singularCohomology ℤ B (2 * j)) := (singularCohomologyFunctor ℤ (2 * j)).map_id _
    rw [hid, ModuleCat.id_apply] at hc
    rw [hc]
    let : ∀ x, NormedAddCommGroup (V x) := hV.fiberNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (V x) := hV.fiberInnerProductSpace
    let := nativeModelTopology V (EuclideanSpace ℂ (Fin 0))
    let := hV.nativeFiberBundle 0 hr
    let := hV.nativeVectorBundle 0 hr
    exact chernClass_eq_zero_of_rank_lt 0 V (hV.nativeModelMetric 0) j hj
  have hpontryagin (j : ℕ) (hj : 0 < j) :
      RealBundle.pontryaginClass RealModel E hV j = 0 := by
    change (-1 : ℤ) ^ j • globalChernClass V hV (2 * j) = 0
    rw [hchern _ (by omega)]
    exact zsmul_zero _
  have hinverse (j : ℕ) (hj : 0 < j) :
      RealBundle.inverseAHatClassComponent RealModel E hV j = 0 := by
    -- Positive-weight universal polynomials have no constant monomial at the zero Chern input.
    rw [RealBundle.inverseAHatClassComponent,
      singularCohomologyWeightedPolynomial_eq_component]
    simp_rw [hpontryagin _ (Nat.succ_pos _), map_zero]
    have hconstant : MvPolynomial.constantCoeff
        (MultiplicativeSequence.polynomial (aHatCharacteristicSeries⁻¹) j) = 0 :=
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous _ j).coeff_eq_zero 0
        (by simpa using (Nat.ne_of_gt hj).symm)
    simp only [MvPolynomial.aeval_zero', hconstant, map_zero]
  cases k with
  | zero => exact RealBundle.inverseAHatEvenComponent_zero RealModel E hV
  | succ k =>
    -- The original parity inclusion is zero in odd indices, and transports zero otherwise.
    rw [RealBundle.inverseAHatEvenComponent]
    split_ifs with hk
    · have hj : 0 < (k + 1) / 2 := by
        obtain ⟨j, hj⟩ := hk
        omega
      rw [hinverse _ hj, map_zero]
      simp only [singularCohomologyDegreeTwoPow, singularCohomologyEvenCup,
        map_zero, LinearMap.zero_apply]
    · simp only [singularCohomologyDegreeTwoPow, singularCohomologyEvenCup,
        map_zero, LinearMap.zero_apply]

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

variable {P : Type v} [TopologicalSpace P]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

local notation "SpinPlus" => HalfSpinorBundle 0 hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle 0 hP (1 : ZMod 2)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native rank-zero half-spin difference equals its canonical Euler times inverse A-hat. -/
theorem halfSpinorCharacterComponent_zero_eq_euler_mul_inverseAHat
    (hPlus : ContinuousHermitianMetric SpinPlus)
    (hMinus : ContinuousHermitianMetric SpinMinus)
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) (k : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    halfSpinorCharacterComponent 0 hP hPlus hMinus (0 + k) =
      (-1 : ℚ) ^ 0 • singularCohomologyEvenCup ℚ B 0 k (zeroRankRationalEulerClass E)
        (RealBundle.inverseAHatEvenComponent RealModel E hV k) := by
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  rw [halfSpinorCharacterComponent_zero, zeroRankRationalEulerClass_eq_one,
    RealBundle.inverseAHatEvenComponent_rank_zero, pow_zero, one_smul]
  -- Homogeneous inclusion turns the same degree-zero cup into the ordinary unit law.
  have hunit := singularEvenCohomologyOf_cup ℚ B 0 k (singularCohomologyOne ℚ B)
    (singularCohomologyDegreeTwoPow ℚ B 0 k)
  rw [singularEvenCohomologyOf_one, one_mul] at hunit
  have hof := congrArg (fun j ↦ singularEvenCohomologyOf ℚ B j
    (singularCohomologyDegreeTwoPow ℚ B 0 j)) (Nat.zero_add k)
  exact (singularEvenCohomologyOf_injective ℚ B (0 + k) (hunit.trans hof.symm)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original compact-base virtual half-spin class satisfies the rank-zero character formula. -/
theorem chernCharacter_halfSpinor_zero_difference [CompactSpace B] [T2Space B]
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) (k : ℕ) :
    letI := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
      (continuous_complexSpinParityRepresentation 0 0)
    letI := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
      (continuous_complexSpinParityRepresentation 0 1)
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    chernCharacterKZeroComponent B (0 + k)
      (ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus) =
      (-1 : ℚ) ^ 0 • singularCohomologyEvenCup ℚ B 0 k (zeroRankRationalEulerClass E)
        (RealBundle.inverseAHatEvenComponent RealModel E hV k) := by
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
    (continuous_complexSpinParityRepresentation 0 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
    (continuous_complexSpinParityRepresentation 0 1)
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let hPlus := (nonempty_continuousHermitianMetric SpinPlus).some
  let hMinus := (nonempty_continuousHermitianMetric SpinMinus).some
  -- The K-class difference uses the same associated bundles as the ordinary formula.
  rw [map_sub, chernCharacterKZeroComponent_bundle SpinPlus hPlus,
    chernCharacterKZeroComponent_bundle SpinMinus hMinus]
  exact halfSpinorCharacterComponent_zero_eq_euler_mul_inverseAHat E hP hPlus hMinus hV k

end AtiyahSinger
