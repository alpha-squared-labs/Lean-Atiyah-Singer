/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequenceParameter
public import AtiyahSinger.Topology.ToddClass

/-!
# The actual degreewise inverse Todd class

Public module ID: M1912.

SG III.11, Example 11.11 and III.12, equations (12.10)--(12.11).
Evaluate the multiplicative-sequence polynomial of the inverse of the
original normalized Todd series on the same genuine integral Chern classes.
Its finite convolution with the existing Todd class is the cohomological
unit. This is inversion of a unit formal series, not division by Euler or
another geometric cohomology class and not an assumed target invariant.

The original bundle can have locally varying rank over an arbitrary base.
The supplied Hermitian metric presents the Chern classes and does not affect
the result. Only finite degreewise expressions are formed; no dimension bound
or unsupported infinite sum in direct-sum cohomology is required. The complex
Thom formula uses these same components and records the conjugation degree
sign in that formula, without introducing a replacement conjugate bundle.
Metric independence and zero normalization retain the original Chern classes.
The finite inverse convolution follows by multiplying the characteristic-series
parameters and evaluating their coefficients in the even cohomology ring.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

/-- The degree-2k inverse Todd class uses the inverse series and original Chern classes. -/
def inverseToddClassComponent (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  singularCohomologyWeightedPolynomial X (fun i : Fin k ↦ i.val + 1)
    (fun i ↦ singularCohomologyRationalization X (2 * (i.val + 1))
      (globalChernClass E h (i.val + 1)))
    (MultiplicativeSequence.polynomial (toddCharacteristicSeries⁻¹) k) k

/-- The inverse Todd construction is independent of the original bundle's auxiliary metric. -/
theorem inverseToddClassComponent_metric_independent
    (h' : ContinuousHermitianMetric E) (k : ℕ) :
    inverseToddClassComponent E h k = inverseToddClassComponent E h' k := by
  /- The original integral globalChernClass is metric-independent in every
  degree. Rationalization therefore gives the same finite list of inputs
  to the same fixed inverse-series polynomial. The original cup product
  and degree transports in its evaluation are unchanged. No comparison
  between unrelated bundle models or global splitting choice is needed. -/
  dsimp only [inverseToddClassComponent]
  simp_rw [globalChernClass_metric_independent E h h']

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degree-zero inverse Todd component is the original cohomological unit. -/
theorem inverseToddClassComponent_zero :
    inverseToddClassComponent E h 0 = singularCohomologyOne ℚ X := by
  /- The normalized Todd characteristic series has constant coefficient
  one, so its inverse has the same constant coefficient. The degree-zero
  multiplicative-sequence polynomial is consequently the constant one.
  Evaluating its empty product gives the original cohomological unit,
  including rank-zero bundles and the empty base. -/
  rw [inverseToddClassComponent, MultiplicativeSequence.polynomial_zero,
    singularCohomologyWeightedPolynomial_one_zero]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The existing Todd class and this specified inverse have unit finite cup convolution. -/
theorem toddClassComponent_mul_inverse (k : ℕ) :
    (∑ i : Fin (k + 1),
      (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ X (2 * k)).hom
        (singularCohomologyEvenCup ℚ X i.val (k - i.val)
          (toddClassComponent E h i.val) (inverseToddClassComponent E h (k - i.val)))) =
      singularCohomologyDegreeTwoPow ℚ X (0 : singularCohomology ℚ X 2) k := by
  /- Stage 1: the original normalized Todd series t is a unit in rational
  formal power series, with t*t^(-1)=1. Take finite products over independent
  formal Chern roots and compare the coefficient of each degree. The
  multiplicative-sequence symmetric-polynomial characterization expresses
  this coefficient identity in the elementary symmetric variables.
  Stage 2: evaluate that identity on the rationalizations of the original
  global Chern classes of E. The finite weighted-polynomial evaluator uses
  the existing even cup product and its canonical degree transports. It
  therefore gives exactly the displayed convolution of the two original
  component families, without choosing actual roots on X.
  Stage 3: the coefficient of the constant series one is the original unit
  in degree zero and zero in positive degrees. The existing degree-two
  power convention on zero expresses both cases on the right. No Euler
  cancellation, connectedness, fixed rank or cohomological bound is used. -/
  classical
  let b : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j
      (singularCohomologyRationalization X (2 * j) (globalChernClass E h j))
  -- The two original weighted evaluations use identical Chern inputs and cup products.
  have ht (j : ℕ) : singularEvenCohomologyOf ℚ X j (toddClassComponent E h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries b) := by
    simp only [toddClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, b]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ j
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous toddCharacteristicSeries j)
  have hi (j : ℕ) : singularEvenCohomologyOf ℚ X j (inverseToddClassComponent E h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries⁻¹ b) := by
    simp only [inverseToddClassComponent, MultiplicativeSequence.transform,
      PowerSeries.coeff_mk, b]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ j
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous toddCharacteristicSeries⁻¹ j)
  apply singularEvenCohomologyOf_injective ℚ X k
  rw [map_sum]
  -- Homogeneous inclusion preserves each canonical transport in the displayed convolution.
  have hterm (i : Fin (k + 1)) :
      singularEvenCohomologyOf ℚ X k
          ((eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
              singularCohomology ℚ X (2 * k)).hom
            (singularCohomologyEvenCup ℚ X i.val (k - i.val)
              (toddClassComponent E h i.val) (inverseToddClassComponent E h (k - i.val)))) =
        PowerSeries.coeff i.val (MultiplicativeSequence.transform toddCharacteristicSeries b) *
          PowerSeries.coeff (k - i.val)
            (MultiplicativeSequence.transform toddCharacteristicSeries⁻¹ b) := by
    rw [singularEvenCohomologyOf_eqToIso ℚ X
      (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup, ht, hi]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦
    PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries b) *
      PowerSeries.coeff (k - j) (MultiplicativeSequence.transform toddCharacteristicSeries⁻¹ b))
    (k + 1)]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
    PowerSeries.coeff i (MultiplicativeSequence.transform toddCharacteristicSeries b) *
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries⁻¹ b)) k,
    ← PowerSeries.coeff_mul, MultiplicativeSequence.transform_mul_inv
      toddCharacteristicSeries characteristicSeries_normalization.1]
  -- The resulting unit series has precisely the original zeroth cup power and zero higher terms.
  rw [singularEvenCohomologyOf_degreeTwoPow, map_zero]
  cases k <;> simp

end AtiyahSinger.ComplexBundle
