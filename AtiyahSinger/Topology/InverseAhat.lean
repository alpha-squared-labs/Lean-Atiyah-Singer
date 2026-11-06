/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequenceParameter
public import AtiyahSinger.Topology.PontryaginAhat

/-!
# The actual degreewise inverse A-hat class

Public module ID: M1911.

SG III.11, Example 11.13 and Proposition 11.24. The inverse class is
constructed from the inverse of the already fixed rational characteristic
series, evaluated by the original finite cup-polynomial construction on the
same genuine Pontryagin classes. It is not an arbitrary inverse supplied as
input, nor division by a geometric cohomology class.

The characteristic series has constant coefficient one, so its formal inverse
exists. The displayed finite convolution identifies this construction with
the inverse of the previously defined original A-hat class in every degree.
Components outside degrees divisible by four are explicitly zero. No infinite
sum in direct-sum cohomology is formed. The original real bundle may have
locally varying rank over any base; a metric on its genuine complexification
is explicitly supplied, and independence is asserted below. Orientation,
compactness and a cohomological dimension bound are unnecessary.
Metric independence and zero normalization retain the original Pontryagin classes.
The finite inverse convolution follows from characteristic-series inversion,
with degree doubling expressed by substitution in a formal power series.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u v

variable {X : Type u} [TopologicalSpace X]
  (G : Type*) (V : X → Type v) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [IsFiniteRank G V]
  (h : letI := ComplexBundle.complexificationTopology G V
    ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] V x))

/-- The degree-4k inverse A-hat class uses the actual inverse characteristic series. -/
def inverseAHatClassComponent (k : ℕ) : singularCohomology ℚ X (2 * (2 * k)) :=
  singularCohomologyWeightedPolynomial X (fun i : Fin k ↦ 2 * (i.val + 1))
    (fun i ↦ singularCohomologyRationalization X (2 * (2 * (i.val + 1)))
      (pontryaginClass G V h (i.val + 1)))
    (MultiplicativeSequence.polynomial (aHatCharacteristicSeries⁻¹) k) (2 * k)

open Classical in
/-- The same inverse class as an even-degree family, zero in degrees not divisible by four. -/
def inverseAHatEvenComponent (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  if hk : Even k then
    (eqToIso (by
      rcases hk with ⟨j, hj⟩
      congr 1
      omega) : singularCohomology ℚ X (2 * (2 * (k / 2))) ≅
        singularCohomology ℚ X (2 * k)).hom (inverseAHatClassComponent G V h (k / 2))
  else 0

/-- The inverse A-hat construction is independent of the auxiliary complexification metric. -/
theorem inverseAHat_metric_independent
    (h' : letI := ComplexBundle.complexificationTopology G V
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] V x)) (k : ℕ) :
    inverseAHatClassComponent G V h k = inverseAHatClassComponent G V h' k ∧
      inverseAHatEvenComponent G V h k = inverseAHatEvenComponent G V h' k := by
  /- The integral Pontryagin classes of the original real bundle are
  independent of the two supplied metrics. Their rationalizations therefore
  give the same inputs to the same finite polynomial of the fixed inverse
  characteristic series. The parity inclusion uses only k and the identical
  degree transport, so it preserves this equality in every even degree. -/
  have hc (j : ℕ) : inverseAHatClassComponent G V h j =
      inverseAHatClassComponent G V h' j := by
    dsimp only [inverseAHatClassComponent]
    simp_rw [(pontryagin_aHat_metric_independent G V h h' _).1]
  refine ⟨hc k, ?_⟩
  -- The parity inclusion changes only the degree, using the same equality on both sides.
  dsimp only [inverseAHatEvenComponent]
  split_ifs with hk
  · rw [hc]
  · rfl

/-- The degree-zero inverse class is the original cohomological unit. -/
theorem inverseAHatEvenComponent_zero :
    inverseAHatEvenComponent G V h 0 = singularCohomologyOne ℚ X := by
  /- The original A-hat series has constant coefficient one, as does its
  formal inverse. Its degree-zero multiplicative-sequence polynomial is
  the constant one. The empty list of original cup factors evaluates to
  the cohomological unit, and the parity inclusion at zero is the identity. -/
  have hc : inverseAHatClassComponent G V h 0 = singularCohomologyOne ℚ X := by
    rw [inverseAHatClassComponent, MultiplicativeSequence.polynomial_zero]
    exact singularCohomologyWeightedPolynomial_one_zero X _ _
  unfold inverseAHatEvenComponent
  rw [dite_eq_left (show Even (0 : ℕ) from ⟨0, rfl⟩)]
  exact hc

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original A-hat and its constructed inverse multiply to one degree by degree. -/
theorem aHatEvenComponent_mul_inverse (k : ℕ) :
    (∑ i : Fin (k + 1),
      (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ X (2 * k)).hom
        (singularCohomologyEvenCup ℚ X i.val (k - i.val)
          (aHatEvenComponent G V h i.val) (inverseAHatEvenComponent G V h (k - i.val)))) =
      singularCohomologyDegreeTwoPow ℚ X (0 : singularCohomology ℚ X 2) k := by
  /- Stage 1: the actual characteristic series a has constant coefficient
  one, so a*a^(-1)=1 in rational formal power series. On independent formal
  Pontryagin roots, the product of the two finite-root series is therefore
  one. Compare coefficients and use the multiplicative-sequence symmetric
  polynomial characterization to obtain the universal finite identities.
  Stage 2: evaluate these identities on the rationalizations of the actual
  Pontryagin classes with the original even cup product. The same finite
  monomial evaluator and canonical degree transports preserve the identities.
  Stage 3: include the degree-4j components as the specified even families.
  For odd k each convolution term has one zero factor. For even k the
  identity is exactly the coefficient calculation. The right side is one
  at k=0 and zero otherwise, using the original zeroth-power convention.
  This uses a unit formal series, never cancellation or division by Euler. -/
  classical
  let b : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X (2 * j)
      (singularCohomologyRationalization X (2 * (2 * j)) (pontryaginClass G V h j))
  -- Doubling all input weights doubles the homogeneous degree of every surviving monomial.
  have hweight (q : PowerSeries ℚ) (j : ℕ) :
      (MultiplicativeSequence.polynomial q j).IsWeightedHomogeneous
        (fun i : Fin j ↦ 2 * (i.val + 1)) (2 * j) := by
    intro d hd
    have hw := MultiplicativeSequence.polynomial_isWeightedHomogeneous q j hd
    calc
      Finsupp.weight (fun i : Fin j ↦ 2 * (i.val + 1)) d =
          2 * Finsupp.weight (fun i : Fin j ↦ i.val + 1) d := by
        simp [Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum, mul_left_comm]
      _ = 2 * j := congrArg (2 * ·) hw
  have ha (j : ℕ) : singularEvenCohomologyOf ℚ X (2 * j) (aHatClassComponent G V h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform aHatCharacteristicSeries b) := by
    simp only [aHatClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, b]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ (2 * j) (hweight _ j)
  have hi (j : ℕ) :
      singularEvenCohomologyOf ℚ X (2 * j) (inverseAHatClassComponent G V h j) =
        PowerSeries.coeff j (MultiplicativeSequence.transform aHatCharacteristicSeries⁻¹ b) := by
    simp only [inverseAHatClassComponent, MultiplicativeSequence.transform,
      PowerSeries.coeff_mk, b]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ (2 * j) (hweight _ j)
  -- The original parity inclusions are exactly substitution t ↦ t² in these coefficient series.
  have haEven (j : ℕ) : singularEvenCohomologyOf ℚ X j (aHatEvenComponent G V h j) =
      PowerSeries.coeff j (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries b)) := by
    unfold aHatEvenComponent
    rw [PowerSeries.coeff_expand]
    by_cases hj : Even j
    · have hdvd : 2 ∣ j := hj.two_dvd
      rw [dite_eq_left hj, ite_eq_left hdvd,
        singularEvenCohomologyOf_eqToIso ℚ X (Nat.mul_div_cancel' hdvd), ha]
    · have hdvd : ¬ 2 ∣ j := fun h ↦ hj (even_iff_two_dvd.mpr h)
      rw [dite_eq_right hj, ite_eq_right hdvd, map_zero]
  have hiEven (j : ℕ) : singularEvenCohomologyOf ℚ X j (inverseAHatEvenComponent G V h j) =
      PowerSeries.coeff j (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries⁻¹ b)) := by
    unfold inverseAHatEvenComponent
    rw [PowerSeries.coeff_expand]
    by_cases hj : Even j
    · have hdvd : 2 ∣ j := hj.two_dvd
      rw [dite_eq_left hj, ite_eq_left hdvd,
        singularEvenCohomologyOf_eqToIso ℚ X (Nat.mul_div_cancel' hdvd), hi]
    · have hdvd : ¬ 2 ∣ j := fun h ↦ hj (even_iff_two_dvd.mpr h)
      rw [dite_eq_right hj, ite_eq_right hdvd, map_zero]
  apply singularEvenCohomologyOf_injective ℚ X k
  rw [map_sum]
  -- Each original degree transport gives precisely the corresponding Cauchy-product term.
  have hterm (i : Fin (k + 1)) :
      singularEvenCohomologyOf ℚ X k
          ((eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
              singularCohomology ℚ X (2 * k)).hom
            (singularCohomologyEvenCup ℚ X i.val (k - i.val)
              (aHatEvenComponent G V h i.val)
              (inverseAHatEvenComponent G V h (k - i.val)))) =
        PowerSeries.coeff i.val (PowerSeries.expand 2 (by decide)
            (MultiplicativeSequence.transform aHatCharacteristicSeries b)) *
          PowerSeries.coeff (k - i.val) (PowerSeries.expand 2 (by decide)
            (MultiplicativeSequence.transform aHatCharacteristicSeries⁻¹ b)) := by
    rw [singularEvenCohomologyOf_eqToIso ℚ X
      (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup,
      haEven, hiEven]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦
    PowerSeries.coeff j (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries b)) *
      PowerSeries.coeff (k - j) (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries⁻¹ b))) (k + 1)]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
    PowerSeries.coeff i (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries b)) *
      PowerSeries.coeff j (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries⁻¹ b))) k,
    ← PowerSeries.coeff_mul, ← map_mul, MultiplicativeSequence.transform_mul_inv
      aHatCharacteristicSeries characteristicSeries_normalization.2.1, map_one]
  -- Substitution preserves the unit series, including the original degree-zero cohomology unit.
  rw [singularEvenCohomologyOf_degreeTwoPow, map_zero]
  cases k <;> simp

end AtiyahSinger.RealBundle
