/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.InverseAhat
public import AtiyahSinger.Topology.InverseTodd

/-!
# Inverse Todd of the original real complexification

Public module ID: M1730.

The existing Todd–A-hat identity identifies the actual Todd series with
A-hat squared. Both inverse characteristic classes are the original polynomial
constructions, with their established unit identities. Uniqueness of a formal
unit inverse therefore identifies inverse Todd with inverse A-hat squared.
The argument works in the even cohomology ring with its possible zero divisors.

Source: SG III.11, the inverse form of the characteristic identity in
Proposition 11.14, using the same original complexification and supplied metric.
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

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Inverse Todd of the actual complexification is the square of the actual inverse A-hat. -/
theorem inverseTodd_complexification_eq_inverseAHat_sq (k : ℕ) :
    letI := ComplexBundle.complexificationTopology G V
    letI := isFiniteRank_complexification G V
    ComplexBundle.inverseToddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenCup ℚ X i.val (k - i.val)
            (inverseAHatEvenComponent G V h i.val)
            (inverseAHatEvenComponent G V h (k - i.val))) := by
  classical
  let := ComplexBundle.complexificationTopology G V
  let := isFiniteRank_complexification G V
  let R := SingularEvenCohomology ℚ X
  let series (a : ∀ j, singularCohomology ℚ X (2 * j)) : PowerSeries R :=
    PowerSeries.mk (fun j ↦ singularEvenCohomologyOf ℚ X j (a j))
  have hcoeff (a b : PowerSeries R) (n : ℕ) :
      PowerSeries.coeff n (a * b) =
        ∑ i : Fin (n + 1), PowerSeries.coeff i.val a * PowerSeries.coeff (n - i.val) b := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ PowerSeries.coeff i a * PowerSeries.coeff j b) n,
      Fin.sum_univ_eq_sum_range
        (fun i ↦ PowerSeries.coeff i a * PowerSeries.coeff (n - i) b) (n + 1)]
  have hconv (a b : ∀ j, singularCohomology ℚ X (2 * j)) (n : ℕ) :
      singularEvenCohomologyOf ℚ X n (∑ i : Fin (n + 1),
        (eqToIso (by congr 1; omega) :
          singularCohomology ℚ X (2 * (i.val + (n - i.val))) ≅
            singularCohomology ℚ X (2 * n)).hom
          (singularCohomologyEvenCup ℚ X i.val (n - i.val) (a i.val) (b (n - i.val)))) =
        PowerSeries.coeff n (series a * series b) := by
    rw [map_sum, hcoeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso ℚ X (by omega), singularEvenCohomologyOf_cup]
    simp only [series, PowerSeries.coeff_mk]
  let A := series (aHatEvenComponent G V h)
  let I := series (inverseAHatEvenComponent G V h)
  let T := series (ComplexBundle.toddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h)
  let J := series (ComplexBundle.inverseToddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h)
  -- Both prescribed inverse classes invert their own prescribed characteristic series.
  have hAI : A * I = 1 := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n
      (series (aHatEvenComponent G V h) * series (inverseAHatEvenComponent G V h)) = _
    rw [← hconv (aHatEvenComponent G V h) (inverseAHatEvenComponent G V h) n,
      aHatEvenComponent_mul_inverse G V h,
      singularEvenCohomologyOf_degreeTwoPow, map_zero]
    cases n <;> simp
  have hTJ : T * J = 1 := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n
      (series (ComplexBundle.toddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h) *
        series (ComplexBundle.inverseToddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h)) = _
    rw [← hconv, ComplexBundle.toddClassComponent_mul_inverse,
      singularEvenCohomologyOf_degreeTwoPow, map_zero]
    cases n <;> simp
  have hT : T = A * A := by
    apply PowerSeries.ext
    intro n
    simp only [T, series, PowerSeries.coeff_mk]
    rw [todd_complexification_eq_aHat_sq G V h, hconv]
  -- Cancellation uses the unit series A, and never a geometric Euler class.
  have hinv : (I * I) * (A * A) = 1 := by
    calc
      (I * I) * (A * A) = (A * I) * (A * I) := by ring
      _ = 1 := by rw [hAI, mul_one]
  have hJ : J = I * I := by
    calc
      J = ((I * I) * (A * A)) * J := by rw [hinv, one_mul]
      _ = (I * I) * ((A * A) * J) := by rw [mul_assoc]
      _ = I * I := by rw [← hT, hTJ, mul_one]
  apply singularEvenCohomologyOf_injective ℚ X k
  rw [hconv]
  simpa only [J, series, PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) hJ

end AtiyahSinger.RealBundle
