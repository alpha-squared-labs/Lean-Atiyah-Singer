/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequence
public import AtiyahSinger.Topology.EvenCohomologyPolynomials
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Characteristic series and finite evaluation in the original even cohomology

Public module ID: M1603.

C02, SG III.11, Examples 11.11 and 11.13 and Proposition 11.14. The Todd
and A-hat series are actual inverses of rational power series with constant
coefficient one. This interprets x/(1-exp(-x)) and sqrt(x)/2/sinh(sqrt(x)/2)
without division by a nonunit or introducing a formal square-root variable.

Weighted polynomial evaluation below uses precisely the original cup product.
It expands each finite polynomial monomial into an ordered list of factors,
cups their actual even cohomology classes, and keeps its specified homogeneous
degree. For the universal multiplicative-sequence polynomials, weighted
homogeneity ensures that every nonzero monomial has that degree. No total
cohomology ring, infinite cohomology sum or arbitrary polynomial evaluator
is assumed as input. The implementation is shared by Todd and A-hat classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

/-- The Todd characteristic series, interpreted as the inverse of (1-exp(-x))/x. -/
def toddCharacteristicSeries : PowerSeries ℚ :=
  (PowerSeries.mk fun k : ℕ ↦ (-1 : ℚ) ^ k / (Nat.factorial (k + 1) : ℚ))⁻¹

/-- The A-hat series in a Pontryagin-root variable, the inverse of sinh(sqrt(x)/2)/(sqrt(x)/2). -/
def aHatCharacteristicSeries : PowerSeries ℚ :=
  (PowerSeries.mk fun k : ℕ ↦
    ((2 : ℚ) ^ (2 * k) * (Nat.factorial (2 * k + 1) : ℚ))⁻¹)⁻¹

/-- The actual characteristic series have their standard unit normalization and first terms. -/
theorem characteristicSeries_normalization :
    toddCharacteristicSeries.constantCoeff = 1 ∧
      aHatCharacteristicSeries.constantCoeff = 1 ∧
      PowerSeries.coeff 1 toddCharacteristicSeries = (1 / 2 : ℚ) ∧
      PowerSeries.coeff 1 aHatCharacteristicSeries = (-1 / 24 : ℚ) := by
  /- The two denominator series have constant coefficient one, so their
  formal inverses have constant coefficient one. Compare their linear
  coefficients in the product identities: the denominators have coefficients
  -1/2 and 1/24 respectively, giving the displayed signs. The A-hat variable
  is the square of a degree-two root, not that degree-two root itself. -/
  -- Both normalized denominators have constant term one.
  have ht : toddCharacteristicSeries.constantCoeff = 1 := by
    norm_num [toddCharacteristicSeries]
  have ha : aHatCharacteristicSeries.constantCoeff = 1 := by
    norm_num [aHatCharacteristicSeries]
  refine ⟨ht, ha, ?_, ?_⟩
  · rw [toddCharacteristicSeries, PowerSeries.coeff_inv]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      PowerSeries.coeff_zero_eq_constantCoeff, Nat.factorial]
  · rw [aHatCharacteristicSeries, PowerSeries.coeff_inv]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      PowerSeries.coeff_zero_eq_constantCoeff, Nat.factorial]

/-- The paired-root identity underlying the geometric Todd/A-hat square formula. -/
theorem toddCharacteristicSeries_mul_evalNeg :
    toddCharacteristicSeries * PowerSeries.evalNegHom toddCharacteristicSeries =
      (PowerSeries.expand 2 (by decide) aHatCharacteristicSeries) ^ 2 := by
  /- Stage 1: multiply the normalized denominators, all of which are units.
  The exponential identity exp(x)exp(-x)=1 identifies
  ((1-exp(-x))/x)((exp(x)-1)/x) with (2*sinh(x/2)/x)^2.
  Each quotient notation here abbreviates its displayed factorial series,
  so this step is coefficientwise formal algebra, not division by x.
  Stage 2: invert the unit identity. The A-hat denominator has only even
  root powers; expand by two substitutes x^2 into its Pontryagin-root series.
  This gives precisely td(x)td(-x)=a(x^2)^2, including the constant terms. -/
  let d : PowerSeries ℚ := PowerSeries.mk fun k : ℕ ↦
    (-1 : ℚ) ^ k / (Nat.factorial (k + 1) : ℚ)
  let h : PowerSeries ℚ := PowerSeries.mk fun k : ℕ ↦
    ((2 : ℚ) ^ (2 * k) * (Nat.factorial (2 * k + 1) : ℚ))⁻¹
  let H := PowerSeries.expand 2 (by decide) h
  let E (a : ℚ) : PowerSeries ℚ := PowerSeries.rescale a (PowerSeries.exp ℚ)
  have hEzero (a : ℚ) : (E a).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff 0 (PowerSeries.rescale a (PowerSeries.exp ℚ)) = 1
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    norm_num
  -- Identify the original normalized denominators after multiplication by X.
  have hd : PowerSeries.X * d = 1 - E (-1) := by
    ext n
    cases n with
    | zero => simp [hEzero]
    | succ n => simp [d, E, pow_succ, div_eq_mul_inv]
  have hdneg : PowerSeries.X * PowerSeries.evalNegHom d = E 1 - 1 := by
    have he := congrArg PowerSeries.evalNegHom hd
    simp only [map_mul, PowerSeries.evalNegHom_X, map_sub, map_one] at he
    have hee : PowerSeries.evalNegHom (E (-1)) = E 1 := by
      simp [E, PowerSeries.evalNegHom, PowerSeries.rescale_rescale]
    rw [hee, neg_mul] at he
    linear_combination -he
  have hH : PowerSeries.X * H = E (1 / 2) - E (-(1 / 2)) := by
    ext n
    cases n with
    | zero => simp [hEzero]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      rcases Nat.even_or_odd n with hn | hn
      · obtain ⟨k, hk⟩ := hn
        have heq : n = 2 * k := by omega
        clear hk
        subst n
        change PowerSeries.coeff (2 * k) (PowerSeries.expand 2 (by decide) h) = _
        rw [PowerSeries.coeff_expand_mul]
        simp [h, E, pow_succ, pow_mul]
        field_simp
        norm_num [← mul_pow]
      · obtain ⟨k, hk⟩ := hn
        have heq : n = 2 * k + 1 := hk
        have hndvd : ¬ 2 ∣ n := by omega
        rw [show PowerSeries.coeff n H = 0 from
          PowerSeries.coeff_expand_of_not_dvd 2 (by decide) h hndvd]
        subst n
        simp [E, pow_succ, pow_mul]
  -- Exponential multiplication proves the denominator identity without dividing by X.
  have hexp (a b : ℚ) : E a * E b = E (a + b) :=
    PowerSeries.exp_mul_exp_eq_exp_add a b
  have hplus : E (1 / 2) * E (1 / 2) = E 1 := by
    convert hexp (1 / 2) (1 / 2) using 1
    norm_num
  have hminus : E (-(1 / 2)) * E (-(1 / 2)) = E (-1) := by
    convert hexp (-(1 / 2)) (-(1 / 2)) using 1
    norm_num
  have hcross : E (1 / 2) * E (-(1 / 2)) = 1 := by
    rw [hexp]
    simp [E]
  have hfull : E (-1) * E 1 = 1 := by
    rw [hexp]
    simp [E]
  have hdenom : d * PowerSeries.evalNegHom d = H ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R := ℚ)))
    calc
      PowerSeries.X ^ 2 * (d * PowerSeries.evalNegHom d) =
          (PowerSeries.X * d) * (PowerSeries.X * PowerSeries.evalNegHom d) := by ring
      _ = (1 - E (-1)) * (E 1 - 1) := by rw [hd, hdneg]
      _ = (E (1 / 2) - E (-(1 / 2))) ^ 2 := by
        linear_combination -hfull -hplus -hminus + 2 * hcross
      _ = PowerSeries.X ^ 2 * H ^ 2 := by
        rw [← hH]
        ring
  -- All denominators have constant term one; their formal inverses are genuine units.
  have ht : d * toddCharacteristicSeries = 1 := by
    apply PowerSeries.mul_inv_cancel
    norm_num [d]
  have htneg : PowerSeries.evalNegHom d *
      PowerSeries.evalNegHom toddCharacteristicSeries = 1 := by
    simpa only [map_mul, map_one] using congrArg PowerSeries.evalNegHom ht
  have hh : h * aHatCharacteristicSeries = 1 := by
    apply PowerSeries.mul_inv_cancel
    norm_num [h]
  have hhE : H * PowerSeries.expand 2 (by decide) aHatCharacteristicSeries = 1 := by
    simpa only [map_mul, map_one] using congrArg (PowerSeries.expand 2 (by decide)) hh
  have hunit : (d * PowerSeries.evalNegHom d) *
      (toddCharacteristicSeries * PowerSeries.evalNegHom toddCharacteristicSeries) = 1 := by
    calc
      _ = (d * toddCharacteristicSeries) *
        (PowerSeries.evalNegHom d * PowerSeries.evalNegHom toddCharacteristicSeries) := by ring
      _ = 1 := by rw [ht, htneg, one_mul]
  have hnonzero : d * PowerSeries.evalNegHom d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hunit
    exact zero_ne_one hunit
  apply mul_left_cancel₀ hnonzero
  calc
    (d * PowerSeries.evalNegHom d) *
        (toddCharacteristicSeries * PowerSeries.evalNegHom toddCharacteristicSeries) = 1 := hunit
    _ = (H * PowerSeries.expand 2 (by decide) aHatCharacteristicSeries) ^ 2 := by
      rw [hhE]
      simp
    _ = (d * PowerSeries.evalNegHom d) *
      (PowerSeries.expand 2 (by decide) aHatCharacteristicSeries) ^ 2 := by
      rw [hdenom]
      ring

universe u

variable (X : Type u) [TopologicalSpace X]

/-- A finite list of original even classes multiplied by the actual cup product. -/
def singularCohomologyEvenListCup {ι : Type*} (w : ι → ℕ)
    (a : ∀ i : ι, singularCohomology ℚ X (2 * w i)) :
    (xs : List ι) → singularCohomology ℚ X (2 * (xs.map w).sum)
  | [] => singularCohomologyOne ℚ X
  | i :: xs => singularCohomologyEvenCup ℚ X (w i) (xs.map w).sum
      (a i) (singularCohomologyEvenListCup w a xs)

open Classical in
/-- The homogeneous degree-k evaluation of a finite weighted polynomial in actual even classes. -/
def singularCohomologyWeightedPolynomial {m : ℕ} (w : Fin m → ℕ)
    (a : ∀ i : Fin m, singularCohomology ℚ X (2 * w i))
    (p : MvPolynomial (Fin m) ℚ) (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  ∑ d ∈ p.support,
    let xs := (List.ofFn fun i : Fin m ↦ List.replicate (d i) i).flatten
    if hd : (xs.map w).sum = k then
      p.coeff d •
        (eqToIso (by rw [hd]) :
          singularCohomology ℚ X (2 * (xs.map w).sum) ≅
            singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenListCup X w a xs)
    else 0

/-- Finite weighted polynomial evaluation commutes with the original cohomology pullback. -/
theorem singularCohomologyWeightedPolynomial_pullback {Y : Type u} [TopologicalSpace Y]
    (f : C(Y, X)) {m : ℕ} (w : Fin m → ℕ)
    (a : ∀ i : Fin m, singularCohomology ℚ X (2 * w i))
    (p : MvPolynomial (Fin m) ℚ) (k : ℕ) :
    singularCohomologyPullback ℚ f (2 * k)
        (singularCohomologyWeightedPolynomial X w a p k) =
      singularCohomologyWeightedPolynomial Y w
        (fun i ↦ singularCohomologyPullback ℚ f (2 * w i) (a i)) p k := by
  /- Pullback preserves the original unit, each original cup product and
  rational scalar multiplication. Induct on each finite monomial list,
  then pass through its canonical degree equality and the finite sum.
  The degree test depends only on the exponent and weights, so it is
  unchanged by pullback. No convergence or homogeneity hypothesis is needed. -/
  -- Pullback commutes with the original degree transports; no grading is replaced.
  have ht {i j : ℕ} (h : i = j) (b : singularCohomology ℚ X i) :
      singularCohomologyPullback ℚ f j
          ((eqToIso (congrArg (singularCohomology ℚ X) h)).hom b) =
        (eqToIso (congrArg (singularCohomology ℚ Y) h)).hom
          (singularCohomologyPullback ℚ f i b) := by
    subst j
    rfl
  have heven (i j : ℕ) (b : singularCohomology ℚ X (2 * i))
      (c : singularCohomology ℚ X (2 * j)) :
      singularCohomologyPullback ℚ f (2 * (i + j))
          (singularCohomologyEvenCup ℚ X i j b c) =
        singularCohomologyEvenCup ℚ Y i j
          (singularCohomologyPullback ℚ f (2 * i) b)
          (singularCohomologyPullback ℚ f (2 * j) c) := by
    change singularCohomologyPullback ℚ f (2 * (i + j))
      ((eqToIso (congrArg (singularCohomology ℚ X) (Nat.mul_add 2 i j).symm)).hom
        (singularCohomologyCup ℚ X (2 * i) (2 * j) b c)) = _
    rw [ht (Nat.mul_add 2 i j).symm]
    exact congrArg (eqToIso
      (congrArg (singularCohomology ℚ Y) (Nat.mul_add 2 i j).symm)).hom
        (singularCohomologyPullback_cup ℚ f (2 * i) (2 * j) b c)
  -- Keep the same ordered monomial list and use the actual unit and cup naturality.
  have hlist (xs : List (Fin m)) :
      singularCohomologyPullback ℚ f (2 * (xs.map w).sum)
          (singularCohomologyEvenListCup X w a xs) =
        singularCohomologyEvenListCup Y w
          (fun i ↦ singularCohomologyPullback ℚ f (2 * w i) (a i)) xs := by
    induction xs with
    | nil => exact singularCohomologyPullback_one ℚ f
    | cons i xs ih =>
      change singularCohomologyPullback ℚ f (2 * (w i + (xs.map w).sum))
        (singularCohomologyEvenCup ℚ X (w i) (xs.map w).sum (a i)
          (singularCohomologyEvenListCup X w a xs)) = _
      rw [heven, ih]
      rfl
  -- Each degree test and coefficient is unchanged, so descend through the finite sum.
  classical
  unfold singularCohomologyWeightedPolynomial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with heq
  · rw [map_smul]
    congr 1
    rw [ht (congrArg (2 * ·) heq), hlist]
  · exact map_zero (singularCohomologyPullback ℚ f (2 * k)).hom

end AtiyahSinger
