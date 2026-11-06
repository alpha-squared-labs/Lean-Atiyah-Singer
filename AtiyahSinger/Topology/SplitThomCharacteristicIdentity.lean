/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteSumBundle
public import AtiyahSinger.Topology.LambdaLineClass
public import AtiyahSinger.Topology.LambdaOperations
public import AtiyahSinger.Topology.LineCharacteristicClasses
public import AtiyahSinger.Topology.LineFirstChernComparison
public import AtiyahSinger.Topology.TrivialInverseTodd

/-!
# The exterior character identity on an actual finite sum of lines

Public module ID: M2181.

For the actual finite sum of a specified line family, the alternating exterior
character is the product of the line factors 1-exp(c). Factoring the root from
each factor identifies its degree-r+j coefficient with the root product times
the signed degree-j inverse Todd class. This is a formal power-series identity
evaluated in the original even cohomology ring; it divides by no cohomology class.

The line roots use the supplied norms and original Unit total topologies.
Actual sum isomorphisms and metric independence retain arbitrary metrics on the
finite sum. Source: SG III.11--III.12, the split form of the Thom-character factor.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v

attribute [local instance] finiteSumTopology isFiniteRank_finiteSum sumTopology isFiniteRank_sum
  trivialTopology isFiniteRank_trivial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual split exterior character equals its Euler-root product times signed inverse Todd. -/
theorem chernCharacterKZeroComponent_lambdaMinusOne_of_lineSplitting (r : ℕ)
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (L : Fin r → X → Type u)
    [∀ i x, NormedAddCommGroup (L i x)] [∀ i x, NormedSpace ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)]
    (hL : ∀ i, ContinuousHermitianMetric (L i))
    (hline : ∀ i x, Module.finrank ℂ (L i x) = 1)
    {E : X → Type v} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (e : Iso E (FiniteSum r L)) (j : ℕ) :
    singularEvenCohomologyOf ℚ X (r + j)
        (chernCharacterKZeroComponent X (r + j) (lambdaMinusOne E)) =
      (∏ i : Fin r, singularEvenCohomologyOf ℚ X 1
        (singularCohomologyRationalization X 2 (firstChernClass (L i) (hline i)))) *
          singularEvenCohomologyOf ℚ X j
            ((-1 : ℚ) ^ (r + j) • inverseToddClassComponent E h j) := by
  classical
  let hsum := ContinuousHermitianMetric.finiteSum hL
  rw [lambdaMinusOne_eq_of_iso E (FiniteSum r L) e,
    inverseToddClassComponent_eq_of_iso E h (FiniteSum r L) hsum e]
  let R := SingularEvenCohomology ℚ X
  let C (a : ComplexKZero X) : PowerSeries R := PowerSeries.mk fun n ↦
    singularEvenCohomologyOf ℚ X n (chernCharacterKZeroComponent X n a)
  let I (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      (hE : ContinuousHermitianMetric E) : PowerSeries R := PowerSeries.mk fun n ↦
    singularEvenCohomologyOf ℚ X n (inverseToddClassComponent E hE n)
  -- The original finite cup convolutions are exactly power-series multiplication.
  have hCmul (a b : ComplexKZero X) : C (a * b) = C a * C b := by
    apply PowerSeries.ext
    intro n
    simp only [C, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    rw [chernCharacterKZeroComponent_mul, map_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso ℚ X
      (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup]
  have hCone : C 1 = 1 := by
    apply PowerSeries.ext
    intro n
    simp only [C, PowerSeries.coeff_mk, chernCharacterKZeroComponent_one,
      singularEvenCohomologyOf_degreeTwoPow, map_zero]
    cases n <;> simp
  have hIsum (E F : X → Type u)
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F) :
      I (E ×ᵇ F) (hE.sum hF) = I E hE * I F hF := by
    apply PowerSeries.ext
    intro n
    simp only [I, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    rw [inverseToddClassComponent_sum, map_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso ℚ X
      (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup]
  have hIiso (E F : X → Type u)
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F) (e : Iso E F) :
      I E hE = I F hF := by
    apply PowerSeries.ext
    intro n
    simpa only [I, PowerSeries.coeff_mk] using
      congrArg (singularEvenCohomologyOf ℚ X n)
        (inverseToddClassComponent_eq_of_iso E hE F hF e n)
  have hfactor (E : X → Type u)
      [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      (hE : ContinuousHermitianMetric E) (hr : ∀ x, Module.finrank ℂ (E x) = 1) :
      C (lambdaMinusOne E) =
        PowerSeries.C (-singularEvenCohomologyOf ℚ X 1
          (singularCohomologyRationalization X 2 (firstChernClass E hr))) *
            (PowerSeries.X ^ 1 * PowerSeries.rescale (-1) (I E hE)) := by
    -- The scalar formulas use the same original first class after comparing auxiliary norms.
    have hfirst : globalChernClass E hE 1 = firstChernClass E hr := by
      have hg := globalChernClass_one_eq_firstChernClass_of_finrank_eq_one E hE hr
      have hn := @firstChernClass_eq_of_iso X _ E hE.fiberNormedAddCommGroup
        (fun x ↦ (hE.fiberInnerProductSpace x).toNormedSpace) _ _ hr E
        (inferInstance : ∀ x, NormedAddCommGroup (E x))
        (inferInstance : ∀ x, NormedSpace ℂ (E x)) _ _ hr (Iso.refl E)
      exact hg.trans hn
    let c := singularCohomologyRationalization X 2 (firstChernClass E hr)
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_C_mul]
    simp only [C, PowerSeries.coeff_mk]
    change singularEvenCohomologyOf ℚ X n
      (chernCharacterKZeroComponent X n (lambdaMinusOne E)) = _
    rw [lambdaMinusOne_eq_one_sub_of_finrank_eq_one E hr, map_sub]
    change singularEvenCohomologyOf ℚ X n
      (chernCharacterKZeroComponent X n (1 : ComplexKZero X) -
        chernCharacterKZeroComponent X n (kZeroClass E)) = _
    rw [chernCharacterKZeroComponent_one, chernCharacterKZeroComponent_bundle E hE,
      globalChernCharacterComponent_eq_pow_of_finrank_eq_one E hE hr, hfirst]
    cases n with
    | zero =>
      simp only [map_sub, singularEvenCohomologyOf_degreeTwoPow,
        pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, sub_self,
        pow_one, PowerSeries.coeff_zero_X_mul, mul_zero]
    | succ n =>
      rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_rescale]
      simp only [I, PowerSeries.coeff_mk]
      change _ = _ * ((-1 : R) ^ n * singularEvenCohomologyOf ℚ X n
        (inverseToddClassComponent E hE n))
      rw [inverseToddClassComponent_eq_pow_of_finrank_eq_one E hE hr, hfirst]
      simp only [map_sub, map_smul, singularEvenCohomologyOf_degreeTwoPow,
        map_zero, zero_pow (Nat.succ_ne_zero n), zero_sub]
      let x : R := singularEvenCohomologyOf ℚ X 1 c
      change -((Nat.factorial (n + 1) : ℚ)⁻¹ • x ^ (n + 1)) =
        -x * ((-1 : R) ^ n * (((-1 : ℚ) ^ n / (Nat.factorial (n + 1) : ℚ)) • x ^ n))
      have hneg (y : R) : (-1 : R) ^ n * y = (-1 : ℚ) ^ n • y := by
        simp only [Algebra.smul_def, map_pow, map_neg, map_one]
      have hsign : (-1 : ℚ) ^ n *
          ((-1 : ℚ) ^ n / (Nat.factorial (n + 1) : ℚ)) =
            (Nat.factorial (n + 1) : ℚ)⁻¹ := by
        rw [div_eq_mul_inv, ← mul_assoc, ← mul_pow]
        simp
      rw [hneg, smul_smul, hsign, mul_smul_comm, neg_mul, ← pow_succ', smul_neg]
  -- Multiply the line identities using the actual finite-sum head--tail isomorphisms.
  have hseries (n : ℕ) (M : Fin n → X → Type u)
      [∀ i x, NormedAddCommGroup (M i x)] [∀ i x, NormedSpace ℂ (M i x)]
      [∀ i, TopologicalSpace (TotalSpace Unit (M i))] [∀ i, IsFiniteRank (M i)]
      (hM : ∀ i, ContinuousHermitianMetric (M i))
      (hm : ∀ i x, Module.finrank ℂ (M i x) = 1) :
      C (lambdaMinusOne (FiniteSum n M)) =
        PowerSeries.C (∏ i : Fin n, -singularEvenCohomologyOf ℚ X 1
          (singularCohomologyRationalization X 2 (firstChernClass (M i) (hm i)))) *
            (PowerSeries.X ^ n * PowerSeries.rescale (-1)
              (I (FiniteSum n M) (ContinuousHermitianMetric.finiteSum hM))) := by
    induction n with
    | zero =>
      have hzero : I (FiniteSum 0 M) (ContinuousHermitianMetric.finiteSum hM) = 1 := by
        let Z := Bundle.Trivial X (Fin 0 → ℂ)
        let hZ := (nonempty_continuousHermitianMetric Z).some
        apply PowerSeries.ext
        intro d
        simp only [I, PowerSeries.coeff_mk]
        rw [inverseToddClassComponent_eq_of_iso (FiniteSum 0 M)
          (ContinuousHermitianMetric.finiteSum hM) Z hZ (finiteSumZeroIso M),
          inverseToddClassComponent_trivial, singularEvenCohomologyOf_degreeTwoPow, map_zero]
        cases d <;> simp
      rw [lambdaMinusOne_eq_one_of_subsingleton, hCone, hzero]
      simp
    | succ n ih =>
      let F := FiniteSum n (fun i ↦ M i.succ)
      let hF := ContinuousHermitianMetric.finiteSum (fun i ↦ hM i.succ)
      let eSum := finiteSumSuccIso n M
      rw [lambdaMinusOne_eq_of_iso (FiniteSum (n + 1) M) (M 0 ×ᵇ F) eSum,
        lambdaMinusOne_sum]
      change C (lambdaMinusOne (M 0) * lambdaMinusOne F) = _
      rw [hCmul, hfactor (M 0) (hM 0) (hm 0), ih (fun i ↦ M i.succ)
        (fun i ↦ hM i.succ) (fun i ↦ hm i.succ)]
      rw [hIiso (FiniteSum (n + 1) M) (M 0 ×ᵇ F)
        (ContinuousHermitianMetric.finiteSum hM) ((hM 0).sum hF) eSum, hIsum]
      rw [Fin.prod_univ_succ, map_mul, map_mul, pow_succ]
      ring
  let roots (i : Fin r) : singularCohomology ℚ X 2 :=
    singularCohomologyRationalization X 2 (firstChernClass (L i) (hline i))
  let x (i : Fin r) : R := singularEvenCohomologyOf ℚ X 1 (roots i)
  have hs := hseries r L hL hline
  change C (lambdaMinusOne (FiniteSum r L)) =
    PowerSeries.C (∏ i, -x i) *
      (PowerSeries.X ^ r * PowerSeries.rescale (-1) (I (FiniteSum r L) hsum)) at hs
  have hcoeff := congrArg (PowerSeries.coeff (r + j)) hs
  simp only [C, PowerSeries.coeff_mk] at hcoeff
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
    Nat.add_sub_cancel_left,
    PowerSeries.coeff_rescale] at hcoeff
  simp only [I, PowerSeries.coeff_mk] at hcoeff
  change singularEvenCohomologyOf ℚ X (r + j)
    (chernCharacterKZeroComponent X (r + j) (lambdaMinusOne (FiniteSum r L))) =
      (∏ i, x i) * singularEvenCohomologyOf ℚ X j
        ((-1 : ℚ) ^ (r + j) • inverseToddClassComponent (FiniteSum r L) hsum j)
  rw [hcoeff, Finset.prod_neg, Finset.card_univ, Fintype.card_fin, map_smul]
  simp only [Algebra.smul_def, map_pow, map_neg, map_one]
  rw [pow_add]
  ring

end AtiyahSinger.ComplexBundle
