/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CharacteristicSeries
public import AtiyahSinger.Topology.EvenCohomologyNaturality
public import Mathlib.Algebra.Module.Rat

/-!
# Weighted polynomial evaluation in the actual even cup ring

Public module ID: M1835.

The finite ordered-list evaluator of characteristic classes agrees with
polynomial evaluation in the direct sum of the original even cohomology
groups. Homogeneity fixes the component; no infinite cohomology sum occurs.
This comparison transfers universal multiplicative-sequence identities to
the original cup products and their canonical degree transports.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (X : Type u) [TopologicalSpace X]

/-- The rational scalar action on the actual even cup ring defines its rational algebra. -/
instance singularEvenCohomologyRationalAlgebra : Algebra ℚ (SingularEvenCohomology ℚ X) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- The universal multiplicative-sequence polynomial has unit constant component. -/
theorem MultiplicativeSequence.polynomial_zero (f : PowerSeries ℚ) :
    MultiplicativeSequence.polynomial f 0 = 1 := by
  unfold MultiplicativeSequence.polynomial
  have hroot : (⟨PowerSeries.coeff 0 (MultiplicativeSequence.rootProduct f 0),
      MultiplicativeSequence.isSymmetric_coeff_rootProduct f 0 0⟩ :
      MvPolynomial.symmetricSubalgebra (Fin 0) ℚ) = 1 := by
    apply Subtype.ext
    simp [MultiplicativeSequence.rootProduct]
  rw [hroot, map_one]

/-- A homogeneous weighted polynomial gives the same class in the actual even cup ring. -/
theorem singularEvenCohomologyOf_weightedPolynomial {m : ℕ} (w : Fin m → ℕ)
    (a : ∀ i : Fin m, singularCohomology ℚ X (2 * w i))
    (p : MvPolynomial (Fin m) ℚ) (k : ℕ) (hp : p.IsWeightedHomogeneous w k) :
    singularEvenCohomologyOf ℚ X k (singularCohomologyWeightedPolynomial X w a p k) =
      MvPolynomial.aeval (fun i ↦ singularEvenCohomologyOf ℚ X (w i) (a i)) p := by
  classical
  let b : Fin m → SingularEvenCohomology ℚ X :=
    fun i ↦ singularEvenCohomologyOf ℚ X (w i) (a i)
  -- Inclusion converts each finite ordered list of original cups into its product.
  have hlist (xs : List (Fin m)) :
      singularEvenCohomologyOf ℚ X (xs.map w).sum
          (singularCohomologyEvenListCup X w a xs) = (xs.map b).prod := by
    induction xs with
    | nil => exact singularEvenCohomologyOf_one ℚ X
    | cons i xs ih =>
      change singularEvenCohomologyOf ℚ X (w i + (xs.map w).sum)
        (singularCohomologyEvenCup ℚ X (w i) (xs.map w).sum (a i)
          (singularCohomologyEvenListCup X w a xs)) = b i * (xs.map b).prod
      rw [singularEvenCohomologyOf_cup, ih]
  -- The polynomial support has exactly the specified weight, so no term is discarded.
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  unfold singularCohomologyWeightedPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  let xs := (List.ofFn fun i : Fin m ↦ List.replicate (d i) i).flatten
  have hdegree : (xs.map w).sum = k := by
    have hdw := hp (MvPolynomial.mem_support_iff.mp hd)
    have hsum : (xs.map w).sum = Finsupp.weight w d := by
      simp [xs, List.map_flatten, List.sum_flatten, List.map_ofFn,
        List.map_replicate, List.sum_replicate, List.sum_ofFn,
        Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    exact hsum.trans hdw
  rw [dite_eq_left hdegree, map_smul, singularEvenCohomologyOf_eqToIso ℚ X hdegree, hlist]
  rw [Algebra.smul_def]
  congr 1
  simp [xs, List.map_flatten, List.prod_flatten, List.map_ofFn,
    List.map_replicate, List.prod_replicate, List.prod_ofFn, b]

/-- The constant polynomial one evaluates to the original degree-zero unit. -/
theorem singularCohomologyWeightedPolynomial_one_zero {m : ℕ} (w : Fin m → ℕ)
    (a : ∀ i : Fin m, singularCohomology ℚ X (2 * w i)) :
    singularCohomologyWeightedPolynomial X w a 1 0 = singularCohomologyOne ℚ X := by
  apply singularEvenCohomologyOf_injective ℚ X 0
  rw [singularEvenCohomologyOf_weightedPolynomial X w a 1 0
    (MvPolynomial.isWeightedHomogeneous_one ℚ w), map_one, singularEvenCohomologyOf_one]

end AtiyahSinger
