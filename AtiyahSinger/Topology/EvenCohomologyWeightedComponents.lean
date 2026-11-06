/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyWeightedEvaluation

/-!
# Components of finite weighted polynomial evaluation

Public module ID: M1834.

The original ordered-list cup evaluator is the specified homogeneous component
of the same finite polynomial evaluated in the actual even cohomology ring.
This comparison applies to arbitrary polynomials, so substitutions of universal
root polynomials retain their original degree without an extra root hypothesis.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (X : Type u) [TopologicalSpace X]

/-- The original finite weighted evaluator is the specified component in the actual cup ring. -/
theorem singularCohomologyWeightedPolynomial_eq_component {m : ℕ} (w : Fin m → ℕ)
    (a : ∀ i : Fin m, singularCohomology ℚ X (2 * w i))
    (p : MvPolynomial (Fin m) ℚ) (k : ℕ) :
    singularCohomologyWeightedPolynomial X w a p k =
      singularEvenCohomologyComponent ℚ X k
        (MvPolynomial.aeval (fun i ↦ singularEvenCohomologyOf ℚ X (w i) (a i)) p) := by
  classical
  let b : Fin m → SingularEvenCohomology ℚ X :=
    fun i ↦ singularEvenCohomologyOf ℚ X (w i) (a i)
  -- The ordered cups have exactly the total degree of their finite factor list.
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
  -- Projection keeps exactly the monomials selected by the original degree test.
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  unfold singularCohomologyWeightedPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  let xs := (List.ofFn fun i : Fin m ↦ List.replicate (d i) i).flatten
  have hprod : (∏ i : Fin m, b i ^ d i) =
      singularEvenCohomologyOf ℚ X (xs.map w).sum
        (singularCohomologyEvenListCup X w a xs) := by
    rw [hlist]
    simp [xs, List.map_flatten, List.prod_flatten, List.map_ofFn,
      List.map_replicate, List.prod_replicate, List.prod_ofFn]
  change (if hd : (xs.map w).sum = k then _ else _) =
    singularEvenCohomologyComponent ℚ X k
      (algebraMap ℚ (SingularEvenCohomology ℚ X) (p.coeff d) * ∏ i, b i ^ d i)
  rw [hprod, ← Algebra.smul_def, map_smul]
  by_cases hd : (xs.map w).sum = k
  · subst k
    simp only [dite_eq_left, eqToIso_refl, Iso.refl_hom, ModuleCat.id_apply,
      singularEvenCohomologyComponent_of]
    rfl
  · simp [hd, singularEvenCohomologyComponent,
      singularEvenCohomologyOf, DirectSum.component.of]

end AtiyahSinger
