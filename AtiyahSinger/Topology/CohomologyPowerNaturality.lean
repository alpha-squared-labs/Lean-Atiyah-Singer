/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyNaturality
public import AtiyahSinger.Topology.SingularCohomologyPowerCombination

/-!
# Naturality of actual cup powers and homogeneous combinations

Public module ID: M1625.

The original degree-two powers commute with continuous pullback. Homogeneous
combinations commute with a specified commutative square, retaining the same
class, coefficients, order of cup factors and canonical degree transports.
These are used to compare projective Chern coefficients after base change.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R]

/-- Pullback preserves the actual recursive degree-two cup powers. -/
theorem singularCohomologyPullback_degreeTwoPow {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (t : singularCohomology R Y 2) (n : ℕ) :
    singularCohomologyPullback R f (2 * n) (singularCohomologyDegreeTwoPow R Y t n) =
      singularCohomologyDegreeTwoPow R X (singularCohomologyPullback R f 2 t) n := by
  apply singularEvenCohomologyOf_injective R X n
  rw [← singularEvenCohomologyPullback_of, singularEvenCohomologyOf_degreeTwoPow,
    singularEvenCohomologyOf_degreeTwoPow, map_pow, singularEvenCohomologyPullback_of]

/-- The specified square preserves homogeneous combinations of the same pulled-back class. -/
theorem singularCohomologyPowerCombination_pullback
    {X₁ X₂ Y₁ Y₂ : Type u} [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (π₁ : C(Y₁, X₁)) (π₂ : C(Y₂, X₂)) (f : C(X₂, X₁)) (g : C(Y₂, Y₁))
    (hsquare : π₁.comp g = f.comp π₂) (t : singularCohomology R Y₁ 2)
    (r n : ℕ) (hn : ∀ i : Fin r, i.val ≤ n)
    (a : ∀ i : Fin r, singularCohomology R X₁ (2 * (n - i.val))) :
    singularCohomologyPullback R g (2 * n)
        (singularCohomologyPowerCombination R π₁ t r n hn a) =
      singularCohomologyPowerCombination R π₂ (singularCohomologyPullback R g 2 t) r n hn
        (fun i ↦ singularCohomologyPullback R f (2 * (n - i.val)) (a i)) := by
  classical
  -- The ordinary homogeneous expression is its finite polynomial expression in the cup ring.
  have hrepr {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
      (p : C(B, A)) (z : singularCohomology R B 2)
      (b : ∀ i : Fin r, singularCohomology R A (2 * (n - i.val))) :
      singularEvenCohomologyOf R B n (singularCohomologyPowerCombination R p z r n hn b) =
        ∑ i : Fin r, singularEvenCohomologyPullback R p
            (singularEvenCohomologyOf R A (n - i.val) (b i)) *
          singularEvenCohomologyOf R B 1 z ^ i.val := by
    rw [singularCohomologyPowerCombination_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso R B (Nat.sub_add_cancel (hn i)),
      singularEvenCohomologyOf_cup, singularEvenCohomologyOf_degreeTwoPow,
      singularEvenCohomologyPullback_of]
  -- Contravariance uses the original specified square, in its actual composition order.
  have hmaps (k : ℕ) :
      singularCohomologyPullback R π₁ k ≫ singularCohomologyPullback R g k =
        singularCohomologyPullback R f k ≫ singularCohomologyPullback R π₂ k := by
    let H := singularCohomologyFunctor R k
    change H.map (TopCat.ofHom π₁).op ≫ H.map (TopCat.ofHom g).op =
      H.map (TopCat.ofHom f).op ≫ H.map (TopCat.ofHom π₂).op
    rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp]
    change H.map (TopCat.ofHom (π₁.comp g)).op = H.map (TopCat.ofHom (f.comp π₂)).op
    rw [hsquare]
  apply singularEvenCohomologyOf_injective R Y₂ n
  rw [← singularEvenCohomologyPullback_of, hrepr, hrepr, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow]
  simp only [singularEvenCohomologyPullback_of]
  congr 1
  have hi := congrArg (fun F : singularCohomology R X₁ (2 * (n - i.val)) ⟶
      singularCohomology R Y₂ (2 * (n - i.val)) ↦ F (a i)) (hmaps (2 * (n - i.val)))
  exact congrArg (singularEvenCohomologyOf R Y₂ (n - i.val)) hi

end AtiyahSinger
