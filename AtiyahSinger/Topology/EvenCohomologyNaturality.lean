/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomialEvaluation

/-!
# Naturality of the original even cohomology ring

Public module ID: M1829.

The degreewise original pullbacks form a ring homomorphism on finite sums.
Projection to each homogeneous component commutes with this same map. These
interfaces let finite polynomial constructions descend in their original degree.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

attribute [local irreducible] singularCohomologyCup

/-- The original pullback preserves even cup products, including the canonical degree transport. -/
theorem singularCohomologyPullback_evenCup (f : C(X, Y)) (p q : ℕ)
    (a : singularCohomology R Y (2 * p)) (b : singularCohomology R Y (2 * q)) :
    singularCohomologyPullback R f (2 * (p + q)) (singularCohomologyEvenCup R Y p q a b) =
      singularCohomologyEvenCup R X p q
        (singularCohomologyPullback R f (2 * p) a)
        (singularCohomologyPullback R f (2 * q) b) := by
  have htransport (n m : ℕ) (h : n = m) (c : singularCohomology R Y n) :
      singularCohomologyPullback R f m
          ((eqToIso (congrArg (singularCohomology R Y) h)).hom c) =
        (eqToIso (congrArg (singularCohomology R X) h)).hom
          (singularCohomologyPullback R f n c) := by
    subst m
    rfl
  -- Naturality of cup is unchanged by the canonical reindexing to even degrees.
  change singularCohomologyPullback R f (2 * (p + q))
      ((eqToIso (congrArg (singularCohomology R Y) (Nat.mul_add 2 p q).symm)).hom
        (singularCohomologyCup R Y (2 * p) (2 * q) a b)) =
    (eqToIso (congrArg (singularCohomology R X) (Nat.mul_add 2 p q).symm)).hom
      (singularCohomologyCup R X (2 * p) (2 * q)
        (singularCohomologyPullback R f (2 * p) a)
        (singularCohomologyPullback R f (2 * q) b))
  rw [htransport _ _ (Nat.mul_add 2 p q).symm, singularCohomologyPullback_cup]

/-- Pullback on the original homogeneous groups, extended to their finite-sum cup ring. -/
def singularEvenCohomologyPullback (f : C(X, Y)) :
    SingularEvenCohomology R Y →+* SingularEvenCohomology R X :=
  DirectSum.toSemiring (fun k ↦
    (singularEvenCohomologyOf R X k).toAddMonoidHom.comp
      (singularCohomologyPullback R f (2 * k)).hom.toAddMonoidHom)
    (by
      change singularEvenCohomologyOf R X 0
        (singularCohomologyPullback R f 0 (singularCohomologyOne R Y)) = 1
      rw [singularCohomologyPullback_one, singularEvenCohomologyOf_one])
    (by
      intro p q a b
      change singularEvenCohomologyOf R X (p + q)
          (singularCohomologyPullback R f (2 * (p + q))
            (singularCohomologyEvenCup R Y p q a b)) =
        singularEvenCohomologyOf R X p (singularCohomologyPullback R f (2 * p) a) *
          singularEvenCohomologyOf R X q (singularCohomologyPullback R f (2 * q) b)
      rw [singularCohomologyPullback_evenCup, singularEvenCohomologyOf_cup])

/-- The ring pullback acts by the specified original pullback on each homogeneous class. -/
@[simp] theorem singularEvenCohomologyPullback_of (f : C(X, Y)) (k : ℕ)
    (a : singularCohomology R Y (2 * k)) :
    singularEvenCohomologyPullback R f (singularEvenCohomologyOf R Y k a) =
      singularEvenCohomologyOf R X k (singularCohomologyPullback R f (2 * k) a) :=
  DirectSum.toSemiring_of
    (A := fun j : ℕ ↦ singularCohomology R Y (2 * j)) _ _ _ k a

/-- Projection from the finite-sum ring to the original degree-2k cohomology group. -/
def singularEvenCohomologyComponent (X : Type u) [TopologicalSpace X] (k : ℕ) :
    SingularEvenCohomology R X →ₗ[R] singularCohomology R X (2 * k) :=
  DirectSum.component R ℕ (fun j : ℕ ↦ singularCohomology R X (2 * j)) k

/-- A homogeneous class is recovered exactly by projection to its own degree. -/
@[simp] theorem singularEvenCohomologyComponent_of (k : ℕ)
    (a : singularCohomology R X (2 * k)) :
    singularEvenCohomologyComponent R X k (singularEvenCohomologyOf R X k a) = a :=
  DirectSum.component.lof_self (M := fun j : ℕ ↦ singularCohomology R X (2 * j)) R k a

/-- Projection to a homogeneous component commutes with the original ring pullback. -/
theorem singularEvenCohomologyComponent_pullback (f : C(X, Y)) (k : ℕ)
    (a : SingularEvenCohomology R Y) :
    singularEvenCohomologyComponent R X k (singularEvenCohomologyPullback R f a) =
      singularCohomologyPullback R f (2 * k) (singularEvenCohomologyComponent R Y k a) := by
  classical
  -- The two additive maps agree on every original homogeneous summand.
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | of i a =>
    change singularEvenCohomologyComponent R X k
        (singularEvenCohomologyPullback R f (singularEvenCohomologyOf R Y i a)) =
      singularCohomologyPullback R f (2 * k)
        (singularEvenCohomologyComponent R Y k (singularEvenCohomologyOf R Y i a))
    rw [singularEvenCohomologyPullback_of]
    by_cases hi : i = k
    · subst i
      rw [singularEvenCohomologyComponent_of, singularEvenCohomologyComponent_of]
    · simp only [singularEvenCohomologyComponent, singularEvenCohomologyOf,
        DirectSum.component.of, hi, ↓reduceDIte, map_zero]

end AtiyahSinger
