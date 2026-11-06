/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomials
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.DirectSum.Ring

/-!
# The even singular cohomology ring

Public module ID: M1833.

The direct sum of the original even singular cohomology groups carries the
original cup product. Canonical changes of degree are the only transports.
Graded commutativity has positive sign in these degrees, so this is a
commutative ring. Its homogeneous inclusions allow ordinary polynomial
identities to be applied to Chern roots without changing their cohomology.
This direct sum is used for finite polynomial identities, not for an infinite
Chern-character sum on a space of unbounded cohomological dimension.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory
open scoped DirectSum

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

attribute [local irreducible] singularCohomologyCup

/-- Homogeneous multiplication is the original even cup product. -/
instance singularCohomologyEvenGMul :
    GradedMonoid.GMul (fun k : ℕ ↦ singularCohomology R X (2 * k)) where
  mul {p q} a b := singularCohomologyEvenCup R X p q a b

/-- The homogeneous unit is the original degree-zero cohomology class. -/
instance singularCohomologyEvenGOne :
    GradedMonoid.GOne (fun k : ℕ ↦ singularCohomology R X (2 * k)) where
  one := singularCohomologyOne R X

/-- The original bilinear cup product distributes over the cohomology addition. -/
instance singularCohomologyEvenGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (fun k : ℕ ↦ singularCohomology R X (2 * k)) where
  toGMul := singularCohomologyEvenGMul R X
  mul_zero {i j} a := (singularCohomologyEvenCup R X i j a).map_zero
  zero_mul {i j} b := by
    change singularCohomologyEvenCup R X i j 0 b = 0
    exact congrArg (fun f : singularCohomology R X (2 * j) →ₗ[R]
      singularCohomology R X (2 * (i + j)) ↦ f b)
        (map_zero (singularCohomologyEvenCup R X i j))
  mul_add {i j} a b c := (singularCohomologyEvenCup R X i j a).map_add b c
  add_mul {i j} a b c :=
    congrArg (fun f : singularCohomology R X (2 * j) →ₗ[R]
      singularCohomology R X (2 * (i + j)) ↦ f c)
        ((singularCohomologyEvenCup R X i j).map_add a b)

/-- The even homogeneous classes form a graded commutative monoid under cup. -/
instance singularCohomologyEvenGCommMonoid :
    GradedMonoid.GCommMonoid (fun k : ℕ ↦ singularCohomology R X (2 * k)) := by
  have eqToIso_apply_heq {A B : ModuleCat.{u} R} (h : A = B) (a : A) :
      HEq ((eqToIso h).hom a) a := by
    subst B
    rfl
  have heq_of_eqToIso_eq {A B : ModuleCat.{u} R} {h : A = B}
      {a : A} {b : B} (hab : (eqToIso h).hom a = b) : HEq a b :=
    (eqToIso_apply_heq h a).symm.trans (heq_of_eq hab)
  have cup_heq {p p' q q' : ℕ} (hp : p = p') (hq : q = q')
      {a : singularCohomology R X p} {a' : singularCohomology R X p'}
      {b : singularCohomology R X q} {b' : singularCohomology R X q'}
      (ha : HEq a a') (hb : HEq b b') :
      HEq (singularCohomologyCup R X p q a b)
        (singularCohomologyCup R X p' q' a' b') := by
    subst p'
    subst q'
    cases eq_of_heq ha
    cases eq_of_heq hb
    rfl
  have evenCup_heq (p q : ℕ)
      (a : singularCohomology R X (2 * p)) (b : singularCohomology R X (2 * q)) :
      HEq (singularCohomologyEvenCup R X p q a b)
        (singularCohomologyCup R X (2 * p) (2 * q) a b) :=
    eqToIso_apply_heq _ _
  let ofLaws (A : ℕ → Type u)
      [GradedMonoid.GMul A] [GradedMonoid.GOne A]
      (hone : ∀ a : GradedMonoid A, 1 * a = a)
      (hmulOne : ∀ a : GradedMonoid A, a * 1 = a)
      (hassoc : ∀ a b c : GradedMonoid A, a * b * c = a * (b * c))
      (hcomm : ∀ a b : GradedMonoid A, a * b = b * a) : GradedMonoid.GCommMonoid A :=
    { one_mul := hone
      mul_one := hmulOne
      mul_assoc := hassoc
      mul_comm := hcomm }
  have hone :
      ∀ a : GradedMonoid (fun k : ℕ ↦ singularCohomology R X (2 * k)), 1 * a = a := by
    rintro ⟨p, a⟩
    apply Sigma.ext (Nat.zero_add p)
    dsimp only [HMul.hMul, Mul.mul, One.one, OfNat.ofNat, GradedMonoid.GMul.mul,
      GradedMonoid.GOne.one, GradedMonoid.GMul.toMul,
      GradedMonoid.GOne.toOne, singularCohomologyEvenGMul, singularCohomologyEvenGOne,
      GradedMonoid.mk]
    -- Forget the canonical regrading, then use the original left-unit law.
    have hcup := evenCup_heq 0 p (singularCohomologyOne R X) a
    have hunit : HEq
        (singularCohomologyCup R X 0 (2 * p) (singularCohomologyOne R X) a) a :=
      heq_of_eqToIso_eq (singularCohomologyOne_cup R X (2 * p) a)
    exact hcup.trans hunit
  have hmulOne :
      ∀ a : GradedMonoid (fun k : ℕ ↦ singularCohomology R X (2 * k)), a * 1 = a := by
    rintro ⟨p, a⟩
    apply Sigma.ext (Nat.add_zero p)
    dsimp only [HMul.hMul, Mul.mul, One.one, OfNat.ofNat, GradedMonoid.GMul.mul,
      GradedMonoid.GOne.one, GradedMonoid.GMul.toMul,
      GradedMonoid.GOne.toOne, singularCohomologyEvenGMul, singularCohomologyEvenGOne,
      GradedMonoid.mk]
    exact (evenCup_heq p 0 a _).trans
      (heq_of_eq (singularCohomologyCup_one R X (2 * p) a))
  have hassoc :
      ∀ a b c : GradedMonoid (fun k : ℕ ↦ singularCohomology R X (2 * k)),
        a * b * c = a * (b * c) := by
    rintro ⟨p, a⟩ ⟨q, b⟩ ⟨r, c⟩
    apply Sigma.ext (Nat.add_assoc p q r)
    dsimp only [HMul.hMul, Mul.mul, One.one, OfNat.ofNat, GradedMonoid.GMul.mul,
      GradedMonoid.GOne.one, GradedMonoid.GMul.toMul,
      GradedMonoid.GOne.toOne, singularCohomologyEvenGMul, singularCohomologyEvenGOne,
      GradedMonoid.mk]
    -- Reassociate the same three ordinary cup factors, including their degrees.
    have hleft := (evenCup_heq (p + q) r _ c).trans
      (cup_heq (Nat.mul_add 2 p q) rfl (evenCup_heq p q a b) (HEq.rfl))
    have hright := (evenCup_heq p (q + r) a _).trans
      (cup_heq rfl (Nat.mul_add 2 q r) (HEq.rfl) (evenCup_heq q r b c))
    have hassoc := heq_of_eqToIso_eq
      (singularCohomologyCup_assoc R X (2 * p) (2 * q) (2 * r) a b c)
    exact hleft.trans (hassoc.trans hright.symm)
  have hcomm :
      ∀ a b : GradedMonoid (fun k : ℕ ↦ singularCohomology R X (2 * k)), a * b = b * a := by
    rintro ⟨p, a⟩ ⟨q, b⟩
    apply Sigma.ext (Nat.add_comm p q)
    dsimp only [HMul.hMul, Mul.mul, One.one, OfNat.ofNat, GradedMonoid.GMul.mul,
      GradedMonoid.GOne.one, GradedMonoid.GMul.toMul,
      GradedMonoid.GOne.toOne, singularCohomologyEvenGMul, singularCohomologyEvenGOne,
      GradedMonoid.mk]
    -- The Koszul sign is one because the two cohomological degrees are even.
    have hsign : (-1 : R) ^ ((2 * p) * (2 * q)) = 1 := by
      rw [Nat.mul_assoc, pow_mul]
      simp
    have hcomm := singularCohomologyCup_comm R X (2 * p) (2 * q) a b
    rw [hsign, one_smul] at hcomm
    exact (evenCup_heq p q a b).trans
      ((heq_of_eqToIso_eq hcomm).trans
        (evenCup_heq q p b a).symm)
  exact ofLaws (fun k : ℕ ↦ singularCohomology R X (2 * k)) hone hmulOne hassoc hcomm

/-- Even cup products give the graded commutative ring structure on the original groups. -/
instance singularCohomologyEvenGCommRing :
    DirectSum.GCommRing (fun k : ℕ ↦ singularCohomology R X (2 * k)) := by
  -- Assemble the standard casts with an abstract family before specializing the cup algebra.
  let ofLaws (A : ℕ → Type u) [∀ i, AddCommGroup (A i)] [GradedMonoid.GCommMonoid A]
      (hmulZero : ∀ {i j} (a : A i), GradedMonoid.GMul.mul a (0 : A j) = 0)
      (hzeroMul : ∀ {i j} (b : A j), GradedMonoid.GMul.mul (0 : A i) b = 0)
      (hmulAdd : ∀ {i j} (a : A i) (b c : A j),
        GradedMonoid.GMul.mul a (b + c) = GradedMonoid.GMul.mul a b + GradedMonoid.GMul.mul a c)
      (haddMul : ∀ {i j} (a b : A i) (c : A j),
        GradedMonoid.GMul.mul (a + b) c = GradedMonoid.GMul.mul a c + GradedMonoid.GMul.mul b c) :
      DirectSum.GCommRing A :=
    { toGCommMonoid := inferInstance
      mul_zero := hmulZero
      zero_mul := hzeroMul
      mul_add := hmulAdd
      add_mul := haddMul
      natCast n := n • GradedMonoid.GOne.one
      natCast_zero := zero_nsmul _
      natCast_succ n := succ_nsmul _ n
      intCast n := n • GradedMonoid.GOne.one
      intCast_ofNat n := natCast_zsmul _ n
      intCast_negSucc_ofNat n := negSucc_zsmul _ n }
  exact ofLaws (fun k : ℕ ↦ singularCohomology R X (2 * k))
    (fun {i j} ↦ DirectSum.GNonUnitalNonAssocSemiring.mul_zero
      (A := fun k : ℕ ↦ singularCohomology R X (2 * k)) (i := i) (j := j))
    (fun {i j} ↦ DirectSum.GNonUnitalNonAssocSemiring.zero_mul
      (A := fun k : ℕ ↦ singularCohomology R X (2 * k)) (i := i) (j := j))
    (fun {i j} ↦ DirectSum.GNonUnitalNonAssocSemiring.mul_add
      (A := fun k : ℕ ↦ singularCohomology R X (2 * k)) (i := i) (j := j))
    (fun {i j} ↦ DirectSum.GNonUnitalNonAssocSemiring.add_mul
      (A := fun k : ℕ ↦ singularCohomology R X (2 * k)) (i := i) (j := j))

/-- The direct sum of the actual even cohomology groups, with the original cup product. -/
abbrev SingularEvenCohomology : Type u :=
  ⨁ k : ℕ, singularCohomology R X (2 * k)

/-- Inclusion of a homogeneous class into the even cohomology ring. -/
def singularEvenCohomologyOf (k : ℕ) :
    singularCohomology R X (2 * k) →ₗ[R] SingularEvenCohomology R X :=
  DirectSum.lof R ℕ (fun j : ℕ ↦ singularCohomology R X (2 * j)) k

/-- The homogeneous inclusion preserves exactly the original even cup product. -/
theorem singularEvenCohomologyOf_cup (p q : ℕ)
    (a : singularCohomology R X (2 * p)) (b : singularCohomology R X (2 * q)) :
    singularEvenCohomologyOf R X (p + q) (singularCohomologyEvenCup R X p q a b) =
      singularEvenCohomologyOf R X p a * singularEvenCohomologyOf R X q b :=
  (DirectSum.of_mul_of
    (A := fun j : ℕ ↦ singularCohomology R X (2 * j)) a b).symm

/-- The original cohomological unit is the unit of the even cohomology ring. -/
@[simp] theorem singularEvenCohomologyOf_one :
    singularEvenCohomologyOf R X 0 (singularCohomologyOne R X) = 1 := rfl

/-- A homogeneous inclusion loses no information about the original cohomology class. -/
theorem singularEvenCohomologyOf_injective (k : ℕ) :
    Function.Injective (singularEvenCohomologyOf R X k) :=
  DirectSum.of_injective k

end AtiyahSinger
