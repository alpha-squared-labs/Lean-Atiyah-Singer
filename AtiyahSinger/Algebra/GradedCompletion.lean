/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequence
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Normalized units in the completion of a graded algebra

Public module ID: M0030.

SG III.11, printed p.229, and MS section 19, printed pp.219--220, use all
formal sums 1+b₁+b₂+... with bₖ in the original degree-k component. Here
the actual power-series coefficients record those components, and the
existing Cauchy multiplication supplies their product. The group is an
explicit subgroup of the original power-series units. Its equivalence
with every normalized graded coefficient sequence ensures that using
units does not restrict the source's domain.

The actual transformation constructed in MultiplicativeSequence induces
the group homomorphism of SG Lemma 11.9 on this full domain. No new
multiplication, abstract characteristic-class map, or geometric roots are
introduced. The algebra is commutative in the ordinary sense; applications
to cohomology use its even-degree or fourfold-degree regrading.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {R : Type*} [CommRing R] [Algebra ℚ R]
  (𝒜 : ℕ → Submodule ℚ R) [GradedAlgebra 𝒜]

/-- Inversion of a normalized formal sum preserves its original graded coefficient spaces. -/
theorem coeff_invOfUnit_mem_graded (b : PowerSeries R) (hb₀ : b.constantCoeff = 1)
    (hb : ∀ k : ℕ, PowerSeries.coeff k b ∈ 𝒜 k) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit b 1) ∈ 𝒜 k := by
  /- The inverse has constant coefficient one. Induct strongly on k
  using PowerSeries.coeff_invOfUnit. Every term of the recursive Cauchy
  sum multiplies b_i in 𝒜 i by an already constructed inverse coefficient
  in 𝒜 j with i+j=k and j<k. Graded multiplication puts it in 𝒜 k;
  finite sums and negation preserve that submodule. The normalization
  hb₀ is exactly what makes this formal inverse the inverse of b.
  This construction requires neither finite support nor nilpotence. -/
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [PowerSeries.coeff_invOfUnit]
    by_cases hk : k = 0
    · subst k
      -- Normalization identifies the inverse's degree-zero coefficient with b₀.
      simpa [PowerSeries.coeff_zero_eq_constantCoeff, hb₀] using hb 0
    · -- Each recursive Cauchy summand has the original total degree k.
      simp only [hk, ↓reduceIte, inv_one, Units.val_one, neg_one_mul]
      apply (𝒜 k).neg_mem
      apply (𝒜 k).sum_mem
      intro p hp
      by_cases hp₂ : p.2 < k
      · rw [ite_eq_left hp₂]
        have hdegree : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
        simpa only [hdegree] using SetLike.mul_mem_graded (hb p.1) (ih p.2 hp₂)
      · rw [ite_eq_right hp₂]
        exact (𝒜 k).zero_mem

/-- The source's entire group of normalized graded formal sums, with its actual multiplication. -/
def gradedCompletionUnits : Subgroup (PowerSeries R)ˣ where
  carrier := {u | (u : PowerSeries R).constantCoeff = 1 ∧
    ∀ k : ℕ, PowerSeries.coeff k (u : PowerSeries R) ∈ 𝒜 k}
  one_mem' := by
    constructor
    · exact PowerSeries.constantCoeff_one
    · intro k
      by_cases hk : k = 0
      · subst k
        simpa using SetLike.one_mem_graded 𝒜
      · simp [PowerSeries.coeff_one, hk]
  mul_mem' := by
    intro u v hu hv
    constructor
    · change ((u : PowerSeries R) * (v : PowerSeries R)).constantCoeff = 1
      rw [map_mul, hu.1, hv.1, mul_one]
    · intro k
      change PowerSeries.coeff k ((u : PowerSeries R) * (v : PowerSeries R)) ∈ 𝒜 k
      rw [PowerSeries.coeff_mul]
      apply (𝒜 k).sum_mem
      intro p hp
      have hdeg : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
      simpa only [hdeg] using SetLike.mul_mem_graded (hu.2 p.1) (hv.2 p.2)
  inv_mem' := by
    intro u hu
    -- The ambient unit inverse is exactly the normalized recursive power-series inverse.
    have hinv : PowerSeries.invOfUnit (u : PowerSeries R) 1 =
        ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) :=
      u.eq_inv_of_mul_eq_one_left (PowerSeries.mul_invOfUnit (u : PowerSeries R) 1 hu.1)
    constructor
    · rw [← hinv]
      simp
    · intro k
      rw [← hinv]
      exact coeff_invOfUnit_mem_graded 𝒜 (u : PowerSeries R) hu.1 hu.2 k

/-- Every normalized graded coefficient sequence is included, with its genuine formal inverse. -/
def gradedCompletionUnitsEquiv :
    gradedCompletionUnits 𝒜 ≃
      {b : PowerSeries R // b.constantCoeff = 1 ∧
        ∀ k : ℕ, PowerSeries.coeff k b ∈ 𝒜 k} where
  toFun u := ⟨((u : (PowerSeries R)ˣ) : PowerSeries R), u.property⟩
  invFun b :=
    ⟨{ val := b.val
       inv := PowerSeries.invOfUnit b.val 1
       val_inv := PowerSeries.mul_invOfUnit b.val 1 b.property.1
       inv_val := PowerSeries.invOfUnit_mul b.val 1 b.property.1 }, b.property⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    rfl

namespace MultiplicativeSequence

/-- SG Lemma 11.9 as the actual group homomorphism on all normalized graded formal sums. -/
def gradedHom (f : PowerSeries ℚ) (hf : f.constantCoeff = 1) :
    gradedCompletionUnits 𝒜 →* gradedCompletionUnits 𝒜 where
  toFun u := (gradedCompletionUnitsEquiv 𝒜).symm
    ⟨transform f ((u : (PowerSeries R)ˣ) : PowerSeries R),
      constantCoeff_transform f _, coeff_transform_mem 𝒜 f _ u.property.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change transform f (1 : PowerSeries R) = 1
    exact transform_one f
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    change transform f
        (((u : (PowerSeries R)ˣ) : PowerSeries R) * ((v : (PowerSeries R)ˣ) : PowerSeries R)) =
      transform f ((u : (PowerSeries R)ˣ) : PowerSeries R) *
        transform f ((v : (PowerSeries R)ˣ) : PowerSeries R)
    exact transform_mul f hf _ _ u.property.1 v.property.1

end MultiplicativeSequence

end AtiyahSinger
