/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyPowerNaturality
public import AtiyahSinger.Topology.ProjectiveChernCoefficients

/-!
# Naturality of the normalized projective coefficients

Public module ID: M2006.

A specified commutative square transports the leading-power relation using
the original pullbacks. Uniqueness of its two genuine power-basis expansions
then identifies the normalized Chern coefficients. The unit and above-rank
zero cases are retained separately, including rank zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

/-- The normalized coefficients are natural under the specified square of genuine power bases. -/
theorem projectiveChernCoefficient_pullback
    {X₁ X₂ Y₁ Y₂ : Type u} [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (π₁ : C(Y₁, X₁)) (π₂ : C(Y₂, X₂)) (f : C(X₂, X₁)) (g : C(Y₂, Y₁))
    (hsquare : π₁.comp g = f.comp π₂) (r : ℕ) (t : singularCohomology ℤ Y₁ 2)
    (hb₁ : Function.Bijective
      (singularCohomologyPowerCombination ℤ π₁ t r r (fun i ↦ Nat.le_of_lt i.isLt)))
    (hb₂ : Function.Bijective
      (singularCohomologyPowerCombination ℤ π₂ (singularCohomologyPullback ℤ g 2 t)
        r r (fun i ↦ Nat.le_of_lt i.isLt))) (k : ℕ) :
    singularCohomologyPullback ℤ f (2 * k) (projectiveChernCoefficient π₁ r t hb₁ k) =
      projectiveChernCoefficient π₂ r (singularCohomologyPullback ℤ g 2 t) hb₂ k := by
  classical
  by_cases hk : k = 0
  · subst k
    simpa only [projectiveChernCoefficient, ↓reduceDIte] using singularCohomologyPullback_one ℤ f
  by_cases hkr : k ≤ r
  · -- Pull back the actual leading-power expansion before applying uniqueness on the new base.
    let C₁ := singularCohomologyPowerCombination ℤ π₁ t r r (fun i ↦ Nat.le_of_lt i.isLt)
    let t₂ := singularCohomologyPullback ℤ g 2 t
    let C₂ := singularCohomologyPowerCombination ℤ π₂ t₂ r r (fun i ↦ Nat.le_of_lt i.isLt)
    let a₁ := (LinearEquiv.ofBijective C₁ hb₁).symm
      (singularCohomologyDegreeTwoPow ℤ Y₁ t r)
    let a₂ := (LinearEquiv.ofBijective C₂ hb₂).symm
      (singularCohomologyDegreeTwoPow ℤ Y₂ t₂ r)
    let b (i : Fin r) := singularCohomologyPullback ℤ f (2 * (r - i.val)) (a₁ i)
    have ha₁ : C₁ a₁ = singularCohomologyDegreeTwoPow ℤ Y₁ t r :=
      (LinearEquiv.ofBijective C₁ hb₁).apply_symm_apply _
    have ha₂ : C₂ a₂ = singularCohomologyDegreeTwoPow ℤ Y₂ t₂ r :=
      (LinearEquiv.ofBijective C₂ hb₂).apply_symm_apply _
    have hbb : C₂ b = singularCohomologyDegreeTwoPow ℤ Y₂ t₂ r := by
      calc
        C₂ b = singularCohomologyPullback ℤ g (2 * r) (C₁ a₁) :=
          (singularCohomologyPowerCombination_pullback ℤ π₁ π₂ f g hsquare
            t r r (fun i ↦ Nat.le_of_lt i.isLt) a₁).symm
        _ = singularCohomologyPullback ℤ g (2 * r)
            (singularCohomologyDegreeTwoPow ℤ Y₁ t r) := congrArg _ ha₁
        _ = singularCohomologyDegreeTwoPow ℤ Y₂ t₂ r :=
          singularCohomologyPullback_degreeTwoPow ℤ g t r
    have hab : a₂ = b := hb₂.injective (ha₂.trans hbb.symm)
    let i : Fin r := ⟨r - k, by omega⟩
    have hdegree : r - i.val = k := by dsimp only [i]; omega
    have htransport (p q : ℕ) (hpq : p = q) (a : singularCohomology ℤ X₁ (2 * p)) :
        singularCohomologyPullback ℤ f (2 * q)
            ((eqToIso (congrArg (fun j ↦ singularCohomology ℤ X₁ (2 * j)) hpq)).hom a) =
          (eqToIso (congrArg (fun j ↦ singularCohomology ℤ X₂ (2 * j)) hpq)).hom
            (singularCohomologyPullback ℤ f (2 * p) a) := by
      subst q
      rfl
    simp only [projectiveChernCoefficient, dite_eq_right hk, dite_eq_left hkr]
    change singularCohomologyPullback ℤ f (2 * k)
        ((-1 : ℤ) ^ (k + 1) • (eqToIso
          (congrArg (fun j ↦ singularCohomology ℤ X₁ (2 * j)) hdegree)).hom (a₁ i)) =
      (-1 : ℤ) ^ (k + 1) • (eqToIso
        (congrArg (fun j ↦ singularCohomology ℤ X₂ (2 * j)) hdegree)).hom (a₂ i)
    rw [map_zsmul, hab, htransport (r - i.val) k hdegree]
  · -- Naturality also retains the definitionally zero coefficients above the original rank.
    simp only [projectiveChernCoefficient, dite_eq_right hk, dite_eq_right hkr, map_zero]

end AtiyahSinger
