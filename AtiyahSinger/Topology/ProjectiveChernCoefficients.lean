/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyRootPowerReduction

/-!
# Normalized coefficients from an actual projective power basis

Public module ID: M2004.

When the specified original cup-power comparison is bijective, expand the
leading power in that basis. Alternating signs give its normalized Chern
coefficients, with degree-zero unit and zero above the rank. A vanishing
split root product identifies these coefficients with the actual elementary
symmetric classes. The basis theorem is an explicit premise here and must
be proved for the actual projective bundle before this construction is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (π : C(Y, X)) (r : ℕ) (t : singularCohomology ℤ Y 2)
  (hb : Function.Bijective
    (singularCohomologyPowerCombination ℤ π t r r (fun i ↦ Nat.le_of_lt i.isLt)))

/-- The normalized signed coefficient of the actual leading-power expansion.
The original cohomology unit is used in degree zero and all above-rank coefficients vanish. -/
def projectiveChernCoefficient (k : ℕ) : singularCohomology ℤ X (2 * k) :=
  if hk : k = 0 then hk.symm ▸ singularCohomologyOne ℤ X
  else if hkr : k ≤ r then
    let i : Fin r := ⟨r - k, by omega⟩
    let a := (LinearEquiv.ofBijective
      (singularCohomologyPowerCombination ℤ π t r r (fun i ↦ Nat.le_of_lt i.isLt)) hb).symm
        (singularCohomologyDegreeTwoPow ℤ Y t r)
    (-1 : ℤ) ^ (k + 1) • (eqToIso
      (congrArg (fun j ↦ singularCohomology ℤ X (2 * j))
        (show r - i.val = k by dsimp only [i]; omega))).hom (a i)
  else 0

/-- A split characteristic relation identifies the normalized coefficients in every degree. -/
theorem projectiveChernCoefficient_eq_elementarySymmetric
    (x : Fin r → singularCohomology ℤ X 2)
    (h : ∏ i : Fin r, (singularEvenCohomologyOf ℤ Y 1 t -
      singularEvenCohomologyPullback ℤ π (singularEvenCohomologyOf ℤ X 1 (x i))) = 0)
    (k : ℕ) :
    projectiveChernCoefficient π r t hb k =
      singularCohomologyElementarySymmetric ℤ X (List.ofFn x) k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp only [projectiveChernCoefficient, ↓reduceDIte]
    cases List.ofFn x <;> rfl
  by_cases hkr : k ≤ r
  · -- The genuine power-basis injectivity identifies all lower-power coefficients at once.
    let C := singularCohomologyPowerCombination ℤ π t r r (fun i ↦ Nat.le_of_lt i.isLt)
    let a := (LinearEquiv.ofBijective C hb).symm
      (singularCohomologyDegreeTwoPow ℤ Y t r)
    let b (i : Fin r) : singularCohomology ℤ X (2 * (r - i.val)) :=
      (-1 : ℤ) ^ (r - i.val + 1) •
        singularCohomologyElementarySymmetric ℤ X (List.ofFn x) (r - i.val)
    have ha : C a = singularCohomologyDegreeTwoPow ℤ Y t r :=
      (LinearEquiv.ofBijective C hb).apply_symm_apply _
    have hbb : C b = singularCohomologyDegreeTwoPow ℤ Y t r :=
      singularCohomologyPowerCombination_esymm_eq_pow π r x t h
    have hab : a = b := hb.injective (ha.trans hbb.symm)
    let i : Fin r := ⟨r - k, by omega⟩
    have hdegree : r - i.val = k := by dsimp only [i]; omega
    have htransport (p q : ℕ) (hpq : p = q) :
        (eqToIso (congrArg (fun j ↦ singularCohomology ℤ X (2 * j)) hpq)).hom
          ((-1 : ℤ) ^ (p + 1) •
            singularCohomologyElementarySymmetric ℤ X (List.ofFn x) p) =
          (-1 : ℤ) ^ (q + 1) •
            singularCohomologyElementarySymmetric ℤ X (List.ofFn x) q := by
      subst q
      rfl
    rw [projectiveChernCoefficient, dite_eq_right hk, dite_eq_left hkr]
    change (-1 : ℤ) ^ (k + 1) • (eqToIso
      (congrArg (fun j ↦ singularCohomology ℤ X (2 * j)) hdegree)).hom (a i) = _
    rw [hab]
    change (-1 : ℤ) ^ (k + 1) • (eqToIso
      (congrArg (fun j ↦ singularCohomology ℤ X (2 * j)) hdegree)).hom
        ((-1 : ℤ) ^ (r - i.val + 1) •
          singularCohomologyElementarySymmetric ℤ X (List.ofFn x) (r - i.val)) = _
    rw [htransport (r - i.val) k hdegree, smul_smul, ← mul_pow]
    simp
  · -- The same finite root list has no elementary symmetric term above its length.
    have hlt : r < k := Nat.lt_of_not_ge hkr
    simp only [projectiveChernCoefficient, dite_eq_right hk, dite_eq_right hkr]
    apply singularEvenCohomologyOf_injective ℤ X k
    rw [map_zero, singularEvenCohomologyOf_elementarySymmetric]
    exact (Multiset.esymm_of_card_lt (by simpa using hlt)).symm

end AtiyahSinger
