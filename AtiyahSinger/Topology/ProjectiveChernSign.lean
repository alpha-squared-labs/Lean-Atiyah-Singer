/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveChernNaturality

/-!
# Chern coefficients under a projective orientation reversal

Public module ID: M2007.

A self-map over the same base which negates the projective degree-two generator
forces the original normalized Chern coefficient in degree `2k` to equal its
`(-1)^k` multiple. The proof compares the same leading-power expansion in the
original finite cohomology basis. No new bundle model or root family is chosen.

Source: project supplement to the projective characteristic relation, used for
the self-conjugacy argument of Milnor--Stasheff, section 15, Lemma 15.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A root-reversing projective self-map over the base forces `cₖ = (-1)^k • cₖ`. -/
theorem projectiveChernCoefficient_eq_neg_one_pow_smul_of_pullback_neg
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (r : ℕ) (t : singularCohomology ℤ Y 2)
    (hb : Function.Bijective
      (singularCohomologyPowerCombination ℤ π t r r (fun i ↦ Nat.le_of_lt i.isLt)))
    (g : C(Y, Y)) (hπ : π.comp g = π)
    (ht : singularCohomologyPullback ℤ g 2 t = -t) (k : ℕ) :
    projectiveChernCoefficient π r t hb k =
      (-1 : ℤ) ^ k • projectiveChernCoefficient π r t hb k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero, one_smul]
  by_cases hkr : k ≤ r
  · let C := singularCohomologyPowerCombination ℤ π t r r (fun i ↦ Nat.le_of_lt i.isLt)
    let a := (LinearEquiv.ofBijective C hb).symm (singularCohomologyDegreeTwoPow ℤ Y t r)
    have ha : C a = singularCohomologyDegreeTwoPow ℤ Y t r :=
      (LinearEquiv.ofBijective C hb).apply_symm_apply _
    -- Negating the root signs its i-th power, keeping the same pulled-back coefficient.
    have hsignCombination : C (fun i ↦ (-1 : ℤ) ^ i.val • a i) =
        singularCohomologyPowerCombination ℤ π (-t) r r (fun i ↦ Nat.le_of_lt i.isLt) a := by
      apply singularEvenCohomologyOf_injective ℤ Y r
      simp only [C, singularCohomologyPowerCombination_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [singularEvenCohomologyOf_eqToIso ℤ Y
        (Nat.sub_add_cancel (Nat.le_of_lt i.isLt)),
        singularEvenCohomologyOf_eqToIso ℤ Y
          (Nat.sub_add_cancel (Nat.le_of_lt i.isLt)),
        singularEvenCohomologyOf_cup, singularEvenCohomologyOf_cup,
        singularEvenCohomologyOf_degreeTwoPow, singularEvenCohomologyOf_degreeTwoPow]
      simp only [map_zsmul, map_neg, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      rw [neg_pow (singularEvenCohomologyOf ℤ Y 1 t) i.val]
      ring
    have hsignPower : singularCohomologyDegreeTwoPow ℤ Y (-t) r =
        (-1 : ℤ) ^ r • singularCohomologyDegreeTwoPow ℤ Y t r := by
      apply singularEvenCohomologyOf_injective ℤ Y r
      rw [singularEvenCohomologyOf_degreeTwoPow, map_zsmul,
        singularEvenCohomologyOf_degreeTwoPow]
      rw [map_neg, neg_pow (singularEvenCohomologyOf ℤ Y 1 t) r]
      simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    -- Pull back the original leading-power equation along the specified self-map.
    have hbase (n : ℕ) : singularCohomologyPullback ℤ (ContinuousMap.id X) n =
        𝟙 (singularCohomology ℤ X n) := (singularCohomologyFunctor ℤ n).map_id _
    have hpull := singularCohomologyPowerCombination_pullback ℤ π π (ContinuousMap.id X) g
      (by simpa only [ContinuousMap.id_comp] using hπ) t r r
      (fun i ↦ Nat.le_of_lt i.isLt) a
    simp only [hbase, ModuleCat.id_apply, ht] at hpull
    have hcompare : C (fun i ↦ (-1 : ℤ) ^ i.val • a i) = C ((-1 : ℤ) ^ r • a) := by
      rw [hsignCombination, ← hpull]
      change singularCohomologyPullback ℤ g (2 * r) (C a) = C ((-1 : ℤ) ^ r • a)
      rw [ha, singularCohomologyPullback_degreeTwoPow, ht, hsignPower, map_zsmul, ha]
    have hcoeff := hb.injective hcompare
    let i : Fin r := ⟨r - k, by omega⟩
    have hdegree : r - i.val = k := by dsimp only [i]; omega
    have hsign : (-1 : ℤ) ^ i.val * (-1) ^ r = (-1) ^ k := by
      rw [← pow_add, show i.val + r = 2 * i.val + k by dsimp only [i]; omega,
        pow_add, pow_mul]
      norm_num
    have hself : a i = (-1 : ℤ) ^ k • a i := by
      have hz := congrArg (fun z : singularCohomology ℤ X (2 * (r - i.val)) ↦
        (-1 : ℤ) ^ i.val • z) (congrFun hcoeff i)
      change (-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ i.val • a i) =
        (-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ r • a i) at hz
      rw [smul_smul, smul_smul, hsign, ← mul_pow] at hz
      simpa using hz
    -- The original normalized coefficient has only its prescribed scalar and degree transport.
    rw [projectiveChernCoefficient, dite_eq_right hk, dite_eq_left hkr]
    change (-1 : ℤ) ^ (k + 1) • (eqToIso
      (congrArg (fun n ↦ singularCohomology ℤ X (2 * n)) hdegree)).hom (a i) =
      (-1 : ℤ) ^ k • ((-1 : ℤ) ^ (k + 1) • (eqToIso
        (congrArg (fun n ↦ singularCohomology ℤ X (2 * n)) hdegree)).hom (a i))
    have htransport := congrArg ((eqToIso
      (congrArg (fun n ↦ singularCohomology ℤ X (2 * n)) hdegree)).hom) hself
    rw [map_zsmul] at htransport
    calc
      _ = (-1 : ℤ) ^ (k + 1) • ((-1 : ℤ) ^ k • (eqToIso
          (congrArg (fun n ↦ singularCohomology ℤ X (2 * n)) hdegree)).hom (a i)) :=
        congrArg ((-1 : ℤ) ^ (k + 1) • ·) htransport
      _ = _ := smul_comm _ _ _
  · simp only [projectiveChernCoefficient, dite_eq_right hk, dite_eq_right hkr]
    exact (zsmul_zero ((-1 : ℤ) ^ k)).symm

end AtiyahSinger
