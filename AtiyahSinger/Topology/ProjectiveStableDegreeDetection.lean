/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomialEvaluation
public import AtiyahSinger.Topology.ProjectiveLowDegreeCohomology

/-!
# Stable-degree detection on an actual projective bundle

Public module ID: M2024.

In cohomological degree `2n` with `n < r`, where `r` is the original bundle
rank, the Leray--Hirsch source has only its initial tautological powers:
every higher shift has zero homology.
These truncated power bases make multiplication by the original tautological
root injective before reaching its first projective relation.

Source: the projective bundle theorem and its stable-degree consequence,
Hatcher, Vector Bundles and K-Theory, Section 3.1. The base remains arbitrary
and the actual singular cochain comparison and its specified root are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

set_option maxHeartbeats 1000000 in
-- The coefficient bijection retains the actual shifted homology and canonical degree transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For `n < r`, Leray--Hirsch gives the truncated power basis in cohomological degree `2n`. -/
theorem singularCohomologyPowerCombination_truncated_bijective_of_lerayHirsch
    (π : C(Y, X)) (t : singularCohomology R Y 2) (r n : ℕ) (hn : n < r)
    (c : ∀ i : ULift.{u} (Fin r), singularCocycles R Y (2 * i.down.val))
    (hc : ∀ i : ULift.{u} (Fin r), singularCocycleClass R Y (2 * i.down.val) (c i) =
      singularCohomologyDegreeTwoPow R Y t i.down.val)
    (hLH : Function.Bijective (homologyMap
      (singularCohomologyLerayHirschMap R π (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) c)
        (2 * n))) :
    Function.Bijective (singularCohomologyPowerCombination R π t (n + 1) n
      (fun i ↦ Nat.le_of_lt_succ i.isLt)) := by
  classical
  let I := ULift.{u} (Fin r)
  let inc (i : Fin (n + 1)) : Fin r := ⟨i.val, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) hn⟩
  have hinc : Function.Injective inc := by
    intro i j hij
    have hval : i.val = j.val := congrArg (fun z : Fin r ↦ z.val) hij
    exact Fin.ext hval
  let C (i : I) : CochainComplex (ModuleCat.{u} R) ℕ :=
    (singularCochains R X).extend (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * i.down.val))
  have hdeg (i : Fin (n + 1)) : 2 * (n - i.val) + 2 * i.val = 2 * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]
  let J (i : Fin (n + 1)) : (C (ULift.up (inc i))).homology (2 * n) ≅
      singularCohomology R X (2 * (n - i.val)) :=
    (singularCochains R X).extendHomologyIso
      (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * i.val)) (hdeg i)
  have hzero (i : I) (hi : n < i.down.val) : IsZero ((C i).homology (2 * n)) := by
    apply (exactAt_iff_isZero_homology _ _).mp
    exact extend_exactAt _ _ (2 * n) (by
      intro j hj
      change j + 2 * i.down.val = 2 * n at hj
      omega)
  let P (a : (cochainFamilyProduct R C).homology (2 * n)) (i : Fin (n + 1)) :=
    (J i).hom (homologyMap (cochainFamilyProductProjection R C (ULift.up (inc i))) (2 * n) a)
  have hprod := bijective_homologyMap_cochainFamilyProductProjection R C (2 * n)
  -- Initial coefficients retain their shift isomorphisms; all remaining homology groups vanish.
  have hP : Function.Bijective P := by
    constructor
    · intro a b hab
      apply hprod.injective
      funext i
      by_cases hi : i.down.val ≤ n
      · let j : Fin (n + 1) := ⟨i.down.val, Nat.lt_succ_of_le hi⟩
        apply (ConcreteCategory.bijective_of_isIso (J j).hom).injective
        exact congrFun hab j
      · let := ModuleCat.isZero_iff_subsingleton.mp (hzero i (Nat.lt_of_not_ge hi))
        exact Subsingleton.elim _ _
    · intro b
      let v (i : I) : (C i).homology (2 * n) :=
        if hi : i.down.val ≤ n then (J ⟨i.down.val, Nat.lt_succ_of_le hi⟩).inv
          (b ⟨i.down.val, Nat.lt_succ_of_le hi⟩) else 0
      obtain ⟨a, ha⟩ := hprod.surjective v
      refine ⟨a, ?_⟩
      funext i
      change (J i).hom
        (homologyMap (cochainFamilyProductProjection R C (ULift.up (inc i))) (2 * n) a) = b i
      have hai := congrFun ha (ULift.up (inc i))
      have hv : v (ULift.up (inc i)) = (J i).inv (b i) := by
        dsimp only [v, inc]
        rw [dite_eq_left (Nat.le_of_lt_succ i.isLt)]
      exact (congrArg (J i).hom (hai.trans hv)).trans (Iso.inv_hom_id_apply (J i) (b i))
  have hsupported (p q k : ℕ) (hk : p + q = k) (z : singularCocycles R Y q)
      (a : ((singularCochains R X).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) q)).homology k) :
      homologyMap
        (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
            (ComplexShape.embeddingUp'Add (1 : ℕ) q) ≫ singularCochainCupMap R Y q z) k a =
        (eqToIso (congrArg (fun j ↦ singularCohomology R Y j) hk)).hom
          (singularCohomologyCup R Y p q
            (singularCohomologyPullback R π p
              (((singularCochains R X).extendHomologyIso
                (ComplexShape.embeddingUp'Add (1 : ℕ) q) hk).hom a))
            (singularCocycleClass R Y q z)) := by
    subst k
    let H := (singularCochains R X).extendHomologyIso
      (ComplexShape.embeddingUp'Add (1 : ℕ) q) (j := p) rfl
    have h := homologyMap_pullback_singularCochainCupMap R π q z p (H.hom a)
    rw [Iso.hom_inv_id_apply] at h
    exact h
  have hcast (p q k : ℕ) (hk : p + q = k)
      (x : singularCohomology R Y (2 * p)) (y : singularCohomology R Y (2 * q)) :
      (eqToIso (congrArg (fun j ↦ singularCohomology R Y j)
        ((Nat.mul_add 2 p q).symm.trans (congrArg (2 * ·) hk)))).hom
          (singularCohomologyCup R Y (2 * p) (2 * q) x y) =
        (eqToIso (congrArg (fun j ↦ singularCohomology R Y (2 * j)) hk)).hom
          (singularCohomologyEvenCup R Y p q x y) := by
    subst k
    rfl
  let F := singularCohomologyLerayHirschMap R π (fun i : I ↦ 2 * i.down.val) c
  have hformula (a : (cochainFamilyProduct R C).homology (2 * n)) :
      homologyMap F (2 * n) a = singularCohomologyPowerCombination R π t (n + 1) n
        (fun i ↦ Nat.le_of_lt_succ i.isLt) (P a) := by
    have hfull := homologyMap_singularCohomologyLerayHirschMap R π
      (fun i : I ↦ 2 * i.down.val) c (2 * n) a
    rw [singularCohomologyPowerCombination_apply]
    apply hfull.trans
    symm
    apply Fintype.sum_of_injective (fun i : Fin (n + 1) ↦ (ULift.up (inc i) : I))
      (ULift.up_injective.comp hinc)
    · intro i hi
      have hi' : n < i.down.val := by
        by_contra h
        have hle := Nat.le_of_not_gt h
        apply hi
        exact ⟨⟨i.down.val, Nat.lt_succ_of_le hle⟩, by apply ULift.ext; apply Fin.ext; rfl⟩
      let := ModuleCat.isZero_iff_subsingleton.mp (hzero i hi')
      rw [show homologyMap (cochainFamilyProductProjection R C i) (2 * n) a = 0 from
        Subsingleton.elim _ _, map_zero]
    · intro i
      have h := hsupported (2 * (n - i.val)) (2 * i.val) (2 * n)
        (hdeg i) (c (ULift.up (inc i)))
        (homologyMap (cochainFamilyProductProjection R C (ULift.up (inc i))) (2 * n) a)
      rw [hc (ULift.up (inc i))] at h
      have he := hcast (n - i.val) i.val n (Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt))
        (singularCohomologyPullback R π (2 * (n - i.val)) (P a i))
        (singularCohomologyDegreeTwoPow R Y t i.val)
      dsimp only [P, J] at he
      have hf := h.trans he
      exact hf.symm
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := hP.surjective a
    obtain ⟨y, rfl⟩ := hP.surjective b
    exact congrArg P (hLH.injective ((hformula x).trans (hab.trans (hformula y).symm)))
  · intro b
    obtain ⟨a, ha⟩ := hLH.surjective b
    exact ⟨P a, (hformula a).symm.trans ha⟩

namespace ComplexBundle

open Bundle

variable (r : ℕ) (E : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For `n < r`, the initial tautological powers span uniquely in cohomological degree `2n`. -/
theorem hermitianProjectivePowerCombination_truncated_bijective (n : ℕ) (hn : n < r) :
    Function.Bijective (singularCohomologyPowerCombination R
      (hermitianProjectiveProjection r E h)
      (singularCohomologyChangeCoefficients R (HermitianProjectiveBundle r E h) 2
        (hermitianProjectiveChernRoot r E h)) (n + 1) n
      (fun i ↦ Nat.le_of_lt_succ i.isLt)) := by
  classical
  let Q := HermitianProjectiveBundle r E h
  let t : singularCohomology R Q 2 :=
    singularCohomologyChangeCoefficients R Q 2 (hermitianProjectiveChernRoot r E h)
  have hrep (k : ℕ) (a : singularCohomology R Q k) :
      ∃ c : singularCocycles R Q k, singularCocycleClass R Q k c = a := by
    let C := singularCochains R Q
    obtain ⟨c, hc⟩ := (C.sc k).moduleCatToCycles.range.mkQ_surjective
      ((C.sc k).moduleCatHomologyIso.hom a)
    refine ⟨c, ?_⟩
    change (C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ c) = a
    rw [hc, Iso.hom_inv_id_apply]
  choose c hc using fun i : ULift.{u} (Fin r) ↦
    hrep (2 * i.down.val) (singularCohomologyDegreeTwoPow R Q t i.down.val)
  exact singularCohomologyPowerCombination_truncated_bijective_of_lerayHirsch R
    (hermitianProjectiveProjection r E h) t r n hn c hc
    (homologyMap_hermitianProjectiveLerayHirsch_bijective R r E h c hc (2 * n))

set_option maxHeartbeats 1000000 in
-- The stable comparison keeps every homogeneous coefficient and its canonical shifted degree.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Multiplication by the original tautological root is injective before its first relation. -/
theorem hermitianProjectiveChernRoot_evenCup_injective (n : ℕ) (hn : n + 1 < r) :
    Function.Injective
      ((singularCohomologyEvenCup R (HermitianProjectiveBundle r E h) n 1).flip
        (singularCohomologyChangeCoefficients R (HermitianProjectiveBundle r E h) 2
          (hermitianProjectiveChernRoot r E h))) := by
  classical
  let Q := HermitianProjectiveBundle r E h
  let p := hermitianProjectiveProjection r E h
  let t : singularCohomology R Q 2 :=
    singularCohomologyChangeCoefficients R Q 2 (hermitianProjectiveChernRoot r E h)
  let P (m : ℕ) := singularCohomologyPowerCombination R p t (m + 1) m
    (fun i ↦ Nat.le_of_lt_succ i.isLt)
  have hP := hermitianProjectivePowerCombination_truncated_bijective R r E h n (by omega)
  have hP' := hermitianProjectivePowerCombination_truncated_bijective R r E h (n + 1) hn
  have hsucc (i : Fin (n + 1)) : n - i.val = n + 1 - i.succ.val := by
    simp
  let shift (a : ∀ i : Fin (n + 1), singularCohomology R X (2 * (n - i.val))) :
      ∀ i : Fin (n + 2), singularCohomology R X (2 * (n + 1 - i.val)) :=
    Fin.cases 0 (fun i ↦
      (eqToIso (congrArg (fun j ↦ singularCohomology R X (2 * j)) (hsucc i))).hom (a i))
  have htransport (a b : ℕ) (hab : a = b) (z : singularCohomology R X (2 * a)) :
      singularCohomologyPullback R p (2 * b)
        ((eqToIso (congrArg (fun j ↦ singularCohomology R X (2 * j)) hab)).hom z) =
      (eqToIso (congrArg (fun j ↦ singularCohomology R Q (2 * j)) hab)).hom
        (singularCohomologyPullback R p (2 * a) z) := by
    subst b
    rfl
  -- Homogeneous inclusion records each coefficient times the same original root power.
  have hcombo (m : ℕ) (a : ∀ i : Fin (m + 1),
      singularCohomology R X (2 * (m - i.val))) :
      singularEvenCohomologyOf R Q m (P m a) =
        ∑ i : Fin (m + 1),
          singularEvenCohomologyOf R Q (m - i.val)
            (singularCohomologyPullback R p (2 * (m - i.val)) (a i)) *
              singularEvenCohomologyOf R Q 1 t ^ i.val := by
    rw [singularCohomologyPowerCombination_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso R Q (Nat.sub_add_cancel
      (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup,
      singularEvenCohomologyOf_degreeTwoPow]
  have hshift (a : ∀ i : Fin (n + 1), singularCohomology R X (2 * (n - i.val))) :
      P (n + 1) (shift a) = singularCohomologyEvenCup R Q n 1 (P n a) t := by
    apply singularEvenCohomologyOf_injective R Q (n + 1)
    rw [hcombo, singularEvenCohomologyOf_cup, hcombo, Finset.sum_mul, Fin.sum_univ_succ]
    simp only [shift, Fin.cases_zero, Fin.cases_succ, map_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [htransport _ _ (hsucc i), singularEvenCohomologyOf_eqToIso R Q (hsucc i)]
    rw [Fin.val_succ, pow_succ, mul_assoc]
  -- In the next degree this coefficient shift has zero initial entry and retains every old entry.
  intro a b hab
  obtain ⟨x, rfl⟩ := hP.surjective a
  obtain ⟨y, rfl⟩ := hP.surjective b
  have hxy : shift x = shift y := hP'.injective
    ((hshift x).trans (hab.trans (hshift y).symm))
  have hcoeff : x = y := by
    funext i
    exact (ConcreteCategory.bijective_of_isIso
      (eqToIso (congrArg (fun j ↦ singularCohomology R X (2 * j)) (hsucc i))).hom).injective
        (congrFun hxy i.succ)
  exact congrArg (P n) hcoeff

end ComplexBundle

end AtiyahSinger
