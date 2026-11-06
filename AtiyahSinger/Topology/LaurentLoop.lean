/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LaurentApproximation
public import AtiyahSinger.Topology.CircleMatrixLoop
public import AtiyahSinger.Topology.StableMatrixLoop
public import Mathlib.Analysis.Matrix.Normed

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units

/-!
# Stable Laurent matrix loops

Public module ID: M1929.

Karoubi III.1.12–1.14, pp.116–117: actual normalized invertible Laurent polynomials,
homotopies with one finite exponent set and continuous coefficients, and the
bijection from their stable classes to continuous stable matrix loop classes.

The matrix norm is the submultiplicative operator norm. Completeness is derived
from the finite product of the complete coefficient algebra. Coefficients may be
noncommutative; no finite-support assumption is imposed on inverse loops.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator unitInterval

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

/-- A normalized Laurent loop in a specified finite general linear group. -/
structure LaurentMatrixLoop (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] where
  /-- The actual finite matrix size, including the zero-size identity loop. -/
  size : ℕ
  /-- The finite Laurent polynomial with matrix coefficients. -/
  polynomial : LaurentPolynomial (Matrix (Fin size) (Fin size) A)
  /-- Its value at the circle base point is the identity. -/
  normalized : laurentPolynomialCircleValue polynomial 1 = 1
  /-- Every value on the circle is invertible. The inverse need not be Laurent. -/
  invertible : ∀ z : Circle, IsUnit (laurentPolynomialCircleValue polynomial z)

namespace LaurentMatrixLoop

variable [CompleteSpace A]

local instance (n : ℕ) : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- The lift of the specified Laurent values into matrix units is continuous. -/
theorem continuous_unitValue (p : LaurentMatrixLoop A) :
    Continuous (fun z : Circle ↦ (p.invertible z).unit) := by
  -- The original values are continuous and inversion is continuous at every Banach-algebra unit.
  apply Units.continuous_iff.mpr
  constructor
  · simp only [Function.comp_def, IsUnit.unit_spec]
    exact continuous_laurentPolynomialCircleValue p.polynomial
  · simp only [← Ring.inverse_unit, IsUnit.unit_spec]
    apply continuous_iff_continuousAt.mpr
    intro z
    have hi := NormedRing.inverse_continuousAt (p.invertible z).unit
    simp only [IsUnit.unit_spec] at hi
    exact hi.comp (continuous_laurentPolynomialCircleValue p.polynomial).continuousAt

/-- The actual continuous circle map into the finite matrix unit group. -/
def toCircleMap (p : LaurentMatrixLoop A) :
    C(Circle, (Matrix (Fin p.size) (Fin p.size) A)ˣ) :=
  ⟨fun z ↦ (p.invertible z).unit, p.continuous_unitValue⟩

/-- The associated interval loop uses the same positive circle parametrization. -/
def toFiniteMatrixLoop (p : LaurentMatrixLoop A) : FiniteMatrixLoop A where
  size := p.size
  loop := circleMapPath p.toCircleMap 1 (by
    apply Units.ext
    exact (p.invertible 1).unit_spec.trans p.normalized)

/-- The continuous stable class of the specified Laurent loop. -/
def stableClass (p : LaurentMatrixLoop A) : StableMatrixLoopClass A :=
  stableMatrixLoopClass p.toFiniteMatrixLoop

/-- Stable Laurent homotopy with one finite exponent set for the entire parameter interval.
The endpoint values are the actual identity-block stabilizations at a common matrix size. -/
def StablyHomotopic (p q : LaurentMatrixLoop A) : Prop :=
  ∃ k l : ℕ, ∃ h : p.size + k = q.size + l,
    ∃ r : LaurentPolynomial C(unitInterval,
        Matrix (Fin (q.size + l)) (Fin (q.size + l)) A),
      let value (t : unitInterval) (z : Circle) :=
        r.coeff.sum (fun j a ↦ (z : ℂ) ^ j • a t)
      (∀ z : Circle, value 0 z =
        cast (congrArg (fun n : ℕ ↦ Matrix (Fin n) (Fin n) A) h)
          (matrixUnitBlockSum (p.invertible z).unit
            (1 : (Matrix (Fin k) (Fin k) A)ˣ) : _)) ∧
      (∀ z : Circle, value 1 z =
        (matrixUnitBlockSum (q.invertible z).unit
          (1 : (Matrix (Fin l) (Fin l) A)ˣ) : _)) ∧
      (∀ t : unitInterval, value t 1 = 1) ∧
      (∀ (t : unitInterval) (z : Circle), IsUnit (value t z))

set_option backward.isDefEq.respectTransparency false in
/-- KA III.1.14, injectivity: stable continuous homotopy can be made Laurent
with exact endpoints and a finite exponent set uniform in the homotopy parameter. -/
theorem stablyHomotopic_iff (p q : LaurentMatrixLoop A) :
    p.StablyHomotopic q ↔ p.toFiniteMatrixLoop.StablyHomotopic q.toFiniteMatrixLoop := by
  /- Stage 1: a continuous-coefficient Laurent polynomial evaluates to a jointly
  continuous matrix family. Its assumed invertibility lifts it to units; the
  fixed value at z=1 gives a based path homotopy at the displayed common size.
  Stage 2: conversely take the actual stabilized path homotopy and use
  circleMapPath_homotopic_iff to descend it to a circle homotopy of units.
  The stabilized endpoints are Laurent: add the identity only to the degree-zero
  block and reindex by the same finSumFinEquiv as matrixUnitBlockSum.
  Stage 3: apply exists_laurent_homotopy_with_endpoints in the finite matrix
  Banach algebra. This gives one Laurent polynomial with continuous coefficients,
  the exact two stabilized endpoint values, and the fixed base point throughout.
  The common dimension equality is transported consistently on both descriptions. -/
  classical
  -- Stabilize the actual Laurent coefficients in precisely the original finite ordering.
  have stabilized_polynomial (p : LaurentMatrixLoop A) (k : ℕ) :
      ∃ s : LaurentPolynomial (Matrix (Fin (p.size + k)) (Fin (p.size + k)) A),
        ∀ z : Circle, laurentPolynomialCircleValue s z =
          (matrixUnitBlockSum (p.invertible z).unit
            (1 : (Matrix (Fin k) (Fin k) A)ˣ) : _) := by
    let L : Matrix (Fin p.size) (Fin p.size) A →ₗ[ℂ]
        Matrix (Fin (p.size + k)) (Fin (p.size + k)) A :=
      { toFun := fun a ↦ Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks a 0 0 (0 : Matrix (Fin k) (Fin k) A))
        map_add' := by
          intro a b
          ext i j
          cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
            simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
        map_smul' := by
          intro c a
          ext i j
          cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
            simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj] }
    let J : Matrix (Fin (p.size + k)) (Fin (p.size + k)) A :=
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (0 : Matrix (Fin p.size) (Fin p.size) A) 0 0
          (1 : Matrix (Fin k) (Fin k) A))
    let s := AddMonoidAlgebra.map L.toAddMonoidHom p.polynomial +
      AddMonoidAlgebra.single 0 J
    refine ⟨s, ?_⟩
    intro z
    have hmap : laurentPolynomialCircleValue
        (AddMonoidAlgebra.map L.toAddMonoidHom p.polynomial) z =
        L (laurentPolynomialCircleValue p.polynomial z) := by
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_map]
      rw [Finsupp.sum_mapRange_index]
      · rw [map_finsuppSum]
        apply Finsupp.sum_congr
        intro j b
        exact (L.map_smul ((z : ℂ) ^ j) (p.polynomial.coeff j)).symm
      · intro j
        simp
    have hsum : laurentPolynomialCircleValue s z =
        L (laurentPolynomialCircleValue p.polynomial z) + J := by
      change ((AddMonoidAlgebra.map L.toAddMonoidHom p.polynomial).coeff +
        Finsupp.single 0 J).sum (fun j b ↦ (z : ℂ) ^ j • b) = _
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_single_index]
        · simpa only [zpow_zero, one_smul, laurentPolynomialCircleValue] using
            congrArg (fun x ↦ x + J) hmap
        · exact smul_zero _
      · intro j hj
        exact smul_zero _
      · intro j hj a b
        exact smul_add _ _ _
    rw [hsum]
    change L (laurentPolynomialCircleValue p.polynomial z) + J =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks ((p.invertible z).unit : _) 0 0 (1 : Matrix (Fin k) (Fin k) A))
    rw [IsUnit.unit_spec]
    ext i j
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [L, J, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  -- Compare the original ordered stabilized paths through their positive circle maps.
  let circle (p : LaurentMatrixLoop A) (k : ℕ) :
      C(Circle, (Matrix (Fin (p.size + k)) (Fin (p.size + k)) A)ˣ) :=
    ⟨fun z ↦ matrixUnitBlockSum (p.invertible z).unit
      (1 : (Matrix (Fin k) (Fin k) A)ˣ),
      (continuous_matrixUnitBlockSum p.size k).comp
        (p.continuous_unitValue.prodMk continuous_const)⟩
  have circle_base (p : LaurentMatrixLoop A) (k : ℕ) : circle p k 1 = 1 := by
    apply Units.ext
    have hp : (p.invertible 1).unit = 1 := Units.ext
      ((p.invertible 1).unit_spec.trans p.normalized)
    change (matrixUnitBlockSum (p.invertible 1).unit
      (1 : (Matrix (Fin k) (Fin k) A)ˣ) :
        Matrix (Fin (p.size + k)) (Fin (p.size + k)) A) = 1
    rw [hp]
    simp [matrixUnitBlockSum]
  have circle_path (p : LaurentMatrixLoop A) (k : ℕ) :
      circleMapPath (circle p k) 1 (circle_base p k) =
        (p.toFiniteMatrixLoop.stabilize k).loop := by
    apply Path.ext
    funext t
    rfl
  have circle_common {n m : ℕ} (h : n = m)
      (f : C(Circle, (Matrix (Fin n) (Fin n) A)ˣ)) (hf : f 1 = 1)
      (g : C(Circle, (Matrix (Fin m) (Fin m) A)ˣ)) (hg : g 1 = 1) :
      Path.Homotopic
        (cast (congrArg (fun d : ℕ ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) h)
          (circleMapPath f 1 hf)) (circleMapPath g 1 hg) ↔
        Nonempty (ContinuousMap.HomotopyWith
          (cast (congrArg (fun d : ℕ ↦ C(Circle, (Matrix (Fin d) (Fin d) A)ˣ)) h) f)
          g (fun a ↦ a 1 = 1)) := by
    subst m
    exact circleMapPath_homotopic_iff f g 1 hf hg
  have cast_value {n m : ℕ} (h : n = m)
      (f : C(Circle, (Matrix (Fin n) (Fin n) A)ˣ)) (z : Circle) :
      ((cast (congrArg (fun d : ℕ ↦ C(Circle, (Matrix (Fin d) (Fin d) A)ˣ)) h) f) z :
        Matrix (Fin m) (Fin m) A) =
        cast (congrArg (fun d : ℕ ↦ Matrix (Fin d) (Fin d) A) h)
          (f z : Matrix (Fin n) (Fin n) A) := by
    subst m
    rfl
  constructor
  · rintro ⟨k, l, h, r, hzero, hone, hbase, hunit⟩
    let f := cast (congrArg
      (fun d : ℕ ↦ C(Circle, (Matrix (Fin d) (Fin d) A)ˣ)) h) (circle p k)
    let g := circle q l
    let R : C(unitInterval × Circle,
        Matrix (Fin (q.size + l)) (Fin (q.size + l)) A) :=
      ⟨fun x ↦ r.coeff.sum (fun j a ↦ (x.2 : ℂ) ^ j • a x.1), by
        unfold Finsupp.sum
        apply continuous_finsetSum
        intro j hj
        have hpower : Continuous (fun z : Circle ↦ (z : ℂ) ^ j) :=
          continuous_subtype_val.comp
            (show Continuous (fun z : Circle ↦ z ^ j) from continuous_id.zpow j)
        exact (hpower.comp continuous_snd).smul
          ((r.coeff j).continuous.comp continuous_fst)⟩
    have hR : ∀ x, IsUnit (R x) := fun x ↦ hunit x.1 x.2
    let V := R.unitsOfForallIsUnit hR
    have hRzero (z : Circle) : R (0, z) = (f z : _) := by
      rw [cast_value h (circle p k) z]
      exact hzero z
    have hRone (z : Circle) : R (1, z) = (g z : _) :=
      hone z
    let H : ContinuousMap.HomotopyWith f g (fun a ↦ a 1 = 1) :=
      { toContinuousMap := V
        map_zero_left := fun z ↦ Units.ext ((hR (0, z)).unit_spec.trans (hRzero z))
        map_one_left := fun z ↦ Units.ext ((hR (1, z)).unit_spec.trans (hRone z))
        prop' := fun t ↦ Units.ext
          ((hR (t, 1)).unit_spec.trans (hbase t)) }
    refine ⟨k, l, h, ?_⟩
    rw [← circle_path p k, ← circle_path q l]
    exact (circle_common h (circle p k) (circle_base p k)
      (circle q l) (circle_base q l)).mpr ⟨H⟩
  · rintro ⟨k, l, h, H⟩
    change p.size + k = q.size + l at h
    rw [← circle_path p k, ← circle_path q l] at H
    obtain ⟨H⟩ := (circle_common h (circle p k) (circle_base p k)
      (circle q l) (circle_base q l)).mp H
    obtain ⟨s, hs⟩ := stabilized_polynomial p k
    obtain ⟨t, ht⟩ := stabilized_polynomial q l
    let s' := cast (congrArg
      (fun d : ℕ ↦ LaurentPolynomial (Matrix (Fin d) (Fin d) A)) h) s
    have hs' (z : Circle) : laurentPolynomialCircleValue s' z =
        ((cast (congrArg
          (fun d : ℕ ↦ C(Circle, (Matrix (Fin d) (Fin d) A)ˣ)) h) (circle p k)) z :
            Matrix (Fin (q.size + l)) (Fin (q.size + l)) A) := by
      have hcast {n m : ℕ} (e : n = m)
          (a : LaurentPolynomial (Matrix (Fin n) (Fin n) A)) :
          laurentPolynomialCircleValue
            (cast (congrArg
              (fun d : ℕ ↦ LaurentPolynomial (Matrix (Fin d) (Fin d) A)) e) a) z =
            cast (congrArg (fun d : ℕ ↦ Matrix (Fin d) (Fin d) A) e)
              (laurentPolynomialCircleValue a z) := by
        subst m
        rfl
      rw [hcast h s, hs, cast_value h (circle p k) z]
      rfl
    -- Forget only the unit certificates; the same homotopy supplies the finite replacement.
    let K : ContinuousMap.HomotopyWith (laurentPolynomialCircleMap s')
        (laurentPolynomialCircleMap t)
        (fun a ↦ a 1 = 1 ∧ ∀ z : Circle, IsUnit (a z)) :=
      { toFun := fun x ↦ (H x : _)
        continuous_toFun := Units.continuous_val.comp H.continuous
        map_zero_left := fun z ↦ (congrArg Units.val (H.apply_zero z)).trans (hs' z).symm
        map_one_left := fun z ↦ (congrArg Units.val (H.apply_one z)).trans (ht z).symm
        prop' := fun v ↦ ⟨congrArg Units.val (H.prop v), fun z ↦ (H (v, z)).isUnit⟩ }
    obtain ⟨r, hzero, hone, hbase, hunit⟩ := exists_laurent_homotopy_with_endpoints s' t K
    have hvalue (z : Circle) (v : unitInterval) :
        laurentPolynomialCircleValue r z v =
          r.coeff.sum (fun j a ↦ (z : ℂ) ^ j • a v) := by
      simp [laurentPolynomialCircleValue, Finsupp.sum, ContinuousMap.sum_apply]
    refine ⟨k, l, h, r, ?_, ?_, ?_, ?_⟩
    · intro z
      exact (hvalue z 0).symm.trans
        ((hzero z).trans ((hs' z).trans (cast_value h (circle p k) z)))
    · intro z
      exact (hvalue z 1).symm.trans ((hone z).trans (ht z))
    · intro v
      exact (hvalue 1 v).symm.trans (hbase v)
    · intro v z
      change IsUnit (r.coeff.sum (fun j a ↦ (z : ℂ) ^ j • a v))
      rw [← hvalue z v]
      exact hunit v z

/-- The actual setoid of stable Laurent homotopies. -/
def stableSetoid : Setoid (LaurentMatrixLoop A) where
  r := StablyHomotopic
  iseqv :=
    { refl := fun p ↦ (p.stablyHomotopic_iff p).mpr
        (FiniteMatrixLoop.stablyHomotopic_equivalence.refl _)
      symm := fun h ↦ (stablyHomotopic_iff _ _).mpr
        (FiniteMatrixLoop.stablyHomotopic_equivalence.symm
          ((stablyHomotopic_iff _ _).mp h))
      trans := fun h₁ h₂ ↦ (stablyHomotopic_iff _ _).mpr
        (FiniteMatrixLoop.stablyHomotopic_equivalence.trans
          ((stablyHomotopic_iff _ _).mp h₁) ((stablyHomotopic_iff _ _).mp h₂)) }

end LaurentMatrixLoop

variable [CompleteSpace A]

/-- Stable Laurent classes formed using actual finite-coefficient homotopies. -/
def StableLaurentLoopClass (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] : Type u :=
  Quotient (LaurentMatrixLoop.stableSetoid (A := A))

/-- The Laurent stable class of the specified finite Laurent matrix loop. -/
def stableLaurentLoopClass (p : LaurentMatrixLoop A) : StableLaurentLoopClass A :=
  Quotient.mk (LaurentMatrixLoop.stableSetoid (A := A)) p

/-- Forgetting the Laurent restriction descends the concrete representative map. -/
def stableLaurentLoopComparison : StableLaurentLoopClass A → StableMatrixLoopClass A :=
  Quotient.lift LaurentMatrixLoop.stableClass (fun p q h ↦
    (stableMatrixLoopClass_eq_iff p.toFiniteMatrixLoop q.toFiniteMatrixLoop).mpr
      ((p.stablyHomotopic_iff q).mp h))

set_option backward.isDefEq.respectTransparency false in
/-- KA III.1.14, surjectivity: every continuous stable loop has a Laurent representative. -/
theorem FiniteMatrixLoop.exists_laurent_representative (p : FiniteMatrixLoop A) :
    ∃ q : LaurentMatrixLoop A, q.stableClass = stableMatrixLoopClass p := by
  /- Stage 1: descend the specified path of matrix units to the circle using
  exists_circleMap_of_path. Composing with the unit value map gives a continuous
  normalized pointwise invertible circle map in exactly the original matrix size.
  Stage 2: apply exists_normalized_laurent_homotopy in the finite matrix Banach
  algebra. Its endpoint supplies the polynomial, normalization and invertibility
  fields of q; all use the same approximating polynomial and homotopy witness.
  Stage 3: lift the homotopy to units and use the positive circle parametrization.
  This is a based homotopy before stabilization, so the displayed stable classes agree. -/
  classical
  -- Descend the specified path, preserving its exact positive circle parametrization.
  let : CompleteSpace (Matrix (Fin p.size) (Fin p.size) A) :=
    inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → A))
  obtain ⟨f, hf, hpath⟩ := exists_circleMap_of_path 1 p.loop
  let F : C(Circle, Matrix (Fin p.size) (Fin p.size) A) :=
    ⟨fun z ↦ (f z : _), Units.continuous_val.comp f.continuous⟩
  have hFbase : F 1 = 1 := congrArg Units.val hf
  have hFunit (z : Circle) : IsUnit (F z) := (f z).isUnit
  obtain ⟨s, ⟨H⟩⟩ := exists_normalized_laurent_homotopy F hFbase hFunit
  -- The same normalized Laurent endpoint determines the polynomial and its certificates.
  have hbase : laurentPolynomialCircleValue s 1 = 1 := by
    exact (H.apply_one 1).symm.trans (H.prop 1).1
  have hunit (z : Circle) : IsUnit (laurentPolynomialCircleValue s z) := by
    change IsUnit ((laurentPolynomialCircleMap s) z)
    rw [← H.apply_one z]
    exact (H.prop 1).2 z
  let q : LaurentMatrixLoop A := ⟨p.size, s, hbase, hunit⟩
  let R := H.toHomotopy.toContinuousMap
  have hR : ∀ x, IsUnit (R x) := fun x ↦ (H.prop x.1).2 x.2
  let V := R.unitsOfForallIsUnit hR
  let K : ContinuousMap.HomotopyWith f q.toCircleMap (fun a ↦ a 1 = 1) :=
    { toContinuousMap := V
      map_zero_left := fun z ↦ Units.ext
        ((hR (0, z)).unit_spec.trans (H.apply_zero z))
      map_one_left := fun z ↦ Units.ext
        ((hR (1, z)).unit_spec.trans ((H.apply_one z).trans (q.invertible z).unit_spec.symm))
      prop' := fun t ↦ Units.ext ((hR (t, 1)).unit_spec.trans (H.prop t).1) }
  -- This is a based homotopy at the original size, before any stabilization.
  have hpaths : Path.Homotopic p.loop q.toFiniteMatrixLoop.loop := by
    rw [← hpath]
    exact (circleMapPath_homotopic_iff f q.toCircleMap 1 hf
      (by apply Units.ext; exact (q.invertible 1).unit_spec.trans q.normalized)).mpr ⟨K⟩
  have hpq : stableMatrixLoopClass p = q.stableClass := by
    apply (stableMatrixLoopClass_eq_iff p q.toFiniteMatrixLoop).mpr
    refine ⟨0, 0, rfl, ?_⟩
    have hstable (a : FiniteMatrixLoop A) : (a.stabilize 0).loop = a.loop := by
      apply Path.ext
      funext t
      apply Units.ext
      ext i j
      change (matrixUnitBlockSum (a.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
        Matrix (Fin (a.size + 0)) (Fin (a.size + 0)) A) i j = (a.loop t : _) i j
      refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
      refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
      change Matrix.fromBlocks (a.loop t : Matrix (Fin a.size) (Fin a.size) A)
        (0 : Matrix (Fin a.size) (Fin 0) A) 0 1
          (finSumFinEquiv.symm (Fin.castAdd 0 i))
          (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
      rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
      rfl
    change Path.Homotopic (p.stabilize 0).loop (q.toFiniteMatrixLoop.stabilize 0).loop
    rw [hstable, hstable]
    exact hpaths
  exact ⟨q, hpq.symm⟩

/-- Karoubi III.1.14: stable Laurent and continuous based loop classes are in bijection. -/
theorem stableLaurentLoopComparison_bijective :
    Function.Bijective (stableLaurentLoopComparison (A := A)) := by
  /- Stage 1: quotient equality in the continuous model is actual stable homotopy.
  The reverse implication of LaurentMatrixLoop.stablyHomotopic_iff supplies
  a Laurent homotopy, proving injectivity by effectiveness of the Laurent quotient.
  Stage 2: choose any finite representative of a continuous stable class and apply
  FiniteMatrixLoop.exists_laurent_representative, proving surjectivity.
  The map is the representative-forgetting map, rather than an unspecified bijection. -/
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
        apply Quotient.sound
        apply (p.stablyHomotopic_iff q).mpr
        exact (stableMatrixLoopClass_eq_iff p.toFiniteMatrixLoop q.toFiniteMatrixLoop).mp hxy
  · intro x
    induction x using Quotient.inductionOn with
    | h p =>
      obtain ⟨q, hq⟩ := p.exists_laurent_representative
      exact ⟨stableLaurentLoopClass q, hq⟩

/-- The comparison equivalence is the same concrete forgetful map on representatives. -/
def stableLaurentLoopEquiv : StableLaurentLoopClass A ≃ StableMatrixLoopClass A :=
  Equiv.ofBijective stableLaurentLoopComparison stableLaurentLoopComparison_bijective

end AtiyahSinger
