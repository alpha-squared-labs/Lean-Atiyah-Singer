/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Path

/-!
# Paths through positive-determinant real matrices

Public module ID: M1996.

Elementary transvections give paths in determinant one. The standard
two-coordinate diagonal factor is a product of six transvections, so the
existing matrix elimination theorem gives a path for every real special
linear matrix. A positive one-coordinate scaling handles any positive
determinant. These actual paths supply homotopies of punctured real fibers;
no homology generator or orientation comparison is assumed in constructing them.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Matrix

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Every real matrix of determinant one is joined to the identity within determinant one. -/
theorem exists_matrix_path_of_det_eq_one (A : Matrix ι ι ℝ) (hA : A.det = 1) :
    ∃ p : Path (1 : Matrix ι ι ℝ) A, ∀ t, (p t).det = 1 := by
  let P (g : SpecialLinearGroup ι ℝ) : Prop :=
    ∃ p : Path (1 : Matrix ι ι ℝ) g.val, ∀ t, (p t).det = 1
  have hmul (g h : SpecialLinearGroup ι ℝ) (hg : P g) (hh : P h) : P (g * h) := by
    obtain ⟨p, hp⟩ := hg
    obtain ⟨q, hq⟩ := hh
    refine ⟨(p.mul q).cast (one_mul 1).symm rfl, ?_⟩
    intro t
    change (p t * q t).det = 1
    rw [Matrix.det_mul, hp, hq, one_mul]
  have htrans (i j : ι) (hij : i ≠ j) (a : ℝ) :
      P (SpecialLinearGroup.transvection hij a) := by
    let p : Path (1 : Matrix ι ι ℝ) (Matrix.transvection i j a) :=
      { toFun := fun t ↦ Matrix.transvection i j (t.val * a)
        continuous_toFun := by
          apply continuous_pi
          intro k
          apply continuous_pi
          intro l
          simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
          split_ifs <;> fun_prop
        source' := by simp
        target' := by simp }
    exact ⟨p, fun t ↦ Matrix.det_transvection_of_ne i j hij _⟩
  -- Elimination reduces the special linear group to transvections and two-coordinate scalings.
  have hdiag (i j : ι) (hij : i ≠ j) (a : ℝ) (ha : a ≠ 0) :
      P (SpecialLinearGroup.diag2n hij a ha) := by
    have hstep (B : Matrix ι ι ℝ) (v w : ι) (s : ℝ) (k l : ι) :
        (B * Matrix.transvection v w s) k l =
          B k l + if l = w then s * B k v else 0 := by
      by_cases h : l = w
      · subst l
        simp [Matrix.mul_transvection_apply_same]
      · simp [Matrix.mul_transvection_apply_of_ne v w k l h, h]
    have hfactor : SpecialLinearGroup.diag2n hij a ha =
        SpecialLinearGroup.transvection hij a *
          SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
          SpecialLinearGroup.transvection hij a *
          SpecialLinearGroup.transvection hij (-1) *
          SpecialLinearGroup.transvection hij.symm 1 *
          SpecialLinearGroup.transvection hij (-1) := by
      apply Subtype.ext
      change Matrix.diagonal (fun k ↦ if k = i then a else if k = j then a⁻¹ else 1) =
        Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) *
          Matrix.transvection i j a * Matrix.transvection i j (-1) *
          Matrix.transvection j i 1 * Matrix.transvection i j (-1)
      ext k l
      simp only [hstep]
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        by_cases hli : l = i <;> by_cases hlj : l = j
      all_goals
        first
        | exact (hij (hki.symm.trans hkj)).elim
        | exact (hij (hli.symm.trans hlj)).elim
        | simp [Matrix.diagonal_apply, Matrix.transvection, Matrix.single_apply,
            Matrix.one_apply, (eq_comm : i = k ↔ k = i), (eq_comm : j = k ↔ k = j),
            (eq_comm : i = l ↔ l = i), (eq_comm : j = l ↔ l = j),
            hki, hkj, hli, hlj, hij, Ne.symm hij, ha]
    rw [hfactor]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_goals exact htrans _ _ _ _
  rcases subsingleton_or_nontrivial ι with hι | hι
  · let : Subsingleton ι := hι
    have heq := Subsingleton.elim (α := SpecialLinearGroup ι ℝ) ⟨A, hA⟩ 1
    have hmat : A = 1 := congrArg Subtype.val heq
    subst A
    exact ⟨Path.refl 1, fun _ ↦ Matrix.det_one⟩
  · let : Nontrivial ι := hι
    exact SpecialLinearGroup.diagonal_transvection_induction' P ⟨A, hA⟩
      (fun i j hij a ha ↦ hdiag i j hij a ha) htrans hmul

/-- Every positive-determinant real matrix admits a path from the identity with positive
determinant throughout, including the empty matrix. -/
theorem exists_matrix_path_of_det_pos (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    ∃ p : Path (1 : Matrix ι ι ℝ) A, ∀ t, 0 < (p t).det := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let : IsEmpty ι := hι
    have heq : A = 1 := Subsingleton.elim _ _
    subst A
    exact ⟨Path.refl 1, fun _ ↦ by simp⟩
  · let : Nonempty ι := hι
    let i : ι := Classical.choice hι
    let d (s : ℝ) : Matrix ι ι ℝ :=
      Matrix.diagonal (Function.update (fun _ ↦ (1 : ℝ)) i s)
    have hd (s : ℝ) : (d s).det = s := by
      simp [d, Matrix.det_diagonal, Function.update_apply]
    have hdprod (s t : ℝ) : d s * d t = d (s * t) := by
      dsimp [d]
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      by_cases hj : j = i <;> simp [hj]
    have hd1 : d 1 = 1 := by ext j k; simp [d]
    let B := d A.det⁻¹ * A
    have hB : B.det = 1 := by
      rw [Matrix.det_mul, hd, inv_mul_cancel₀ hA.ne']
    obtain ⟨p, hp⟩ := exists_matrix_path_of_det_eq_one B hB
    -- Only the positive determinant factor is scaled; the determinant-one factor follows p.
    let q : Path (1 : Matrix ι ι ℝ) (d A.det) :=
      { toFun := fun t ↦ d ((1 - t.val) + t.val * A.det)
        continuous_toFun := by
          apply continuous_pi
          intro j
          apply continuous_pi
          intro k
          simp only [d, Matrix.diagonal_apply, Function.update_apply]
          split_ifs <;> fun_prop
        source' := by simpa using hd1
        target' := by simp }
    have hend : d A.det * B = A := by
      dsimp [B]
      rw [← Matrix.mul_assoc, hdprod, mul_inv_cancel₀ hA.ne', hd1, one_mul]
    refine ⟨(q.mul p).cast (one_mul 1).symm hend.symm, ?_⟩
    intro t
    change 0 < (q t * p t).det
    rw [Matrix.det_mul, hp, mul_one]
    change 0 < (d ((1 - t.val) + t.val * A.det)).det
    rw [hd]
    have ht0 := t.property.1
    have ht1 := t.property.2
    by_cases ht : t.val = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1)
        (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hA)

end AtiyahSinger
