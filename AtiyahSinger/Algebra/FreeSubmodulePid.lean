/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Submodules of arbitrary free modules over a PID

Public module ID: M0029.

The usual leading-coordinate proof works for an arbitrary well-ordered basis.
Every vector has finite support, so elimination uses well-founded induction,
without any finite-generation assumption. This is needed for the integral
universal coefficient argument on the actual, generally infinite singular chains.

The argument is the standard submodule theorem over a principal ideal domain;
it extends the finite-rank submodule result currently available in mathlib.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module Submodule

universe u v

/-- A submodule of an arbitrary free module over a PID is free. -/
theorem moduleFree_submodule_of_pid (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Free R M] (N : Submodule R M) : Module.Free R N := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hwf : WellFounded ((· < ·) : ι → ι → Prop) := WellOrderingRel.isWellOrder.wf
  -- At each index, the possible leading coefficients form an ideal.
  let F (i : ι) : Submodule R N :=
    { carrier := {x | ∀ j, i < j → b.repr x.val j = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy j hj
        simp [hx j hj, hy j hj]
      smul_mem' := by
        intro a x hx j hj
        simp [hx j hj] }
  let c (i : ι) : N →ₗ[R] R := (b.coord i).comp N.subtype
  let I (i : ι) : Ideal R := (F i).map (c i)
  let a (i : ι) : R := Submodule.IsPrincipal.generator (I i)
  have hex (i : ι) : ∃ x : N, x ∈ F i ∧ c i x = a i :=
    Submodule.IsPrincipal.generator_mem (I i)
  choose x hx hcx using hex
  let J := {i : ι // a i ≠ 0}
  let w : J → N := fun i ↦ x i.val
  have hc (i : ι) (z : N) : c i z = b.repr z.val i := rfl
  have hbelow (i j : ι) (hij : i < j) : c j (x i) = 0 := hx i j hij
  -- A finite linear relation is detected at its largest nonzero coordinate.
  have hind : LinearIndependent R w := by
    apply linearIndependent_iff.mpr
    intro l hl
    by_contra hn
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image l.support Subtype.val
      (Finsupp.support_nonempty_iff.mpr hn)
    have hs : ∑ j ∈ l.support, l j * c i.val (w j) = 0 := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
        smul_eq_mul, map_zero] using congrArg (c i.val) hl
    have hsum : (∑ j ∈ l.support, l j * c i.val (w j)) = l i * a i.val := by
      rw [Finset.sum_eq_single i]
      · rw [show c i.val (w i) = a i.val from hcx i.val]
      · intro j hj hji
        have hlt : j.val < i.val := lt_of_le_of_ne (hmax j hj)
          (fun h ↦ hji (Subtype.ext h))
        rw [show c i.val (w j) = 0 from hbelow j.val i.val hlt, mul_zero]
      · exact fun h ↦ (h hi).elim
    exact (mul_ne_zero (Finsupp.mem_support_iff.mp hi) i.property) (hsum.symm.trans hs)
  -- Eliminate the largest coordinate. The residual support has a strictly smaller maximum.
  let P : Submodule R N := Submodule.span R (Set.range w)
  have hbounded (i : ι) : ∀ z : N, z ∈ F i → z ∈ P := by
    induction i using hwf.induction with
    | h i ih =>
      intro z hz
      have hzI : c i z ∈ I i := ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hxi⟩ : ∃ r : R, c i z = r * a i ∧ r • x i ∈ P := by
        obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd (I i)).mp hzI
        by_cases ha : a i = 0
        · refine ⟨0, ?_, by simp⟩
          change c i z = a i * s at hs
          rw [hs, ha, mul_zero, zero_mul]
        · refine ⟨s, ?_, P.smul_mem s (Submodule.subset_span ⟨⟨i, ha⟩, rfl⟩)⟩
          exact hs.trans (mul_comm _ _)
      let y : N := z - r • x i
      have hyi : c i y = 0 := by
        simp only [y, map_sub, map_smul, smul_eq_mul, hcx]
        rw [hr, sub_self]
      have hy : ∀ j, i ≤ j → b.repr y.val j = 0 := by
        intro j hij
        rcases hij.eq_or_lt with h | h
        · subst j
          exact hyi
        · change b.repr (z.val - r • (x i).val) j = 0
          simp [hz j h, hx i j h]
      have hyP : y ∈ P := by
        by_cases hy0 : y = 0
        · simp [hy0]
        have hne : (b.repr y.val).support.Nonempty := by
          apply Finsupp.support_nonempty_iff.mpr
          intro he
          apply hy0
          apply Subtype.ext
          exact b.repr.injective (he.trans (map_zero _).symm)
        let j := (b.repr y.val).support.max' hne
        have hj : j ∈ (b.repr y.val).support := Finset.max'_mem _ hne
        have hji : j < i := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hj) (hy j (le_of_not_gt h))
        apply ih j hji y
        intro k hjk
        apply Finsupp.notMem_support_iff.mp
        intro hk
        exact (not_lt_of_ge ((b.repr y.val).support.le_max' k hk)) hjk
      have hzEq : z = y + r • x i := by simp [y]
      rw [hzEq]
      exact P.add_mem hyP hxi
  have hspan : ⊤ ≤ P := by
    intro z _
    by_cases hz : z = 0
    · simp [hz]
    have hne : (b.repr z.val).support.Nonempty := by
      apply Finsupp.support_nonempty_iff.mpr
      intro he
      apply hz
      apply Subtype.ext
      exact b.repr.injective (he.trans (map_zero _).symm)
    let i := (b.repr z.val).support.max' hne
    apply hbounded i z
    intro j hij
    apply Finsupp.notMem_support_iff.mp
    intro hj
    exact (not_lt_of_ge ((b.repr z.val).support.le_max' j hj)) hij
  exact Module.Free.of_basis (Basis.mk hind hspan)

end AtiyahSinger
