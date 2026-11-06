/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm

/-!
# Fredholm approximation at an operator with closed range and finite kernel

Public module ID: M0958.

A closed-range Hilbert operator with finite kernel is Fredholm if it belongs
to the operator-norm closure of the Fredholm operators. The bounded inverse
on its kernel complement supplies a left inverse modulo finite rank. Openness
is applied to this already Fredholm composite before canceling the factors.

This standard semi-Fredholm argument is needed for the original associated
graded graph: its Green bound must be established before its positive elliptic
regularizations can be used. There is no assertion about arbitrary limits of
Fredholm operators.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Closed range and finite kernel make Fredholm norm approximation sufficient. -/
theorem isFredholm_of_closed_range_of_finite_ker_of_mem_closure
    (T : E →L[ℂ] F) (hclosed : IsClosed (T.range : Set F))
    (hfinite : FiniteDimensional ℂ T.ker)
    (happrox : T ∈ closure {R : E →L[ℂ] F | R.IsFredholm}) : T.IsFredholm := by
  classical
  let : FiniteDimensional ℂ T.ker := hfinite
  let : CompleteSpace T.range := hclosed.completeSpace_coe
  let N := T.ker.orthogonal
  -- The original operator is a Banach isomorphism from the kernel complement to its range.
  let A : N →L[ℂ] T.range := (T.comp N.subtypeL).codRestrict T.range (fun x ↦ ⟨x, rfl⟩)
  have hA : Function.Bijective A := by
    constructor
    · intro x y hxy
      apply sub_eq_zero.mp
      apply Subtype.ext
      have hT : T ((x - y : N) : E) = 0 := by
        have h := congrArg Subtype.val hxy
        change T (x : E) = T (y : E) at h
        simpa only [Submodule.coe_sub, map_sub, sub_eq_zero] using h
      have hker : ((x - y : N) : E) ∈ T.ker := hT
      exact inner_self_eq_zero.mp ((x - y).property _ hker)
    · rintro ⟨z, x, rfl⟩
      refine ⟨⟨x - T.ker.starProjection x, T.ker.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      apply Subtype.ext
      change T (x - T.ker.starProjection x) = T x
      rw [map_sub]
      exact (congrArg (fun z : F ↦ T x - z)
        (T.ker.starProjection_apply_mem x)).trans (sub_zero _)
  let e : N ≃L[ℂ] T.range :=
    (LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquivOfContinuous A.continuous
  let S : F →L[ℂ] E :=
    N.subtypeL.comp (e.symm.toContinuousLinearMap.comp T.range.orthogonalProjectionOnto)
  have hST (x : E) : S (T x) = x - T.ker.starProjection x := by
    let y : N := ⟨x - T.ker.starProjection x, T.ker.sub_starProjection_mem_orthogonal x⟩
    have hy : e y = (⟨T x, ⟨x, rfl⟩⟩ : T.range) := by
      apply Subtype.ext
      change T (x - T.ker.starProjection x) = T x
      rw [map_sub]
      exact (congrArg (fun z : F ↦ T x - z)
        (T.ker.starProjection_apply_mem x)).trans (sub_zero _)
    change (e.symm (T.range.orthogonalProjectionOnto (T x)) : E) = _
    rw [T.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, ⟨x, rfl⟩⟩,
      ← hy, e.symm_apply_apply]
  have hcomposite : (S.comp T).IsFredholm := by
    have hprojection : IsCompactOperator T.ker.starProjection :=
      (isCompactOperator_of_locallyCompactSpace_dom T.ker.orthogonalProjectionOnto).clm_comp
        T.ker.subtypeL
    have h := isFredholm_add_compact (ContinuousLinearMap.id ℂ E)
      (-T.ker.starProjection) ContinuousLinearMap.IsFredholm.id hprojection.neg
    convert h using 1
    ext x
    simpa only [comp_apply, add_apply, neg_apply, id_apply, sub_eq_add_neg] using hST x
  -- Openness is used at S*T, whose Fredholmness has already been proved.
  let U : Set (E →L[ℂ] F) := {R | (S.comp R).IsFredholm}
  have hU : IsOpen U := by
    apply ContinuousLinearMap.isOpen_setOfPred_isFredholm.preimage
    fun_prop
  obtain ⟨R, hSR, hR⟩ := mem_closure_iff.mp happrox U hU hcomposite
  have hS : S.IsFredholm := hR.comp_iff_left.mp hSR
  exact hS.comp_iff_right.mp hcomposite

end AtiyahSinger
