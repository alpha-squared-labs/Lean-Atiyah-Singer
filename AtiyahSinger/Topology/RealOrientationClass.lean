/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationCycle
public import AtiyahSinger.Topology.RealOrientationCycleSign
public import AtiyahSinger.Topology.RealOrientationCycleNaturality
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality
public import AtiyahSinger.Topology.SimplexLocalHomology
public import AtiyahSinger.Topology.SingularIntegralEvaluation
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Orientation

/-!
# Integral fiber classes normalized by a native real orientation

Public module ID: M2043.

For a real basis b of rank r, the affine simplex with vertices
-sum_i b_i, b_0, ..., b_(r-1) contains zero in its interior and has positive
determinant r+1 in that basis. Its sign is corrected according to the given
native Orientation. The resulting relative homology cycle determines the
unique integral cohomology class whose cap followed by augmentation is +1.
Independence of b and naturality refer to these actual normalized classes.

This is the normalization of Milnor--Stasheff, Characteristic Classes,
section 9, p.96. The affine coordinates and signed-chain implementation are
project supplements. Hatcher, Algebraic Topology, section 3.3, supplies the
relative local homology and cap interpretation. No generator is assumed.

Rank zero requires care: native Orientation has two signs, while every empty
basis has the canonical positive orientation. The simplex is then the point
zero, with coefficient +1 or -1 according to the given orientation. We do not
claim that a negative zero-dimensional orientation has a positive basis.
For positive rank the signed simplex is equivalent to choosing a positive
basis, without making existence of that basis an additional assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Convexity Opposite
open scoped Simplicial

universe u

variable {r : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r))

/-- Evaluation on the geometrically specified cycle by the original cap and augmentation. -/
def realOrientationEvaluation
    (a : relativeSingularCohomology ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r) : ℤ :=
  (((TopCat.of V).singularHomology₀ε (singularCoefficient ℤ))
    (relativeSingularCapProduct ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r 0
      a (realOrientationCycle b o))).down

/-- The native real orientation specifies exactly one integral class of evaluation one. -/
theorem existsUnique_realOrientationClass :
    ∃! a : relativeSingularCohomology ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r,
      realOrientationEvaluation b o a = 1 := by
  /- The actual signed simplex is a primitive integral local homology class,
  computed by the same triple boundary and simplex-face recursion. Local homology
  below the dimension vanishes. Integral Kronecker duality therefore identifies
  evaluation on this very cycle with the integers, including the zero-dimensional
  signed point. Taking the fiber over one gives existence and uniqueness. -/
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  have hprev : r = 0 ∨ Subsingleton
      (relativeSingularHomology ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) (r - 1)) := by
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr (subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv
        ℤ b.equivFun.toContinuousLinearEquiv (r - 1) (by omega))
  have hbij := relativeSingularCapProduct_augmentation_bijective_of_generator ℤ
    (Set.ofPred (fun v : V ↦ v ≠ 0)) r (realOrientationCycle b o)
    (by
      convert realOrientationCycle_is_generator b o using 1
      funext a
      exact int_smul_eq_zsmul
        (relativeSingularHomology ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r).isModule
        a (realOrientationCycle b o)) hprev
  exact hbij.existsUnique 1

/-- The integral relative fiber orientation, selected by geometric evaluation one. -/
def realOrientationClass : relativeSingularCohomology ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r :=
  (existsUnique_realOrientationClass b o).exists.choose

/-- The specified integral fiber orientation has the prescribed positive evaluation. -/
theorem realOrientationClass_evaluation :
    realOrientationEvaluation b o (realOrientationClass b o) = 1 := by
  /- Take the normalization component of the same existence witness used to
  define the class. The cycle and its sign remain exactly those specified by
  b and o; no independent generator or coefficient convention is substituted. -/
  exact (existsUnique_realOrientationClass b o).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized integral fiber class freely generates its relative cohomology. -/
theorem realOrientationClass_is_generator :
    Function.Bijective (fun a : ℤ ↦ a • realOrientationClass b o) := by
  let E : relativeSingularCohomology ℤ (Set.ofPred (fun z : V ↦ z ≠ 0)) r →+ ℤ :=
    { toFun := realOrientationEvaluation b o
      map_zero' := by
        unfold realOrientationEvaluation
        erw [map_zero, LinearMap.zero_apply, map_zero]
        rfl
      map_add' := by
        intro a a'
        unfold realOrientationEvaluation
        erw [map_add, LinearMap.add_apply, map_add]
        rfl }
  have hnorm : E (realOrientationClass b o) = 1 :=
    realOrientationClass_evaluation b o
  -- The unique fiber over one forces the kernel to vanish: translate a kernel element
  -- by the specified class, then apply uniqueness to this same evaluation functional.
  have hinj : Function.Injective E := by
    intro a a' haa'
    have heval : E (a - a' + realOrientationClass b o) = 1 := by
      rw [map_add, map_sub, haa', sub_self, zero_add, hnorm]
    have heq := (existsUnique_realOrientationClass b o).unique heval hnorm
    exact sub_eq_zero.mp (add_right_cancel (heq.trans (zero_add _).symm))
  constructor
  · -- Evaluation of an integral multiple is its coefficient.
    intro a a' haa'
    have h := congrArg E haa'
    simpa only [map_zsmul, hnorm, smul_eq_mul, mul_one] using h
  · -- Injectivity identifies every class with the multiple given by its evaluation.
    intro a
    refine ⟨E a, hinj ?_⟩
    rw [map_zsmul, hnorm, smul_eq_mul, mul_one]

/-- The normalized class depends on the native orientation and not the coordinate basis. -/
theorem realOrientationClass_basis_independent (c : Module.Basis (Fin r) ℝ V) :
    realOrientationClass b o = realOrientationClass c o := by
  /- Stage 1: the actual basis-change homeomorphism acts on local homology by
  the sign of its determinant. The native basis-orientation comparison records
  the same sign, so the two signed simplex cycles represent the same generator.
  Stage 2: cap evaluation and uniqueness identify their two normalized classes.
  In rank zero both bases are the unique empty basis and the sign is unchanged.
  No continuous family of the arbitrarily chosen bases is required. -/
  apply (existsUnique_realOrientationClass b o).unique
  · exact realOrientationClass_evaluation b o
  · unfold realOrientationEvaluation
    rw [realOrientationCycle_basis_independent b c o]
    exact realOrientationClass_evaluation c o

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedVariables false in

/-- A continuous linear equivalence preserving the given native orientations preserves the class. -/
theorem realOrientationClass_pullback
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : Module.Basis (Fin r) ℝ W) (oW : Orientation ℝ W (Fin r))
    (e : V ≃L[ℝ] W) (he : Orientation.map (Fin r) e.toLinearEquiv o = oW) :
    relativeSingularCohomologyPullback ℤ (⟨e, e.continuous⟩ : C(V, W))
      (A := (Set.ofPred (fun v : V ↦ v ≠ 0))) (B := (Set.ofPred (fun w : W ↦ w ≠ 0)))
      (fun v hv hv0 ↦ hv (e.injective (hv0.trans e.map_zero.symm))) r
      (realOrientationClass c oW) = realOrientationClass b o := by
  /- Stage 1: transport b by the actual linear equivalence e. The orientation
  hypothesis makes its signed simplex the pushforward of the original signed
  simplex, including the sign of a zero-dimensional orientation.
  Stage 2: naturality of the original relative cap and augmentation identifies
  evaluations. Basis independence replaces the transported basis by c, and
  uniqueness of the class with evaluation one gives the displayed equality. -/
  let f : C(V, W) := ⟨e, e.continuous⟩
  have hf : Set.MapsTo f (Set.ofPred (fun v : V ↦ v ≠ 0)) (Set.ofPred (fun w : W ↦ w ≠ 0)) :=
    fun _ hv h ↦ hv (e.injective (h.trans e.map_zero.symm))
  let d := b.map e.toLinearEquiv
  have hcycle : relativeSingularHomologyMap ℤ f hf r (realOrientationCycle b o) =
      realOrientationCycle d oW := by
    simpa only [he] using realOrientationCycle_map b o e
  have hclass : realOrientationClass c oW = realOrientationClass d oW :=
    realOrientationClass_basis_independent c oW d
  apply (existsUnique_realOrientationClass b o).unique
  · unfold realOrientationEvaluation
    rw [relativeSingularCapProduct_augmentation]
    change (singularCochainHomologyEvaluation ℤ
      (relativeSingularChains ℤ (Set.ofPred (fun v : V ↦ v ≠ 0))) r
      (HomologicalComplex.homologyMap
        ((singularCochainDualFunctor ℤ).map (relativeSingularChainsMap ℤ f hf).op) r
        (realOrientationClass c oW)) (realOrientationCycle b o)).down = 1
    rw [← singularCochainHomologyEvaluation_naturality]
    change (singularCochainHomologyEvaluation ℤ
      (relativeSingularChains ℤ (Set.ofPred (fun w : W ↦ w ≠ 0))) r
      (realOrientationClass c oW)
      (relativeSingularHomologyMap ℤ f hf r (realOrientationCycle b o))).down = 1
    rw [hcycle, hclass, ← relativeSingularCapProduct_augmentation]
    exact realOrientationClass_evaluation d oW
  · exact realOrientationClass_evaluation b o

end AtiyahSinger
