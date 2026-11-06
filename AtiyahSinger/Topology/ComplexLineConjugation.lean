/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexLineChern
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.Determinant

/-!
# Conjugate-linear comparison of the original first Chern class

Public module ID: M1709.

Orientation-reversing real coordinates negate the normalized complex-plane
class. An actual conjugate-linear equivalence of the original line fibers
therefore negates their first Chern classes, by uniqueness of the same normalized
Thom classes and naturality along the actual zero sections.

Source: Milnor--Stasheff, sections 9 and 14, the Euler definition of the first
Chern class and the reversal of the positive complex line orientation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A real linear orientation reversal negates the specified complex-plane generator. -/
theorem complexOrientationClass_pullback_of_det_neg
    (e : ULift.{u} ℂ ≃L[ℝ] ULift.{u} ℂ) (he : LinearMap.det e.toLinearMap < 0) :
    relativeSingularCohomologyPullback ℤ (⟨e, e.continuous⟩ : C(ULift.{u} ℂ, ULift.{u} ℂ))
      (A := (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)))
      (B := (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)))
      (fun _ hz hzero ↦ hz (e.injective (hzero.trans e.map_zero.symm))) 2
      complexOrientationClass = -complexOrientationClass := by
  classical
  let b := Complex.basisOneI.map (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
  have ho : Orientation.map (Fin 2) e.toLinearEquiv b.orientation = -b.orientation := by
    rw [← Module.Basis.orientation_map]
    exact (b.orientation_comp_linearEquiv_eq_neg_iff_det_neg e.toLinearEquiv).mpr he
  -- Reversing the chosen orientation negates the same signed relative simplex cycle.
  have hcycle : realOrientationCycle b (-b.orientation) =
      -realOrientationCycle b b.orientation := by
    unfold realOrientationCycle
    rw [← map_neg]
    congr 1
    apply Subtype.ext
    change realOrientationRelativeChain b (-b.orientation) =
      -realOrientationRelativeChain b b.orientation
    simp only [realOrientationRelativeChain, Module.Ray.ne_neg_self, ite_false, ite_true]
    erw [← map_neg, ← map_neg]
    rfl
  have hneg : realOrientationClass b (-b.orientation) =
      -realOrientationClass b b.orientation := by
    apply (existsUnique_realOrientationClass b (-b.orientation)).unique
    · exact realOrientationClass_evaluation b (-b.orientation)
    · unfold realOrientationEvaluation
      rw [hcycle]
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact realOrientationClass_evaluation b b.orientation
  have hclass : complexOrientationClass.{u} = realOrientationClass b b.orientation := by
    apply (existsUnique_realOrientationClass b b.orientation).unique
    · have h := complexOrientationClass_evaluation.{u}
      unfold complexOrientationEvaluation at h
      rw [complexOrientationCycle_eq_realOrientationCycle] at h
      exact h
    · exact realOrientationClass_evaluation b b.orientation
  -- Naturality transports the native orientation; its reversal fixes the required sign.
  have hp := realOrientationClass_pullback b b.orientation b (-b.orientation) e ho
  rw [hneg, map_neg] at hp
  rw [hclass]
  exact neg_eq_iff_eq_neg.mp hp

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [ComplexBundle.IsFiniteRank E]
  (hE : ∀ x : X, Module.finrank ℂ (E x) = 1)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual continuous conjugate-linear bundle equivalence negates the first Chern class. -/
theorem firstChernClass_eq_neg_of_conjugateLinearEquiv
    {F : X → Type u} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [ComplexBundle.IsFiniteRank F]
    (hF : ∀ x : X, Module.finrank ℂ (F x) = 1) (e : ∀ x : X, E x ≃ₗ⋆[ℂ] F x)
    (he : Continuous (fun z : TotalSpace Unit E ↦ (⟨z.proj, e z.proj z.snd⟩ :
      TotalSpace Unit F))) :
    firstChernClass E hE = -firstChernClass F hF := by
  let f : C(TotalSpace Unit E, TotalSpace Unit F) :=
    ⟨fun z ↦ ⟨z.proj, e z.proj z.snd⟩, he⟩
  let A : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  let B : Set (TotalSpace Unit F) := {z | z.snd ≠ 0}
  have hf : Set.MapsTo f A B := by
    intro z hz hzero
    exact hz ((e z.proj).injective (hzero.trans (e z.proj).map_zero.symm))
  -- The scalar conjugation is the same real reflection in every complex fiber coordinate.
  let j : ULift.{u} ℂ ≃L[ℝ] ULift.{u} ℂ :=
    (ContinuousLinearEquiv.ulift.trans Complex.conjCLE).trans ContinuousLinearEquiv.ulift.symm
  let jMap : C(ULift.{u} ℂ, ULift.{u} ℂ) := ⟨j, j.continuous⟩
  have hj : Set.MapsTo jMap {z : ULift.{u} ℂ | z ≠ 0} {z : ULift.{u} ℂ | z ≠ 0} :=
    fun _ hz hzero ↦ hz (j.injective (hzero.trans j.map_zero.symm))
  have hjdet : LinearMap.det j.toLinearMap < 0 := by
    have hd := LinearMap.det_conj Complex.conjAe.toLinearEquiv.toLinearMap
      (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
    change LinearMap.det j.toLinearMap = LinearMap.det Complex.conjAe.toLinearEquiv.toLinearMap
      at hd
    rw [hd, Complex.det_conjAe]
    norm_num
  have hjclass : relativeSingularCohomologyPullback ℤ jMap hj 2 complexOrientationClass =
      -complexOrientationClass := complexOrientationClass_pullback_of_det_neg j hjdet
  have hthom : -relativeSingularCohomologyPullback ℤ f hf 2
      (complexLineThomClass F hF) = complexLineThomClass E hE := by
    apply (existsUnique_complexLineThomClass E hE).unique
    · intro x c
      let := ComplexBundle.finite_fiber (E := F) x
      let dL : F x ≃ₗ[ℂ] ℂ :=
        ((e x).symm.trans c.toLinearEquiv).trans (starLinearEquiv ℂ)
      let d : F x ≃L[ℂ] ℂ := dL.toContinuousLinearEquiv
      have hd : Set.MapsTo (complexLineFiberMap F x d) {z : ULift.{u} ℂ | z ≠ 0} B := by
        intro z hz hzero
        apply hz
        apply ULift.ext
        change d.symm z.down = 0 at hzero
        exact d.symm.injective (by simpa using hzero)
      have hcomp : f.comp (complexLineFiberMap E x c) =
          (complexLineFiberMap F x d).comp jMap := by
        apply ContinuousMap.ext
        intro z
        apply congrArg (TotalSpace.mk x)
        change e x (c.symm z.down) = d.symm (star z.down)
        simp [d, dL]
      rw [map_neg, ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      simp only [hcomp]
      rw [relativeSingularCohomologyPullback_comp ℤ jMap (complexLineFiberMap F x d) hj hd 2,
        ModuleCat.comp_apply,
        complexLineThomClass_fiber, hjclass, neg_neg]
    · exact (existsUnique_complexLineThomClass E hE).exists.choose_spec
  -- The total map fixes the base and carries its actual zero section to the target zero section.
  let zE : C(X, TotalSpace Unit E) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section E⟩
  let zF : C(X, TotalSpace Unit F) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section F⟩
  have hz : f.comp zE = zF := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (TotalSpace.mk x) (e x).map_zero
  have hsq : singularCohomologyPullback ℤ f 2 ≫ singularCohomologyPullback ℤ zE 2 =
      singularCohomologyPullback ℤ zF 2 := by
    let C := singularCohomologyFunctor ℤ 2
    change C.map (TopCat.ofHom f).op ≫ C.map (TopCat.ofHom zE).op = _
    rw [← C.map_comp, ← op_comp]
    change singularCohomologyPullback ℤ (f.comp zE) 2 = _
    rw [hz]
  change singularCohomologyPullback ℤ zE 2
    (relativeSingularCohomologyToOrdinary ℤ A 2 (complexLineThomClass E hE)) = _
  rw [← hthom, map_neg, map_neg]
  apply congrArg Neg.neg
  change (relativeSingularCohomologyPullback ℤ f hf 2 ≫
    relativeSingularCohomologyToOrdinary ℤ A 2 ≫ singularCohomologyPullback ℤ zE 2)
      (complexLineThomClass F hF) = _
  rw [← Category.assoc, relativeSingularCohomologyPullback_toOrdinary, Category.assoc, hsq]
  rfl

end AtiyahSinger
