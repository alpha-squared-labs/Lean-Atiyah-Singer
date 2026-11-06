/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleCohomologyThom
public import AtiyahSinger.Topology.ComplexLineChern

/-!
# The original complex line Euler normalization

Public module ID: M1710.

The native canonical complex orientation and the original line Thom class
have the same positive fiber normalization. Uniqueness compares the two
specified Thom classes through the identity-on-vectors total homeomorphism.
Their Euler classes therefore agree, and actual coefficient change gives the
rational formula used in the Thom defect calculation.

Source: Milnor--Stasheff, section 14, the first Chern class of a complex line.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original canonical complex line Euler class is the original rational first Chern class. -/
theorem cohomologyEulerClass_complex_line
    {X : Type u} [TopologicalSpace X]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (hline : ∀ x, Module.finrank ℂ (E x) = 1) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℝ (Fin 2))
    letI := h.realNativeFiberBundle 1 hline
    letI := h.realNativeVectorBundle 1 hline
    cohomologyEulerClass ℚ 2 E (h.complexCohomologyOrientation 1 hline).rationalization =
      singularCohomologyRationalization X 2 (firstChernClass E hline) := by
  classical
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let V := EuclideanSpace ℝ (Fin 2)
  let := nativeModelTopology E V
  let := h.realNativeFiberBundle 1 hline
  let := h.realNativeVectorBundle 1 hline
  let o := h.complexCohomologyOrientation 1 hline
  let H := nativeModelTotalHomeomorph E V
  let f : C(TotalSpace V E, TotalSpace Unit E) := ⟨H, H.continuous⟩
  let g : C(TotalSpace Unit E, TotalSpace V E) := ⟨H.symm, H.symm.continuous⟩
  let A := bundleNonzero 2 E
  let B : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  have hf : Set.MapsTo f A B := fun _ hz ↦ hz
  have hg : Set.MapsTo g B A := fun _ hz ↦ hz
  let := isIso_relativeSingularCohomologyPullback_of_inverse ℤ f g hf hg rfl rfl 2
  let I := asIso (relativeSingularCohomologyPullback ℤ f hf 2)
  let T := cohomologyThomClass ℤ 2 E o
  -- Interleaving any actual complex coordinate gives the positive original real frame.
  have ho (x : X) (e : E x ≃L[ℂ] ℂ) :
      let d : E x ≃L[ℂ] ULift.{u} ℂ := e.trans ContinuousLinearEquiv.ulift.symm
      relativeSingularCohomologyPullback ℤ (⟨d.symm, d.symm.continuous⟩ : C(_, _))
        (show Set.MapsTo d.symm {z : ULift.{u} ℂ | z ≠ 0} {v : E x | v ≠ 0} from
          fun _ hz hv ↦ hz (d.symm.injective (hv.trans d.symm.map_zero.symm))) 2
        (o.fiberClass x) = complexOrientationClass := by
    let d : E x ≃L[ℂ] ULift.{u} ℂ := e.trans ContinuousLinearEquiv.ulift.symm
    let eR : ULift.{u} ℂ ≃L[ℝ] E x :=
      { d.symm.toLinearEquiv.restrictScalars ℝ with
        continuous_toFun := d.symm.continuous
        continuous_invFun := d.continuous }
    let b0 := Complex.basisOneI.map (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
    let b := (Module.Basis.singleton (Fin 1) ℂ).map e.symm.toLinearEquiv
    have hmap : b0.map eR.toLinearEquiv = complexBasisRealification b := by
      apply DFunLike.ext
      intro i
      fin_cases i
      · simp [b0, b, eR, d, complexBasisRealification, Module.Basis.smulTower'_apply,
          Complex.coe_basisOneI, finProdFinEquiv, Fin.modNat, ContinuousLinearEquiv.ulift]
      · simpa [b0, b, eR, d, complexBasisRealification, Module.Basis.smulTower'_apply,
          Complex.coe_basisOneI, finProdFinEquiv, Fin.modNat, ContinuousLinearEquiv.ulift] using
          e.symm.map_smul Complex.I 1
    have hOrient : Orientation.map (Fin 2) eR.toLinearEquiv b0.orientation =
        h.complexRealOrientation 1 hline x := by
      rw [← Module.Basis.orientation_map, hmap, h.complexRealOrientation_basis 1 hline x b]
    have hclass : complexOrientationClass.{u} = realOrientationClass b0 b0.orientation := by
      apply (existsUnique_realOrientationClass b0 b0.orientation).unique
      · have hnorm := complexOrientationClass_evaluation.{u}
        unfold complexOrientationEvaluation at hnorm
        rw [complexOrientationCycle_eq_realOrientationCycle] at hnorm
        exact hnorm
      · exact realOrientationClass_evaluation b0 b0.orientation
    have hfiber : o.fiberClass x =
        realOrientationClass (complexBasisRealification b) (h.complexRealOrientation 1 hline x) :=
      geometricCohomologyOrientation_fiberClass 2 E (h.complexRealOrientation 1 hline)
        (h.complexRealOrientation_locally_compatible 1 hline) x (complexBasisRealification b)
    rw [hfiber, hclass]
    exact realOrientationClass_pullback b0 b0.orientation (complexBasisRealification b)
      (h.complexRealOrientation 1 hline x) eR hOrient
  have hT (x : X) : relativeSingularCohomologyPullback ℤ (bundleFiberInclusion 2 E x)
      (fun _ hv ↦ hv) 2 T = o.fiberClass x :=
    (existsUnique_cohomologyThomClass ℤ 2 E o).exists.choose_spec x
  have hU : I.inv T = complexLineThomClass E hline := by
    apply (existsUnique_complexLineThomClass E hline).unique
    · intro x e
      let d : E x ≃L[ℂ] ULift.{u} ℂ := e.trans ContinuousLinearEquiv.ulift.symm
      let j : C(ULift.{u} ℂ, E x) := ⟨d.symm, d.symm.continuous⟩
      have hj : Set.MapsTo j {z : ULift.{u} ℂ | z ≠ 0} {v : E x | v ≠ 0} :=
        fun _ hz hv ↦ hz (d.symm.injective (hv.trans d.symm.map_zero.symm))
      let i := bundleFiberInclusion 2 E x
      have hi : Set.MapsTo i {v : E x | v ≠ 0} A := fun _ hv ↦ hv
      have hsquare : relativeSingularCohomologyPullback ℤ (complexLineFiberMap E x e)
          ((hf.comp hi).comp hj) 2 = I.hom ≫
            relativeSingularCohomologyPullback ℤ i hi 2 ≫
              relativeSingularCohomologyPullback ℤ j hj 2 := by
        change relativeSingularCohomologyPullback ℤ ((f.comp i).comp j) _ 2 = _
        rw [relativeSingularCohomologyPullback_comp ℤ j (f.comp i) hj (hf.comp hi) 2,
          relativeSingularCohomologyPullback_comp ℤ i f hi hf 2, Category.assoc]
        rfl
      rw [hsquare, ModuleCat.comp_apply, ModuleCat.comp_apply, I.inv_hom_id_apply]
      exact (congrArg (relativeSingularCohomologyPullback ℤ j hj 2) (hT x)).trans (ho x e)
    · exact (existsUnique_complexLineThomClass E hline).exists.choose_spec
  have hThom : relativeSingularCohomologyPullback ℤ f hf 2
      (complexLineThomClass E hline) = T := by
    rw [← hU]
    exact I.inv_hom_id_apply T
  -- Restriction to the same zero section gives equality of the original integral Euler classes.
  have hEuler : cohomologyEulerClass ℤ 2 E o = firstChernClass E hline := by
    have hforget := congrArg (fun a ↦ a (complexLineThomClass E hline))
      (relativeSingularCohomologyPullback_toOrdinary ℤ f hf 2)
    change relativeSingularCohomologyToOrdinary ℤ A 2
        (relativeSingularCohomologyPullback ℤ f hf 2 (complexLineThomClass E hline)) =
      singularCohomologyPullback ℤ f 2
        (relativeSingularCohomologyToOrdinary ℤ B 2 (complexLineThomClass E hline)) at hforget
    rw [hThom] at hforget
    unfold cohomologyEulerClass
    rw [hforget]
    change (singularCohomologyFunctor ℤ 2).map _
      ((singularCohomologyFunctor ℤ 2).map _ _) = _
    rw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl
  exact (cohomologyEulerClass_rationalization o).symm.trans
    (congrArg (singularCohomologyRationalization X 2) hEuler)

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
