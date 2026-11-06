/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinStructurePullback
public import AtiyahSinger.Topology.CohomologyThomNaturality
public import AtiyahSinger.Topology.SpinCohomologyOrientation

/-!
# Naturality of the original Euler class and its spin normalization

Public module ID: M2168.

An oriented bundle map preserves the Euler class defined by the original Thom
class and zero section. For the actual native pullback of a spin structure,
the specified geometric orientations give this compatibility without an extra
orientation-class input. Rationalization then preserves the same identity.

Source: Milnor--Stasheff, section 9, Euler naturality; Spin Geometry II.1 and
III.12 for the original spin orientation. No compactness or properness is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u v

section Oriented

variable (R : Type) [CommRing R] (r : ℕ)
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (F : Y → Type u) [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℝ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) F)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) F]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) F]
  (oE : CohomologyOrientation R r E) (oF : CohomologyOrientation R r F)
  (f : C(X, Y))
  (g : C(TotalSpace (EuclideanSpace ℝ (Fin r)) E,
    TotalSpace (EuclideanSpace ℝ (Fin r)) F))
  (hN : Set.MapsTo g (bundleNonzero r E) (bundleNonzero r F))
  (e : ∀ x, E x ≃L[ℝ] F (f x))
  (hg : ∀ x, g.comp (bundleFiberInclusion r E x) =
    (bundleFiberInclusion r F (f x)).comp ⟨e x, (e x).continuous⟩)
  (ho : ∀ x, relativeSingularCohomologyPullback R
    (⟨e x, (e x).continuous⟩ : C(E x, F (f x)))
      (show Set.MapsTo (e x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) r
      (oF.fiberClass (f x)) = oE.fiberClass x)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hN hg ho in
/-- An actual oriented bundle map preserves the original zero-section Euler class. -/
theorem cohomologyEulerClass_pullback :
    singularCohomologyPullback R f r (cohomologyEulerClass R r F oF) =
      cohomologyEulerClass R r E oE := by
  -- Fiber linearity identifies the two maps from the original zero section.
  have hzero : g.comp (bundleZeroSection r E) = (bundleZeroSection r F).comp f := by
    apply ContinuousMap.ext
    intro x
    have hx := congrArg (fun h ↦ h 0) (hg x)
    simpa only [ContinuousMap.comp_apply, bundleFiberInclusion, bundleZeroSection,
      ContinuousMap.coe_mk, zeroSection, map_zero] using hx
  have hpull (a : singularCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) F) r) :
      singularCohomologyPullback R f r
          (singularCohomologyPullback R (bundleZeroSection r F) r a) =
        singularCohomologyPullback R (bundleZeroSection r E) r
          (singularCohomologyPullback R g r a) := by
    have hmap : singularCohomologyPullback R (bundleZeroSection r F) r ≫
        singularCohomologyPullback R f r =
      singularCohomologyPullback R g r ≫
        singularCohomologyPullback R (bundleZeroSection r E) r := by
      change (singularCohomologyFunctor R r).map _ ≫
          (singularCohomologyFunctor R r).map _ =
        (singularCohomologyFunctor R r).map _ ≫ (singularCohomologyFunctor R r).map _
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      exact congrArg (fun h : C(_, _) ↦ singularCohomologyPullback R h r) hzero.symm
    exact congrArg (fun h ↦ h a) hmap
  -- Forgetting the relative condition commutes with the same oriented Thom pullback.
  have hthom := congrArg (fun h ↦ h (cohomologyThomClass R r F oF))
    (relativeSingularCohomologyPullback_toOrdinary R g hN r)
  simp only [ModuleCat.comp_apply] at hthom
  rw [cohomologyThomClass_pullback R r E F oE oF f g hN e hg ho] at hthom
  unfold cohomologyEulerClass
  rw [hpull, ← hthom]

end Oriented

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

variable {m : ℕ} {B X : Type u} {P : Type v} {E : B → Type u}
  [hnorm : ∀ b, NormedAddCommGroup (E b)] [hinnerSpace : ∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ b, Orientation ℝ (E b) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The Euler class normalized by the original spin lift is natural under its native pullback. -/
theorem TopologicalSpinStructure.rationalEulerClass_pullback
    (S : TopologicalSpinStructure m E o hm hP) (f : C(X, B)) :
    letI := hP
    letI : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hnorm (f x)
    letI : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hinnerSpace (f x)
    letI : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
    letI : FiberBundle RealModel ((f : X → B) *ᵖ E) :=
      FiberBundle.pullback (F := RealModel) (E := E) f
    letI : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toAddCommMonoid
    letI : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hinnerSpace (f x)).toModule
    letI : VectorBundle ℝ RealModel ((f : X → B) *ᵖ E) :=
      VectorBundle.pullback ℝ (F := RealModel) (E := E) f
    letI := isContinuousRiemannianBundle_pullback RealModel E f
    singularCohomologyPullback ℚ f (2 * m) S.rationalEulerClass =
      (S.pullback f).rationalEulerClass := by
  classical
  let := hP
  let : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
    fun x ↦ hnorm (f x)
  let : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
    fun x ↦ hinnerSpace (f x)
  let : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
  let : FiberBundle RealModel ((f : X → B) *ᵖ E) :=
    FiberBundle.pullback (F := RealModel) (E := E) f
  let : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hnorm (f x)).toAddCommMonoid
  let : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hinnerSpace (f x)).toModule
  let : VectorBundle ℝ RealModel ((f : X → B) *ᵖ E) :=
    VectorBundle.pullback ℝ (F := RealModel) (E := E) f
  let := isContinuousRiemannianBundle_pullback RealModel E f
  let E' := (f : X → B) *ᵖ E
  let g : C(TotalSpace RealModel E', TotalSpace RealModel E) :=
    ⟨Pullback.lift (f : X → B), Pullback.continuous_lift RealModel E f⟩
  let e (x : X) : E' x ≃L[ℝ] E (f x) := ContinuousLinearEquiv.refl ℝ (E (f x))
  have hN : Set.MapsTo g (bundleNonzero (2 * m) E') (bundleNonzero (2 * m) E) :=
    fun _ hv ↦ hv
  have hg (x : X) : g.comp (bundleFiberInclusion (2 * m) E' x) =
      (bundleFiberInclusion (2 * m) E (f x)).comp ⟨e x, (e x).continuous⟩ := rfl
  -- Both spin orientations use the same original oriented fiber and the same basis.
  have ho (x : X) : relativeSingularCohomologyPullback ℤ
      (⟨e x, (e x).continuous⟩ : C(E' x, E (f x)))
      (show Set.MapsTo (e x) {v : E' x | v ≠ 0} {v : E (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) (2 * m)
      (S.integralCohomologyOrientation.fiberClass (f x)) =
        (S.pullback f).integralCohomologyOrientation.fiberClass x := by
    let b : Module.Basis (Fin (2 * m)) ℝ (E (f x)) :=
      (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map
        (VectorBundle.continuousLinearEquivAt ℝ RealModel E (f x)).symm.toLinearEquiv
    unfold TopologicalSpinStructure.integralCohomologyOrientation
    rw [geometricCohomologyOrientation_fiberClass (2 * m) E o
      S.isLocallyCompatibleBundleOrientation (f x) b,
      geometricCohomologyOrientation_fiberClass (2 * m) E' (fun x ↦ o (f x))
        (S.pullback f).isLocallyCompatibleBundleOrientation x b]
    apply realOrientationClass_pullback b (o (f x)) b (o (f x)) (e x)
    change Orientation.map (Fin (2 * m)) (LinearEquiv.refl ℝ (E (f x))) (o (f x)) = _
    rw [Orientation.map_refl]
    rfl
  -- First pull back the integral zero-section class, then change coefficients.
  have hint := cohomologyEulerClass_pullback ℤ (2 * m) E' E
    (S.pullback f).integralCohomologyOrientation S.integralCohomologyOrientation
    f g hN e hg ho
  unfold TopologicalSpinStructure.rationalEulerClass
  rw [← singularCohomologyRationalization_naturality, hint]

end AtiyahSinger
