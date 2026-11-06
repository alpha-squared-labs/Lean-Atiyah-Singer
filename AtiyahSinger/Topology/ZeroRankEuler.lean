/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ZeroRankBundle
public import AtiyahSinger.Topology.CohomologyRationalization
public import AtiyahSinger.Topology.GeometricCohomologyOrientation
public import AtiyahSinger.Topology.TrivialCohomologyThom

/-!
# The normalized Euler class of the original rank-zero real bundle

Public module ID: M2275.

The actual empty basis in each native fiber gives its canonical orientation.
The existing geometric normalization then gives an integral cohomological
orientation, and the existing integral Thom class and original zero section
define its Euler class. Rational coefficient change gives the degree-zero
unit, as a theorem about these same constructions rather than a definition.

This is the rank-zero supplement to the geometric normalization and Euler
construction in Milnor--Stasheff, Characteristic Classes, section 9,
pp.96--98. The source's bundle setup has positive rank. The supplement uses
the pair (point,empty), the signed-point normalization already implemented
in RealOrientationClass, and the original projection/zero-section
homeomorphism in ZeroRankBundle. The coefficient map is the ordinary one
from Hatcher, Algebraic Topology, sections 3.1--3.2.

Native zero-dimensional Orientation also has a negative sign. This module
uses the orientation of the actual empty basis, so the signed point has
coefficient +1. It does not assert Euler = 1 for an arbitrary cohomological
orientation or for the negative native orientation. No base nonemptiness,
compactness, separation, metric, manifold, or rank-zero spin structure is
assumed. The proof retains this canonical sign and the original fiber normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory HomologicalComplex Opposite
open scoped Simplicial

universe u

variable {B : Type u} [TopologicalSpace B]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]

/-- The canonical orientation of the actual empty basis in each original rank-zero fiber. -/
def zeroRankBundleOrientation : ∀ x : B, Orientation ℝ (E x) (Fin 0) :=
  fun x ↦
    let b : Module.Basis (Fin 0) ℝ (E x) := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.map
      (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin 0)) E x).symm.toLinearEquiv
    b.orientation

/-- Canonical empty bases satisfy the positive local-frame condition on the original bundle. -/
theorem isLocallyCompatibleBundleOrientation_zeroRank :
    IsLocallyCompatibleBundleOrientation 0 E (zeroRankBundleOrientation E) := by
  /- Stage 1: over the open set consisting of the entire base, pull the
  standard empty Euclidean basis back by the same native chart equivalence
  used to define zeroRankBundleOrientation. Its orientation is the prescribed
  one by construction; every actual fiber is zero-dimensional.
  Stage 2: continuity is required for each column indexed by Fin 0. There
  are no columns, so this condition is vacuous. This does not infer continuity
  of arbitrary chart choices. The family therefore witnesses precisely the
  existing local positive-frame predicate for the original total topology. -/

  intro x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, ?_⟩
  let b : ∀ y : (Set.univ : Set B), Module.Basis (Fin 0) ℝ (E y.val) := fun y ↦
    (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.map
      (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin 0)) E y.val).symm.toLinearEquiv
  refine ⟨b, ?_, ?_⟩
  · intro y
    rfl
  · -- There are no frame columns, so no continuity of the chosen charts is needed.
    intro j
    exact Fin.elim0 j

/-- The integral cohomological orientation normalized by the original canonical empty bases. -/
def zeroRankIntegralCohomologyOrientation : CohomologyOrientation ℤ 0 E :=
  geometricCohomologyOrientation 0 E (zeroRankBundleOrientation E)
    (isLocallyCompatibleBundleOrientation_zeroRank E)

/-- The rational Euler class obtained from the actual normalized integral Thom class. -/
def zeroRankRationalEulerClass : singularCohomology ℚ B 0 :=
  singularCohomologyRationalization B 0
    (cohomologyEulerClass ℤ 0 E (zeroRankIntegralCohomologyOrientation E))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonically normalized rank-zero Euler class is the actual degree-zero rational unit. -/
theorem zeroRankRationalEulerClass_eq_one :
    zeroRankRationalEulerClass E = singularCohomologyOne ℚ B := by
  /- Stage 1: the actual empty basis makes the punctured fiber empty, so the
  original relative chain projection and its cohomology comparison are isomorphisms.
  The inverse image of the ordinary unit evaluates to one on the same positive
  signed point: use naturality of the Kronecker pairing and literal evaluation of
  the original constant-one cocycle. The uniqueness defining realOrientationClass
  therefore identifies that unit with the prescribed geometric fiber orientation.
  Stage 2: at each base point the zero section factors through that same fiber.
  Naturality of the relative-to-ordinary map and the original Thom normalization
  identify the point pullback of the Euler class with the point unit. Detection of
  H⁰ by all point pullbacks gives the integral unit on the original base.
  Stage 3: ordinary coefficient change sends this same integral unit to the rational
  unit. This includes an empty base and makes no positive-rank or nonempty assumption. -/
  classical
  let o := zeroRankIntegralCohomologyOrientation E
  -- First identify the normalized positive empty-basis class on each actual fiber.
  have hfiber (x : B) :
      relativeSingularCohomologyToOrdinary ℤ (Set.ofPred (fun v : E x ↦ v ≠ 0)) 0 (o.fiberClass x) =
        singularCohomologyOne ℤ (E x) := by
    let V := E x
    let b : Module.Basis (Fin 0) ℝ V :=
      (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.map
        (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin 0)) E x).symm.toLinearEquiv
    let A : Set V := {v | v ≠ 0}
    let C := singularChains ℤ V
    let Q := relativeSingularChains ℤ A
    let prj := relativeSingularChainsProjection ℤ A
    let S := TopCat.toSSet.obj (TopCat.of V)
    let : IsEmpty A := ⟨fun v ↦ v.property
      (b.equivFun.injective (Subsingleton.elim _ _))⟩
    let : IsIso prj := isIso_relativeSingularChainsProjection_of_isEmpty ℤ A
    have : IsIso (relativeSingularCohomologyToOrdinary ℤ A 0) := by
      change IsIso (homologyMap ((singularCochainDualFunctor ℤ).map prj.op) 0)
      infer_instance
    let I := asIso (relativeSingularCohomologyToOrdinary ℤ A 0)
    let a := I.inv (singularCohomologyOne ℤ V)
    let z : (C.sc 0).moduleCatLeftHomologyData.K :=
      ⟨S.ιChainComplex (R := singularCoefficient ℤ) (realOrientationSimplex b) (ULift.up 1), by
        change C.dFrom 0 _ = 0
        simp⟩
    let zc : C.homology 0 :=
      (C.sc 0).moduleCatHomologyIso.inv ((C.sc 0).moduleCatLeftHomologyData.π z)
    have hcycle : homologyMap prj 0 zc = realOrientationCycle b b.orientation := by
      apply homologyMap_cycleClass ℤ C Q prj 0 z
        ⟨realOrientationRelativeChain b b.orientation,
          realOrientationRelativeChain_mem_cycles b b.orientation⟩
      simp only [realOrientationRelativeChain, ite_true]
      rfl
    have ha : realOrientationEvaluation b b.orientation a = 1 := by
      unfold realOrientationEvaluation
      rw [relativeSingularCapProduct_augmentation]
      change (singularCochainHomologyEvaluation ℤ Q 0 a
        (realOrientationCycle b b.orientation)).down = 1
      rw [← hcycle, singularCochainHomologyEvaluation_naturality]
      change (singularCochainHomologyEvaluation ℤ C 0 (I.hom (I.inv _)) zc).down = 1
      rw [Iso.inv_hom_id_apply]
      change (singularCochainHomologyEvaluation ℤ C 0
        (singularCocycleClass ℤ V 0 (singularCocycleOne ℤ V)) zc).down = 1
      have heval := singularCochainHomologyEvaluation_cycleClass ℤ C 0
        (singularCocycleOne ℤ V) z
      change singularCochainHomologyEvaluation ℤ C 0
        (singularCocycleClass ℤ V 0 (singularCocycleOne ℤ V)) zc = _ at heval
      rw [heval]
      change (singularCochainEquiv ℤ V 0 (singularCochainOne ℤ V)
        (realOrientationSimplex b)).down = 1
      rw [singularCochainOne, LinearEquiv.apply_symm_apply]
      rfl
    have heq : realOrientationClass b b.orientation = a :=
      (existsUnique_realOrientationClass b b.orientation).unique
        (realOrientationClass_evaluation b b.orientation) ha
    change I.hom (realOrientationClass b b.orientation) = singularCohomologyOne ℤ V
    rw [heq]
    exact I.inv_hom_id_apply _
  -- At each base point, zero-section pullback factors through the same fiber inclusion.

  have heuler : cohomologyEulerClass ℤ 0 E o = singularCohomologyOne ℤ B := by
    apply singularCohomology_zero_ext ℤ B
    intro x
    let j := bundleFiberInclusion 0 E x
    let z : C(PUnit.{u + 1}, E x) := ContinuousMap.const _ 0
    let f : C(PUnit.{u + 1}, B) := ContinuousMap.const _ x
    have hmaps : (bundleZeroSection 0 E).comp f = j.comp z := rfl
    have hcomp : singularCohomologyPullback ℤ (bundleZeroSection 0 E) 0 ≫
        singularCohomologyPullback ℤ f 0 =
      singularCohomologyPullback ℤ j 0 ≫ singularCohomologyPullback ℤ z 0 := by
      let F := singularCohomologyFunctor ℤ 0
      change F.map (TopCat.ofHom (bundleZeroSection 0 E)).op ≫ F.map (TopCat.ofHom f).op =
        F.map (TopCat.ofHom j).op ≫ F.map (TopCat.ofHom z).op
      rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
      exact congrArg (fun q ↦ F.map (TopCat.ofHom q).op) hmaps
    have hforget := relativeSingularCohomologyPullback_toOrdinary ℤ j
      (A := (Set.ofPred (fun v : E x ↦ v ≠ 0))) (B := bundleNonzero 0 E) (fun _ hv ↦ hv) 0
    have hthom : relativeSingularCohomologyPullback ℤ j
        (A := (Set.ofPred (fun v : E x ↦ v ≠ 0))) (B := bundleNonzero 0 E) (fun _ hv ↦ hv) 0
        (cohomologyThomClass ℤ 0 E o) = o.fiberClass x :=
      (existsUnique_cohomologyThomClass ℤ 0 E o).exists.choose_spec x
    change singularCohomologyPullback ℤ f 0
      (singularCohomologyPullback ℤ (bundleZeroSection 0 E) 0
        (relativeSingularCohomologyToOrdinary ℤ (bundleNonzero 0 E) 0
          (cohomologyThomClass ℤ 0 E o))) = _
    rw [← ModuleCat.comp_apply, hcomp, ModuleCat.comp_apply]
    have heq := congrArg (fun t ↦ t (cohomologyThomClass ℤ 0 E o)) hforget
    change relativeSingularCohomologyToOrdinary ℤ (Set.ofPred (fun v : E x ↦ v ≠ 0)) 0
      (relativeSingularCohomologyPullback ℤ j _ 0 (cohomologyThomClass ℤ 0 E o)) =
        singularCohomologyPullback ℤ j 0
          (relativeSingularCohomologyToOrdinary ℤ (bundleNonzero 0 E) 0
            (cohomologyThomClass ℤ 0 E o)) at heq
    rw [← heq, hthom, hfiber, singularCohomologyPullback_one,
      singularCohomologyPullback_one]
  -- Ordinary coefficient change preserves this same integral unit.
  change singularCohomologyRationalization B 0 (cohomologyEulerClass ℤ 0 E o) = _
  rw [heuler, singularCohomologyRationalization_one]

end AtiyahSinger
