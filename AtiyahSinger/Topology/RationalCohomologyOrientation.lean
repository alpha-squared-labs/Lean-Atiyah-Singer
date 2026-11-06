/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyEuler
public import AtiyahSinger.Topology.RelativeCohomologyRationalization
public import AtiyahSinger.Topology.RelativeEvaluationRationalization
public import AtiyahSinger.Topology.RealOrientationClass

/-!
# Rationalization of the original integral orientation and Thom construction

Public module ID: M2032.

The prescribed integral fiber classes are sent through the actual relative
coefficient map. They generate the rational fiber cohomology, and the same
coefficient map sends their original local extensions to rational extensions.
This constructs the rational cohomological orientation without choosing a
new generator or assuming a Thom-class comparison.

The original integral and rational Thom classes, Euler classes, Thom maps,
and relative fiber integrals then satisfy the displayed coefficient-change
identities. The inverse maps here are the existing relative cohomological
fiber integrals. No Poincare-duality Gysin or differential-form integration
identification is inferred from these commuting squares.

Sources: Milnor--Stasheff, Characteristic Classes, section 9, pp.96--98,
and Theorem 10.4 with its coefficient discussion, pp.110--111. The actual
coefficient map is the simplexwise map from Hatcher, Algebraic Topology,
sections 3.1--3.2. General integral cohomological orientations and rank zero
are project supplements to the geometric positive-rank presentation in MS.
The fiber calculation uses a finite-dimensional Euclidean pair. It does not
tensor an arbitrary integral cohomology isomorphism, and no rationalization
isomorphism or surjectivity for the base is claimed. In particular, the
commuting squares on integral inputs do not restrict later self-intersection
formulas to rational classes coming from integers.

The original bundle, total topology, nonzero complement, projection and
zero section are unchanged. No compactness, separation, metric, manifold,
connectedness or nonempty-base hypothesis is required. Coefficient-change
proofs use the specified Thom constructions; their existence is a separate dependency.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

universe u

variable {r : ℕ} {X : Type u} [TopologicalSpace X]
  {E : X → Type u} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [hV : VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation ℤ r E)

namespace CohomologyOrientation

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hV in
/-- The actual coefficient image of an integral fiber generator is a rational generator. -/
theorem rationalization_fiberClass_is_generator (x : X) :
    Function.Bijective (fun a : ℚ ↦ a •
      relativeSingularCohomologyRationalization {v : E x | v ≠ 0} r (o.fiberClass x)) := by
  /- Stage 1: the original native fiber chart identifies the rational local
  homology with Q. Below-dimension vanishing makes evaluation on its chosen
  generator a bijection from rational relative cohomology to Q; degree zero
  is handled by the same evaluation theorem's boundary case.
  Stage 2: the normalized geometric integral class and cycle evaluate to one.
  Compatibility of both actual coefficient maps makes that class's rational
  image nonzero. The supplied integral fiber class generates the integral
  group, so the geometric class is an integral multiple of it. Its rational
  image is consequently nonzero as well.
  Stage 3: every nonzero vector in this rational rank-one group generates it.
  The evaluation coordinate gives explicit injectivity and a scalar preimage,
  proving generation by the exact coefficient image of o.fiberClass.
  This finite-dimensional fiber argument makes no tensor-product comparison
  or cohomology finiteness assumption on the base. -/
  -- A native fiber chart supplies the original rational rank-one local homology group.
  let V := E x
  let A : Set V := {v | v ≠ 0}
  let b : Module.Basis (Fin r) ℝ V :=
    (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map
      (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin r)) E x).symm.toLinearEquiv
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let e : V ≃L[ℝ] (Fin r → ℝ) := b.equivFun.toContinuousLinearEquiv
  let f : C(V, ULift.{u} (Fin r → ℝ)) :=
    ⟨fun v ↦ ULift.up (e v), continuous_uliftUp.comp e.continuous⟩
  let g : C(ULift.{u} (Fin r → ℝ), V) :=
    ⟨fun y ↦ e.symm y.down, e.symm.continuous.comp continuous_uliftDown⟩
  have hf : Set.MapsTo f A {y | y ≠ 0} := by
    intro v hv h
    apply hv
    apply e.injective
    simpa [f] using congrArg ULift.down h
  have hg : Set.MapsTo g {y | y ≠ 0} A := by
    intro y hy h
    apply hy
    apply ULift.ext
    simpa [g] using congrArg e h
  let : CategoryTheory.IsIso (relativeSingularHomologyMap ℚ f hf r) :=
    isIso_relativeSingularHomologyMap_of_inverse ℚ f g hf hg
      (by apply ContinuousMap.ext; intro v; exact e.symm_apply_apply v)
      (by apply ContinuousMap.ext; intro y; exact congrArg ULift.up (e.apply_symm_apply y.down)) r
  let H : ℚ ≃ₗ[ℚ] relativeSingularHomology ℚ A r :=
    (euclideanLocalHomologyEquiv.{u} ℚ r).trans
      (CategoryTheory.asIso (relativeSingularHomologyMap ℚ f hf r)).symm.toLinearEquiv
  let D := singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ A) r
  let ev : relativeSingularCohomology ℚ A r →ₗ[ℚ] ℚ :=
    { toFun := fun a ↦ (D a (H 1)).down
      map_add' := by intros; simp [map_add]
      map_smul' := by intros; simp [map_smul] }
  have hprev : r = 0 ∨ Subsingleton (relativeSingularHomology ℚ A (r - 1)) := by
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr (subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv
        ℚ e (r - 1) (by omega))
  have hgen : Function.Bijective (fun a : ℚ ↦ a • H 1) := by
    have hfun : (fun a : ℚ ↦ a • H 1) = H := by
      funext a
      rw [← H.map_smul, smul_eq_mul, mul_one]
    rw [hfun]
    exact H.bijective
  have hev : Function.Bijective ev := by
    have h := relativeSingularCapProduct_augmentation_bijective_of_generator
      ℚ A r (H 1) hgen hprev
    convert h using 1
    funext a
    exact (congrArg ULift.down
      (relativeSingularCapProduct_augmentation ℚ A r a (H 1))).symm
  -- The integral normalization survives the actual coefficient maps, so its image is nonzero.
  let a₀ := realOrientationClass b b.orientation
  let z₀ := realOrientationCycle b b.orientation
  have hnorm : (singularCochainHomologyEvaluation ℤ
      (relativeSingularChains ℤ A) r a₀ z₀).down = 1 := by
    rw [← relativeSingularCapProduct_augmentation]
    exact realOrientationClass_evaluation b b.orientation
  have hnonzero : relativeSingularCohomologyRationalization A r a₀ ≠ 0 := by
    intro hzero
    have hpair := singularCochainHomologyEvaluation_rationalization A r a₀ z₀
    rw [hzero, map_zero, LinearMap.zero_apply, hnorm] at hpair
    norm_num at hpair
  have ho : relativeSingularCohomologyRationalization A r (o.fiberClass x) ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := (o.is_generator x).surjective a₀
    apply hnonzero
    have hk' : k • o.fiberClass x = a₀ :=
      (int_smul_eq_zsmul (relativeSingularCohomology ℤ A r).isModule
        k (o.fiberClass x)).symm.trans hk
    rw [← hk', map_zsmul, hzero]
    exact zsmul_zero _
  -- Every nonzero vector in this specified rational rank-one group is a generator.
  let a : relativeSingularCohomology ℚ A r :=
    relativeSingularCohomologyRationalization A r (o.fiberClass x)
  have ha : ev a ≠ 0 := fun h ↦ ho (hev.injective (h.trans (map_zero ev).symm))
  constructor
  · intro s t h
    have heq := congrArg ev h
    change ev (s • a) = ev (t • a) at heq
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at heq
    exact mul_right_cancel₀ ha heq
  · intro c
    refine ⟨ev c / ev a, hev.injective ?_⟩
    change ev ((ev c / ev a) • a) = ev c
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ ha]

/-- The rational orientation whose fiber classes are the actual images of the integral ones. -/
def rationalization : CohomologyOrientation ℚ r E where
  fiberClass x :=
    relativeSingularCohomologyRationalization {v : E x | v ≠ 0} r (o.fiberClass x)
  is_generator := rationalization_fiberClass_is_generator o
  locally_compatible := by
    -- Rationalize the same local extension on the original restricted total space.
    intro x
    rcases o.locally_compatible x with ⟨U, hU, hx, c, hc⟩
    refine ⟨U, hU, hx,
      relativeSingularCohomologyRationalization (bundleNonzeroOver r E U) r c, ?_⟩
    intro y hy
    -- Naturality uses exactly the original fiber inclusion and its nonzero-pair witness.
    have hNat := relativeSingularCohomologyRationalization_naturality
      (bundleFiberInclusionOver r E U y hy)
      (A := {v : E y | v ≠ 0}) (B := bundleNonzeroOver r E U) (fun _ hv ↦ hv) r c
    exact hNat.symm.trans
      (congrArg (relativeSingularCohomologyRationalization {v : E y | v ≠ 0} r) (hc y hy))

end CohomologyOrientation

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The integral Thom class maps to the Thom class of its rationalized orientation. -/
theorem cohomologyThomClass_rationalization :
    relativeSingularCohomologyRationalization (bundleNonzero r E) r
        (cohomologyThomClass ℤ r E o) =
      cohomologyThomClass ℚ r E o.rationalization := by
  /- Stage 1: pull the actual coefficient image of the integral Thom class
  back along each original fiber inclusion. Relative coefficient naturality
  and the integral Thom-class normalization give the coefficient image of
  o.fiberClass at that same point.
  Stage 2: these are exactly the fiber classes of o.rationalization. Apply
  uniqueness of the rational Thom class on the original total-space pair.
  No generator, orientation, base space or relative support is replaced. -/
  -- Compare restrictions along the same fiber inclusions and use the original uniqueness.
  apply (existsUnique_cohomologyThomClass ℚ r E o.rationalization).unique
  · intro x
    have hnat := relativeSingularCohomologyRationalization_naturality
      (bundleFiberInclusion r E x)
      (A := {v : E x | v ≠ 0}) (B := bundleNonzero r E) (fun _ hv ↦ hv) r
      (cohomologyThomClass ℤ r E o)
    exact hnat.symm.trans (congrArg
      (relativeSingularCohomologyRationalization {v : E x | v ≠ 0} r)
      ((existsUnique_cohomologyThomClass ℤ r E o).exists.choose_spec x))
  · exact (existsUnique_cohomologyThomClass ℚ r E o.rationalization).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Coefficient change preserves Euler classes for the same specified integral orientation. -/
theorem cohomologyEulerClass_rationalization :
    singularCohomologyRationalization X r (cohomologyEulerClass ℤ r E o) =
      cohomologyEulerClass ℚ r E o.rationalization := by
  /- Stage 1: expand both Euler constructions as the original zero-section
  pullback of the relative-to-ordinary image of the specified Thom class.
  Move coefficient change through this actual pullback and through the
  actual relative-to-ordinary comparison using their naturality identities.
  Stage 2: cohomologyThomClass_rationalization identifies the remaining
  relative class with the Thom class of o.rationalization. This retains
  the integral normalization rather than allowing rational-unit rescaling. -/
  -- Naturality preserves the actual zero section and the relative-to-ordinary comparison.
  unfold cohomologyEulerClass
  rw [singularCohomologyRationalization_naturality,
    relativeSingularCohomologyRationalization_toOrdinary, cohomologyThomClass_rationalization]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original integral and rational Thom maps commute with actual coefficient change. -/
theorem cohomologyThomMap_rationalization (p : ℕ) (a : singularCohomology ℤ X p) :
    relativeSingularCohomologyRationalization (bundleNonzero r E) (p + r)
        (cohomologyThomMap ℤ r E o p a) =
      cohomologyThomMap ℚ r E o.rationalization p
        (singularCohomologyRationalization X p a) := by
  /- Stage 1: the integral Thom map is the actual ordered action pi-star(a)
  cup U. The relative coefficient-action identity sends it to the action
  of the rationalized first factor on the rationalized second factor.
  Stage 2: ordinary coefficient naturality identifies the first factor
  with pi-star of the rationalized input. The Thom-class comparison
  identifies the second with the same rational orientation's Thom class.
  The factor order and degree p+r are unchanged; there is no graded sign. -/
  -- Coefficient change preserves the ordered action, with the Thom factor on the right.
  change relativeSingularCohomologyRationalization (bundleNonzero r E) (p + r)
      (relativeSingularCohomologyAction ℤ (bundleNonzero r E) p r
        (singularCohomologyPullback ℤ (bundleProjection r E) p a)
        (cohomologyThomClass ℤ r E o)) =
    relativeSingularCohomologyAction ℚ (bundleNonzero r E) p r
      (singularCohomologyPullback ℚ (bundleProjection r E) p
        (singularCohomologyRationalization X p a))
      (cohomologyThomClass ℚ r E o.rationalization)
  rw [relativeSingularCohomologyRationalization_action,
    singularCohomologyRationalization_naturality, cohomologyThomClass_rationalization]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified relative inverse Thom maps commute with the same coefficient maps. -/
theorem cohomologyFiberIntegral_rationalization (p : ℕ)
    (b : relativeSingularCohomology ℤ (bundleNonzero r E) (p + r)) :
    singularCohomologyRationalization X p (cohomologyFiberIntegral ℤ r E o p b) =
      cohomologyFiberIntegral ℚ r E o.rationalization p
        (relativeSingularCohomologyRationalization (bundleNonzero r E) (p + r) b) := by
  /- Stage 1: write b as the integral Thom image of its integral inverse
  image, using the existing equivalence on these very relative groups.
  The Thom-map coefficient identity then sends b to the rational Thom
  image of the rationalized integral inverse image.
  Stage 2: apply the inverse of that same rational Thom equivalence and
  its inverse identity. This yields the asserted relative cohomological
  fiber-integral square. It proves neither a Poincare-duality comparison
  nor equality with integration of differential forms, and does not assert
  that every rational relative class comes from an integral class. -/
  -- Apply the same rational Thom equivalence; both sides then reduce to coefficient change of b.
  apply (cohomologyThomEquiv ℚ r E o.rationalization p).injective
  have hZ := (cohomologyThomEquiv ℤ r E o p).apply_symm_apply b
  have hQ := (cohomologyThomEquiv ℚ r E o.rationalization p).apply_symm_apply
    (relativeSingularCohomologyRationalization (bundleNonzero r E) (p + r) b)
  change cohomologyThomMap ℤ r E o p (cohomologyFiberIntegral ℤ r E o p b) = b at hZ
  change cohomologyThomMap ℚ r E o.rationalization p
    (cohomologyFiberIntegral ℚ r E o.rationalization p
      (relativeSingularCohomologyRationalization (bundleNonzero r E) (p + r) b)) =
    relativeSingularCohomologyRationalization (bundleNonzero r E) (p + r) b at hQ
  change cohomologyThomMap ℚ r E o.rationalization p _ =
    cohomologyThomMap ℚ r E o.rationalization p _
  rw [hQ, ← cohomologyThomMap_rationalization, hZ]

end AtiyahSinger
