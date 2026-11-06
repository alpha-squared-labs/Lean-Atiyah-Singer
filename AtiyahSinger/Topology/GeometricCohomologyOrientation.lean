/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyEuler
public import AtiyahSinger.Topology.RealOrientationClass
public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import Mathlib.Topology.Instances.Matrix

/-!
# From positive local native frames to normalized cohomological orientation

Public module ID: M1862.

A locally compatible native real orientation has positive local bases whose
columns are continuous in the original total space. This standard geometric
condition implies local compatibility of the signed, simplex-normalized
integral fiber generators. The resulting CohomologyOrientation can be used
directly by the existing cohomologyThomClass and cohomologyEulerClass.
It does not assume a local cohomology class, global Thom class, Euler class,
or their desired comparison as part of the geometric orientation condition.

Sources: Milnor--Stasheff, Characteristic Classes, section 9, pp.96--97,
where positively oriented local frames give the local relative cohomology
generators; the Euler construction is section 9, p.98. The explicit bridge
to mathlib's Orientation and native vector-bundle topology is a project
supplement. No metric, paracompactness or compactness is required.

The native preferred chart at each individual fiber only selects coordinates;
its selection need not vary continuously. Basis independence identifies its
normalized class with the one from each genuine local positive frame. In rank
zero the positive-frame condition forces the canonical empty-basis orientation.
The fiber-class construction itself still supports either native sign in rank
zero. This distinction avoids asserting an impossible negative empty basis.
The proofs use a fixed native chart and a neighborhood on which the determinant
of the given frame remains positive. Fiber normalization and its naturality are
the imported real-orientation interfaces; the preferred charts need not vary continuously.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  (o : ∀ x : X, Orientation ℝ (E x) (Fin r))

/-- The native orientation admits positive bases with locally continuous original columns. -/
def IsLocallyCompatibleBundleOrientation : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ b : ∀ y : U, Module.Basis (Fin r) ℝ (E y.val),
      (∀ y : U, (b y).orientation = o y.val) ∧
      ∀ j : Fin r, Continuous (fun y : U ↦
        (⟨y.val, b y j⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E))

variable [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

/-- The integral orientation of each actual fiber, normalized by its given native orientation. -/
def geometricCohomologyFiberClass (x : X) :
    relativeSingularCohomology ℤ {v : E x | v ≠ 0} r :=
  realOrientationClass
    ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map
      (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin r)) E x).symm.toLinearEquiv)
    (o x)

/-- Every normalized geometric fiber class freely generates the original relative fiber group. -/
theorem geometricCohomologyFiberClass_is_generator (x : X) :
    Function.Bijective (fun a : ℤ ↦ a • geometricCohomologyFiberClass r E o x) := by
  /- Use the normalized generator theorem for the actual basis pulled back
  from the preferred native chart. This is a fiberwise argument and does not
  assert continuity of the preferred chart selection as x varies. -/
  exact realOrientationClass_is_generator _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Positive continuous local frames give common local extensions of the normalized classes. -/
theorem geometricCohomologyFiberClass_locally_compatible
    (ho : IsLocallyCompatibleBundleOrientation r E o) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : relativeSingularCohomology ℤ (bundleNonzeroOver r E U) r,
        ∀ (y : X) (hy : y ∈ U),
          relativeSingularCohomologyPullback ℤ (bundleFiberInclusionOver r E U y hy)
            (A := {v : E y | v ≠ 0}) (B := bundleNonzeroOver r E U)
            (fun _ hv ↦ hv) r c = geometricCohomologyFiberClass r E o y := by
  classical
  intro x
  obtain ⟨U, hU, hx, b, hb, hcont⟩ := ho x
  let F := EuclideanSpace ℝ (Fin r)
  let t := trivializationAt F E x
  let V := U ∩ t.baseSet
  have hV : IsOpen V := hU.inter t.open_baseSet
  have hxV : x ∈ V := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let j : V → U := fun y ↦ ⟨y.val, y.property.1⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let e₀ := t.continuousLinearEquivAt ℝ x hxV.2
  let e (y : V) : E y.val ≃L[ℝ] E x :=
    (t.continuousLinearEquivAt ℝ y.val y.property.2).trans e₀.symm
  let c (y : V) : Module.Basis (Fin r) ℝ (E x) := (b (j y)).map (e y).toLinearEquiv
  -- In one fixed native chart the given continuous frame has continuous columns.
  have hc (i : Fin r) : Continuous (fun y : V ↦ c y i) := by
    exact e₀.symm.continuous.comp
      (t.continuousOn.comp_continuous ((hcont i).comp hj)
        (fun y ↦ t.mem_source.mpr y.property.2)).snd
  let c₀ := c ⟨x, hxV⟩
  let D (y : V) : ℝ := c₀.det (c y)
  have hmat : Continuous (fun y : V ↦ c₀.toMatrix (c y)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    exact ((continuous_apply i).comp (continuous_equivFun_basis c₀)).comp (hc k)
  have hD : Continuous D := hmat.matrix_det
  -- Shrink until that determinant is positive. The same argument includes the empty basis.
  let W : Set X := Subtype.val '' {y : V | 0 < D y}
  have hW : IsOpen W := hV.isOpenMap_subtype_val _ (isOpen_lt continuous_const hD)
  have hxW : x ∈ W := by
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    change 0 < c₀.det c₀
    rw [Module.Basis.det_self]
    norm_num
  have hWV : W ⊆ V := by
    rintro y ⟨z, _, rfl⟩
    exact z.property
  let p : C(BundleTotalOver r E W, E x) :=
    ⟨fun z ↦ e₀.symm (t z.val).2, e₀.symm.continuous.comp
      (t.continuousOn.comp_continuous continuous_subtype_val
        (fun z ↦ t.mem_source.mpr (hWV z.property).2)).snd⟩
  have hp : Set.MapsTo p (bundleNonzeroOver r E W) {w : E x | w ≠ 0} := by
    intro z hz hzero
    let y : V := ⟨z.val.proj, hWV z.property⟩
    apply hz
    exact (e y).injective (hzero.trans (e y).map_zero.symm)
  let a := realOrientationClass c₀ c₀.orientation
  -- Pull back one fixed normalized model class through that actual native trivialization.
  refine ⟨W, hW, hxW, relativeSingularCohomologyPullback ℤ p hp r a, ?_⟩
  intro y hy
  let yV : V := ⟨y, hWV hy⟩
  have hpos : 0 < D yV := by
    obtain ⟨z, hz, heq⟩ := hy
    have hzy : z = yV := Subtype.ext heq
    exact hzy ▸ hz
  have hor : Orientation.map (Fin r) (e yV).toLinearEquiv (o y) = c₀.orientation := by
    have hcori : (c yV).orientation = c₀.orientation :=
      ((c₀.orientation_eq_iff_det_pos (c yV)).mpr hpos).symm
    simpa only [c, Module.Basis.orientation_map, hb] using hcori
  let i := bundleFiberInclusionOver r E W y hy
  have hi : Set.MapsTo i {v : E y | v ≠ 0} (bundleNonzeroOver r E W) := fun _ hv ↦ hv
  have hcomp := congrArg (fun f ↦ f a)
    (relativeSingularCohomologyPullback_comp ℤ i p hi hp r)
  change relativeSingularCohomologyPullback ℤ i hi r
    (relativeSingularCohomologyPullback ℤ p hp r a) = _
  refine hcomp.symm.trans ?_
  -- Naturality identifies the restriction with the specified orientation in this fiber.
  have hnatural := realOrientationClass_pullback (b (j yV)) (o y)
    c₀ c₀.orientation (e yV) hor
  exact hnatural.trans (realOrientationClass_basis_independent (b (j yV)) (o y) _)

/-- The integral cohomological orientation normalized by the original positive geometric frames. -/
def geometricCohomologyOrientation (ho : IsLocallyCompatibleBundleOrientation r E o) :
    CohomologyOrientation ℤ r E where
  fiberClass := geometricCohomologyFiberClass r E o
  is_generator := by
    -- The generic orientation field uses its module action; over Z it is the usual zsmul.
    intro x
    change Function.Bijective (fun a : ℤ ↦
      (relativeSingularCohomology ℤ {v : E x | v ≠ 0} r).isModule.smul a
        (geometricCohomologyFiberClass r E o x))
    simp_rw [int_smul_eq_zsmul]
    exact geometricCohomologyFiberClass_is_generator r E o x
  locally_compatible := geometricCohomologyFiberClass_locally_compatible r E o ho

/-- Any actual basis computes the same normalized fiber restriction of the geometric orientation. -/
theorem geometricCohomologyOrientation_fiberClass
    (ho : IsLocallyCompatibleBundleOrientation r E o) (x : X)
    (b : Module.Basis (Fin r) ℝ (E x)) :
    (geometricCohomologyOrientation r E o ho).fiberClass x = realOrientationClass b (o x) := by
  /- The left side is the specified native-chart normalization. Apply basis
  independence for the same native orientation to replace only those coordinates
  by b. The original fiber, relative complement and integral coefficients agree. -/
  exact realOrientationClass_basis_independent _ (o x) b

end AtiyahSinger
