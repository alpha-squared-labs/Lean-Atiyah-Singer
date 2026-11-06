/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThom
public import AtiyahSinger.Topology.LocalHomologyLinearization
public import AtiyahSinger.Topology.RealOrientationGeneratorSign
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Integral fiber signs in one fixed native vector-bundle chart

Public module ID: M1109.

The given cohomological orientation assigns an integral unit to the positive
cycle of each native linear fiber coordinate system. Along a path staying in
one trivialization, the actual nonzero fiber inclusions are homotopic. Evaluation
of the same global relative Thom class therefore makes the sign constant.
Local Euclidean base charts provide the required path-connected neighborhoods.

Source: Milnor--Stasheff, Characteristic Classes, section 9, local constancy of
integral fiber orientations. The proof uses the already constructed relative
Thom class and does not assume a total-space homological orientation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory
open scoped unitInterval

variable (r : ℕ) {B : Type} [TopologicalSpace B]
  (E : B → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation ℤ r E)
  (t : Trivialization (EuclideanSpace ℝ (Fin r)) (π (EuclideanSpace ℝ (Fin r)) E))
  [t.IsLinear ℝ]

/-- The sign obtained by evaluating the specified fiber class on this native coordinate basis. -/
def bundleFiberChartSign (x : B) (hx : x ∈ t.baseSet) : ℤ :=
  let b := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map
    (t.continuousLinearEquivAt ℝ x hx).symm.toLinearEquiv
  realOrientationEvaluation b b.orientation (o.fiberClass x)

omit [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E] in
/-- A primitive integral fiber class gives a unit sign in any native linear chart. -/
theorem isUnit_bundleFiberChartSign (x : B) (hx : x ∈ t.baseSet) :
    IsUnit (bundleFiberChartSign r E o t x hx) := by
  apply isUnit_realOrientationEvaluation_of_generator
  have h := o.is_generator x
  change Function.Bijective (fun m : ℤ ↦
    (relativeSingularCohomology ℤ {v : E x | v ≠ 0} r).isModule.smul m (o.fiberClass x)) at h
  simp_rw [int_smul_eq_zsmul] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A path contained in one native trivialization preserves the specified integral fiber sign. -/
theorem bundleFiberChartSign_eq_of_path
    {x y : B} (hx : x ∈ t.baseSet) (hy : y ∈ t.baseSet)
    (γ : Path x y) (hγ : ∀ s, γ s ∈ t.baseSet) :
    bundleFiberChartSign r E o t x hx = bundleFiberChartSign r E o t y hy := by
  let F := EuclideanSpace ℝ (Fin r)
  let TE := TotalSpace F E
  let b := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
  let u := cohomologyThomClass ℤ r E o
  let j (z : B) (hz : z ∈ t.baseSet) : C(F, TE) :=
    (bundleFiberInclusion r E z).comp
      ⟨(t.continuousLinearEquivAt ℝ z hz).symm,
        (t.continuousLinearEquivAt ℝ z hz).symm.continuous⟩
  have hj (z : B) (hz : z ∈ t.baseSet) :
      Set.MapsTo (j z hz) {v : F | v ≠ 0} (bundleNonzero r E) := by
    intro v hv hzero
    exact hv ((t.continuousLinearEquivAt ℝ z hz).symm.injective
      (hzero.trans (t.continuousLinearEquivAt ℝ z hz).symm.map_zero.symm))
  let ev (z : relativeSingularHomology ℤ (bundleNonzero r E) r) : ℤ :=
    (singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ (bundleNonzero r E)) r
      u z).down
  -- Fiber normalization and the original pairing naturality read each sign on one global class.
  have hvalue (z : B) (hz : z ∈ t.baseSet) : bundleFiberChartSign r E o t z hz =
      ev (relativeSingularHomologyMap ℤ (j z hz) (hj z hz) r
        (realOrientationCycle b b.orientation)) := by
    let e := (t.continuousLinearEquivAt ℝ z hz).symm
    let q : C(F, E z) := ⟨e, e.continuous⟩
    have hq : Set.MapsTo q {v : F | v ≠ 0} {v : E z | v ≠ 0} :=
      fun _ hv heq ↦ hv (e.injective (heq.trans e.map_zero.symm))
    let i := bundleFiberInclusion r E z
    have hi : Set.MapsTo i {v : E z | v ≠ 0} (bundleNonzero r E) := fun _ hv ↦ hv
    have hu : relativeSingularCohomologyPullback ℤ i hi r u = o.fiberClass z :=
      (existsUnique_cohomologyThomClass ℤ r E o).exists.choose_spec z
    have hcoord : relativeSingularCohomologyPullback ℤ q hq r (o.fiberClass z) =
        relativeSingularCohomologyPullback ℤ (j z hz) (hj z hz) r u := by
      rw [← hu, ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    calc
      bundleFiberChartSign r E o t z hz = realOrientationEvaluation b b.orientation
          (relativeSingularCohomologyPullback ℤ q hq r (o.fiberClass z)) :=
        (realOrientationEvaluation_pullback b e (o.fiberClass z)).symm
      _ = realOrientationEvaluation b b.orientation
          (relativeSingularCohomologyPullback ℤ (j z hz) (hj z hz) r u) := by rw [hcoord]
      _ = ev (relativeSingularHomologyMap ℤ (j z hz) (hj z hz) r
          (realOrientationCycle b b.orientation)) := by
        unfold realOrientationEvaluation
        rw [relativeSingularCapProduct_augmentation]
        change (singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ {v : F | v ≠ 0}) r
          (HomologicalComplex.homologyMap ((singularCochainDualFunctor ℤ).map
            (relativeSingularChainsMap ℤ (j z hz) (hj z hz)).op) r u)
          (realOrientationCycle b b.orientation)).down = _
        rw [← singularCochainHomologyEvaluation_naturality]
        rfl
  -- The original inverse trivialization carries the path times each nonzero model vector.
  let H : (j x hx).Homotopy (j y hy) :=
    { toFun z := t.toOpenPartialHomeomorph.symm (γ z.1, z.2)
      continuous_toFun := t.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
        (fun z ↦ t.mem_target.mpr (hγ z.1))
      map_zero_left := by
        intro v
        change t.toOpenPartialHomeomorph.symm (γ 0, v) = j x hx v
        rw [γ.source]
        exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm x hx v
      map_one_left := by
        intro v
        change t.toOpenPartialHomeomorph.symm (γ 1, v) = j y hy v
        rw [γ.target]
        exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm y hy v }
  have hH (s : unitInterval) (v : F) (hv : v ≠ 0) : H (s, v) ∈ bundleNonzero r E := by
    change t.toOpenPartialHomeomorph.symm (γ s, v) ∈ bundleNonzero r E
    rw [t.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) (γ s) (hγ s) v]
    intro hzero
    exact hv ((t.continuousLinearEquivAt ℝ (γ s) (hγ s)).symm.injective
      (hzero.trans (t.continuousLinearEquivAt ℝ (γ s) (hγ s)).symm.map_zero.symm))
  have hmaps := relativeSingularHomologyMap_eq_of_homotopy ℤ (hj x hx) (hj y hy) H hH r
  rw [hvalue x hx, hvalue y hy, hmaps]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified integral fiber sign is locally constant inside a fixed Euclidean base chart
and a fixed native bundle trivialization. -/
theorem exists_locally_constant_bundleFiberChartSign
    {n : ℕ} (e : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (x : B) (he : x ∈ e.source) (ht : x ∈ t.baseSet) :
    ∃ U : Set B, IsOpen U ∧ x ∈ U ∧ ∃ hUt : U ⊆ t.baseSet,
      ∃ _hUe : U ⊆ e.source, ∀ y (hy : y ∈ U),
        bundleFiberChartSign r E o t y (hUt hy) = bundleFiberChartSign r E o t x ht := by
  let V := EuclideanSpace ℝ (Fin n)
  have hOpen : IsOpen (e '' (t.baseSet ∩ e.source)) :=
    e.isOpen_image_of_subset_source (t.open_baseSet.inter e.open_source) Set.inter_subset_right
  have hxImage : e x ∈ e '' (t.baseSet ∩ e.source) := ⟨x, ⟨ht, he⟩, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hOpen (e x) hxImage
  have htarget : Metric.ball (e x) δ ⊆ e.target := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hball hv
    exact e.map_source hy.2
  let U : Set B := e.symm '' Metric.ball (e x) δ
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball htarget
  have hxU : x ∈ U := ⟨e x, Metric.mem_ball_self hδ, e.left_inv he⟩
  have hsub : U ⊆ t.baseSet ∩ e.source := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨z, hz, hze⟩ := hball hv
    rw [← hze, e.left_inv hz.2]
    exact hz
  have hUt : U ⊆ t.baseSet := fun _ hy ↦ (hsub hy).1
  have hUe : U ⊆ e.source := fun _ hy ↦ (hsub hy).2
  have hpath : IsPathConnected U :=
    ((convex_ball (e x) δ).isPathConnected ⟨e x, Metric.mem_ball_self hδ⟩).image'
      (e.continuousOn_symm.mono htarget)
  refine ⟨U, hU, hxU, hUt, hUe, ?_⟩
  intro y hy
  obtain ⟨γ, hγ⟩ := hpath.joinedIn x hxU y hy
  exact (bundleFiberChartSign_eq_of_path r E o t ht (hUt hy) γ
    (fun s ↦ hUt (hγ s))).symm

end AtiyahSinger
