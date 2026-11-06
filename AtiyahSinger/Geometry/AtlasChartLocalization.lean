/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.VariableRankDifferentialOperator
public import AtiyahSinger.Geometry.AtlasFrame
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Cutoff localization in a locally finite-rank bundle chart

Public module ID: M1088.

D05: transport a coordinate Schwartz operator to the actual sections of a
specified smooth bundle atlas. Each cutoff uses the rank of its own original
frame. Localization uses that frame; extension uses its inverse on the same
original fiber, with zero extension outside the chart and frame overlap.
No global constant rank, fiber norm, density or new total-space topology is used.

The smoothness, support and linearity properties are grouped implementation
certificates for these two concrete maps. The round trip multiplies by the
square of the cutoff. The maps are not unqualified inverses.

Sources: Spin Geometry III.2.2 and III.3.15, pp.171 and 186. The original
fixed-rank construction remains in ChartLocalization; this version retains
the locally varying ranks of SmoothComplexBundleAtlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)

/-- A compact coordinate cutoff using one chart of the specified original bundle atlas. -/
structure AtlasChartCutoff (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) where
  /-- The index of the original bundle frame used on both sides of localization. -/
  frameIndex : A.Index
  /-- The real cutoff on the manifold coordinate space. -/
  cutoff : EuclideanSpace ℝ (Fin n) → ℝ
  /-- The cutoff is real smooth. -/
  smooth_cutoff : ContDiff ℝ ∞ cutoff
  /-- Its topological support is compact in the coordinate space. -/
  compact_support : HasCompactSupport cutoff
  /-- Its support avoids the boundary of both the manifold chart and the original frame. -/
  support_subset : tsupport cutoff ⊆ c.target ∩ c.symm ⁻¹' (A.chart frameIndex).baseSet

namespace AtlasChartCutoff

variable {A} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (L : AtlasChartCutoff A c)

/-- The actual cutoff section coordinates, extended by zero outside the chart target. -/
def localizedFunction (u : A.smoothSections) (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin (A.rank L.frameIndex)) := by
  classical
  exact if z ∈ c.target then
    (L.cutoff z : ℂ) • atlasSectionInChart A c L.frameIndex u.val z
  else 0

/-- Cutoff extension through the inverse original frame, retaining the actual fiber vectors. -/
def extendedFunction
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex))))
    (x : M) : E x := by
  classical
  exact if hx : x ∈ c.source ∩ (A.chart L.frameIndex).baseSet then
    (L.cutoff (c x) : ℂ) • (A.frameLinearEquiv L.frameIndex x hx.2).symm
      ((EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ) (v (c x)))
  else 0

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]
  (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)

include hM hT hc

set_option linter.unusedSectionVars false in
/-- The grouped smoothness and support certificate for the concrete localization. -/
theorem localizedFunction_properties (u : A.smoothSections) :
    ContDiff ℝ ∞ (L.localizedFunction u) ∧
      tsupport (L.localizedFunction u) ⊆ tsupport L.cutoff ∧
        HasCompactSupport (L.localizedFunction u) := by
  /- Stage 1: every nonzero localized value has a nonzero cutoff.
  Taking closures puts the localized support inside the fixed
  closed compact cutoff support.
  Stage 2: on that support, subordination gives the coordinate and
  frame overlap. Compose the original section coordinates with the
  inverse smooth manifold chart and Euclidean coordinate equivalence,
  then multiply by the cutoff. Outside the closed support the formula
  is locally zero. These regions prove smoothness across the boundary
  without requiring a common rank for different atlas charts. -/
  classical
  have hsupport : tsupport (L.localizedFunction u) ⊆ tsupport L.cutoff := by
    apply closure_minimal ?_ (isClosed_tsupport L.cutoff)
    intro z hz
    by_contra houtside
    have hzero := image_eq_zero_of_notMem_tsupport houtside
    exact hz (by simp [localizedFunction, hzero])
  refine ⟨?_, hsupport,
    L.compact_support.of_isClosed_subset (isClosed_tsupport _) hsupport⟩
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ tsupport L.cutoff
  · -- In the cutoff support, use the given section coordinates and the actual inverse chart.
    have hzchart := (L.support_subset hz).1
    have hzframe := (L.support_subset hz).2
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) hzchart
    have hsection := (u.property L.frameIndex).contMDiffAt
      ((A.chart L.frameIndex).open_baseSet.mem_nhds hzframe)
    let e := EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ
    have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp z
      (hsection.comp z hchart)
    have hlocal := (Complex.ofRealCLM.contDiff.comp L.smooth_cutoff).contDiffAt.smul
      hcoords.contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds hzchart] with y hy
    simp [localizedFunction, atlasSectionInChart, hy, e]
  · -- Outside the closed cutoff support the specified zero-extension formula is locally zero.
    apply (contDiffAt_const
      (c := (0 : EuclideanSpace ℂ (Fin (A.rank L.frameIndex))))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport L.cutoff).isOpen_compl.mem_nhds hz] with y hy
    have hzero := image_eq_zero_of_notMem_tsupport hy
    simp [localizedFunction, hzero]

/-- The grouped smoothness and fixed support certificate for inverse-frame extension. -/
theorem extendedFunction_properties
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex)))) :
    A.IsSmoothSection (L.extendedFunction v) ∧
      ∀ x : M, x ∉ c.symm '' tsupport L.cutoff → L.extendedFunction v x = 0 := by
  /- Stage 1: in the chart/frame overlap, express the inverse-frame vector
  in any original atlas frame. This gives its smooth transition matrix
  applied to cutoff(c x) v(c x). The same finite coordinate equivalence
  changes only the model, and never changes the original vector in E x.
  Stage 2: outside the inverse image of the cutoff support the extension
  vanishes. That image is compact by subordination and continuity of c.symm,
  and hence closed by Hausdorffness. Thus the extension is locally zero
  outside it, including across both chart boundaries. Glue the smooth
  overlap and zero region. The two branches also give the stated vanishing. -/
  classical
  have hvanish (x : M) (hx : x ∉ c.symm '' tsupport L.cutoff) :
      L.extendedFunction v x = 0 := by
    by_cases hvalid : x ∈ c.source ∩ (A.chart L.frameIndex).baseSet
    · have hcut : c x ∉ tsupport L.cutoff := by
        intro hcut
        exact hx ⟨c x, hcut, c.left_inv hvalid.1⟩
      simp [extendedFunction, hvalid, image_eq_zero_of_notMem_tsupport hcut]
    · simp [extendedFunction, hvalid]
  refine ⟨?_, hvanish⟩
  have hcompact : IsCompact (c.symm '' tsupport L.cutoff) :=
    L.compact_support.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ (L.support_subset hz).1))
  intro j x hxj
  by_cases hx : x ∈ c.symm '' tsupport L.cutoff
  · obtain ⟨z, hz, rfl⟩ := hx
    have hzchart := (L.support_subset hz).1
    have hxsource := c.map_target hzchart
    have hxframe := (L.support_subset hz).2
    have hchart := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) hxsource
    -- Recover every output coordinate by the original smooth transition columns.
    let e := EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ
    have hvector := (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contMDiffAt
      ((v.smooth ⊤).comp_contMDiffAt hchart)
    have hcutoff :=
      (Complex.ofRealCLM.contDiff.comp L.smooth_cutoff).comp_contMDiffAt hchart
    have hsum : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun y ↦ ∑ k : Fin (A.rank L.frameIndex),
          ((EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ) (v (c y))) k •
            (A.chart j ((A.chart L.frameIndex).toPartialEquiv.symm
              (y, Pi.single k 1))).2) (c.symm z) := by
      apply contMDiffAt_finsetSum
      intro k _
      have hcoeff := contMDiffAt_pi_space.mp hvector k
      have hcolumn := (A.contMDiffOn_coordChange L.frameIndex j k).contMDiffAt
        (((A.chart L.frameIndex).open_baseSet.inter
          (A.chart j).open_baseSet).mem_nhds ⟨hxframe, hxj⟩)
      have hmul : ContDiff ℝ ∞
          (fun p : ℂ × (Fin (A.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
      exact hmul.comp_contMDiffAt (hcoeff.prodMk_space hcolumn)
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × (Fin (A.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
    have hlocal := hmul.comp_contMDiffAt (hcutoff.prodMk_space hsum)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [c.open_source.mem_nhds hxsource,
      (A.chart L.frameIndex).open_baseSet.mem_nhds hxframe,
      (A.chart j).open_baseSet.mem_nhds hxj] with y hyc hyi hyj
    simp only [extendedFunction,
      dite_eq_left (show y ∈ c.source ∩ (A.chart L.frameIndex).baseSet from ⟨hyc, hyi⟩)]
    rw [(A.linear j y hyj).map_smul]
    congr 1
    let T := (A.frameLinearEquiv j y hyj).toLinearMap.comp
      (A.frameLinearEquiv L.frameIndex y hyi).symm.toLinearMap
    have hexpand := congrArg T ((Pi.basisFun ℂ (Fin (A.rank L.frameIndex))).sum_repr
      ((EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ) (v (c y))))
    simp [T, map_sum, map_smul] at hexpand
    have hcolumn (k : Fin (A.rank L.frameIndex)) :
        (A.frameLinearEquiv j y hyj)
            ((A.frameLinearEquiv L.frameIndex y hyi).symm (Pi.single k 1)) =
          (A.chart j ((A.chart L.frameIndex).toPartialEquiv.symm (y, Pi.single k 1))).2 := by
      change (A.chart j ⟨y, cast (congrArg E
        ((A.chart L.frameIndex).proj_symm_apply' hyi))
          ((A.chart L.frameIndex).toOpenPartialHomeomorph.symm (y, Pi.single k 1)).2⟩).2 = _
      have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
        ((A.chart L.frameIndex).proj_symm_apply' (x := Pi.single k 1) hyi)
        ((A.chart L.frameIndex).toOpenPartialHomeomorph.symm (y, Pi.single k 1)).2
      exact congrArg (fun p : TotalSpace Unit E ↦ (A.chart j p).2) hpoint
    simp only [hcolumn] at hexpand
    change (A.frameLinearEquiv j y hyj)
      ((A.frameLinearEquiv L.frameIndex y hyi).symm
        ((EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ) (v (c y)))) = _
    exact hexpand.symm
  · -- The compact inverse-chart image is closed, so extension is locally zero off it.
    have hzero : ∀ᶠ y in 𝓝 x, (A.chart j ⟨y, L.extendedFunction v y⟩).2 = 0 := by
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hx,
        (A.chart j).open_baseSet.mem_nhds hxj] with y hy hyj
      rw [hvanish y hy]
      exact (A.linear j y hyj).map_zero
    exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt

/-- The actual compactly supported Schwartz localization. -/
def localize (u : A.smoothSections) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex))) :=
  (L.localizedFunction_properties hc u).2.2.toSchwartzMap
    (L.localizedFunction_properties hc u).1

/-- The actual smooth section obtained by the specified inverse-frame extension. -/
def extend
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex)))) :
    A.smoothSections :=
  ⟨L.extendedFunction v, (L.extendedFunction_properties hc v).1⟩

/-- The grouped linearity certificate for the two concrete cutoff maps. -/
theorem isLinearMap_localize_extend :
    IsLinearMap ℂ (L.localize hc) ∧ IsLinearMap ℂ (L.extend hc) := by
  /- For localization, evaluate pointwise on the cutoff support. The inverse
  chart point then lies in the original frame base set, so A.linear gives
  addition and scalar multiplication. Off this support all terms vanish.
  For extension, the selected inverse frame is complex linear on each
  valid fiber; the other branch is zero. Commute the cutoff scalar with
  the constant complex scalar. Extensionality of Schwartz functions and
  of the actual section subtype supplies the four linear-map fields. -/
  classical
  constructor
  · constructor
    · intro u v
      apply DFunLike.ext
      intro z
      change L.localizedFunction (u + v) z = L.localizedFunction u z + L.localizedFunction v z
      by_cases hz : z ∈ tsupport L.cutoff
      · have hzchart := (L.support_subset hz).1
        have hzframe := (L.support_subset hz).2
        simp only [localizedFunction, ite_eq_left hzchart, atlasSectionInChart,
          Submodule.coe_add, Pi.add_apply]
        rw [(A.linear L.frameIndex (c.symm z) hzframe).map_add]
        simp only [map_add, smul_add]
      · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]
    · intro a u
      apply DFunLike.ext
      intro z
      change L.localizedFunction (a • u) z = a • L.localizedFunction u z
      by_cases hz : z ∈ tsupport L.cutoff
      · have hzchart := (L.support_subset hz).1
        have hzframe := (L.support_subset hz).2
        simp only [localizedFunction, ite_eq_left hzchart, atlasSectionInChart,
          Submodule.coe_smul, Pi.smul_apply]
        rw [(A.linear L.frameIndex (c.symm z) hzframe).map_smul]
        simp only [map_smul, smul_comm (L.cutoff z : ℂ) a]
      · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  · constructor
    · intro u v
      apply Subtype.ext
      funext x
      change L.extendedFunction (u + v) x = L.extendedFunction u x + L.extendedFunction v x
      by_cases hx : x ∈ c.source ∩ (A.chart L.frameIndex).baseSet
      · simp [extendedFunction, hx, map_add, smul_add]
      · simp [extendedFunction, hx]
    · intro a v
      apply Subtype.ext
      funext x
      change L.extendedFunction (a • v) x = a • L.extendedFunction v x
      by_cases hx : x ∈ c.source ∩ (A.chart L.frameIndex).baseSet
      · simp [extendedFunction, hx, map_smul, smul_comm (L.cutoff (c x) : ℂ) a]
      · simp [extendedFunction, hx]

/-- Localization as the complex-linear map with the displayed coordinate formula. -/
def localizeLinearMap : A.smoothSections →ₗ[ℂ]
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex))) :=
  IsLinearMap.mk' (L.localize hc) (L.isLinearMap_localize_extend hc).1

/-- Extension as the complex-linear map into the original smooth sections. -/
def extendLinearMap :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex))) →ₗ[ℂ]
      A.smoothSections :=
  IsLinearMap.mk' (L.extend hc) (L.isLinearMap_localize_extend hc).2

/-- The round trip is multiplication by cutoff squared, including outside the chart. -/
theorem localize_extend_apply
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex))))
    (z : EuclideanSpace ℝ (Fin n)) :
    L.localize hc (L.extend hc v) z = (L.cutoff z : ℂ) ^ 2 • v z := by
  /- On the cutoff support, subordination makes both manifold charts and
  the original frame and its linear inverse cancel. Each of the two maps
  contributes the same cutoff factor. Off that support the cutoff is zero
  and localization vanishes, including outside the chart target. The argument
  includes rank zero and does not insert an identity term at zero fibers. -/
  classical
  by_cases hz : z ∈ tsupport L.cutoff
  · have hzchart := (L.support_subset hz).1
    have hzframe := (L.support_subset hz).2
    have hxsource := c.map_target hzchart
    have hforward := c.right_inv hzchart
    have hvalid : c.symm z ∈ c.source ∩ (A.chart L.frameIndex).baseSet := ⟨hxsource, hzframe⟩
    change L.localizedFunction (L.extend hc v) z = _
    simp only [localizedFunction, ite_eq_left hzchart, atlasSectionInChart, extend,
      extendedFunction, dite_eq_left hvalid, hforward]
    have hlinear := (A.linear L.frameIndex (c.symm z) hzframe).map_smul
      (L.cutoff z : ℂ)
      ((A.frameLinearEquiv L.frameIndex (c.symm z) hzframe).symm
        ((EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ) (v z)))
    rw [hlinear]
    change (L.cutoff z : ℂ) • (EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ).symm
      ((L.cutoff z : ℂ) •
        (A.frameLinearEquiv L.frameIndex (c.symm z) hzframe)
          ((A.frameLinearEquiv L.frameIndex (c.symm z) hzframe).symm
            ((EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ) (v z)))) = _
    simp only [LinearEquiv.apply_symm_apply, map_smul,
      ContinuousLinearEquiv.symm_apply_apply, smul_smul, pow_two]
  · have hzero := image_eq_zero_of_notMem_tsupport hz
    change L.localizedFunction (L.extend hc v) z = _
    simp [localizedFunction, hzero]

end AtlasChartCutoff

end AtiyahSinger
