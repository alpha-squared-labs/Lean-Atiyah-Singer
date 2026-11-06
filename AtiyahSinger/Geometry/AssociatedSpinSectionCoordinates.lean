/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.SmoothAtlasSections
public import AtiyahSinger.Geometry.SmoothSpinorBundle

/-!
# Section coordinates in the original unit-section spin frames

Public module ID: M1083.

The original associated representative equivalence gives a model-valued section
on each supplied principal chart, with zero values outside that chart. A smooth
section of a compatible associated atlas has smooth model coordinates on that
original domain. The coordinate choice is shared by connection descent and
Clifford compatibility.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

set_option maxSynthPendingDepth 50

variable {n m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : ContRepresentation ℂ (spinGroup (realSpinorQuadraticForm m)) W)
  (A : SmoothSpinPrincipalAtlas m 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) projection)
  (H : SmoothComplexBundleAtlas (n := n) (AssociatedVectorFiber hP ρ))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin n)

/-- Coordinates in the original unit-section associated frame, zero outside its domain. -/
def associatedSpinSectionCoordinates (b : M) (σ : ∀ x : M, AssociatedVectorFiber hP ρ x)
    (x : M) : W := by
  classical
  exact if hx : x ∈ (A.trivialization b).baseSet then
    (associatedVectorFiberMkLinearEquiv hP ρ
      ((A.trivialization b).toPartialEquiv.symm (x, 1))
      ((A.trivialization b).proj_symm_apply' hx)).symm (σ x) else 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [IsManifold I ∞ M] [FiniteDimensional ℂ W] in
/-- Smooth sections have smooth coordinates in every one of the same principal charts. -/
theorem contMDiffOn_associatedSpinSectionCoordinates (hH : A.IsAssociatedVectorAtlas hP ρ H)
    (b : M) (u : H.smoothSections) :
    ContMDiffOn I 𝓘(ℝ, W) ∞ (associatedSpinSectionCoordinates hP ρ A b u.val)
      (A.trivialization b).baseSet := by
  classical
  obtain ⟨j, c, hbase, hchart⟩ := hH b
  have hcoord (y : M) (hy : y ∈ (A.trivialization b).baseSet) :
      c (associatedSpinSectionCoordinates hP ρ A b u.val y) =
        (H.chart j ⟨y, u.val y⟩).2 := by
    let E := associatedVectorFiberMkLinearEquiv hP ρ
      ((A.trivialization b).toPartialEquiv.symm (y, 1))
      ((A.trivialization b).proj_symm_apply' hy)
    have h := hchart ((A.trivialization b).toPartialEquiv.symm (y, 1)) y
      ((A.trivialization b).proj_symm_apply' hy) hy (E.symm (u.val y))
    change (H.chart j ⟨y, E (E.symm (u.val y))⟩).2 = _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    have hunit : (A.trivialization b) ((A.trivialization b).toPartialEquiv.symm (y, 1)) =
        (y, 1) := (A.trivialization b).apply_symm_apply' hy
    rw [hunit] at h
    simp only [map_one, one_apply_eq_self] at h
    simp only [associatedSpinSectionCoordinates, dite_eq_left hy]
    exact h.symm
  have hs := (c.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff
    |>.comp_contMDiffOn (u.property j)
  rw [hbase] at hs
  apply hs.congr
  intro y hy
  change associatedSpinSectionCoordinates hP ρ A b u.val y =
    c.symm (H.chart j ⟨y, u.val y⟩).2
  rw [← hcoord y hy, LinearEquiv.symm_apply_apply]

end AtiyahSinger
