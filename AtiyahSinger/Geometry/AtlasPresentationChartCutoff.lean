/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundlePresentation
public import AtiyahSinger.Geometry.AtlasChartLocalization

/-!
# Coordinate cutoffs of an original finite atlas presentation

Public module ID: M1101.

Each original partition function gives an actual compact coordinate cutoff in
the same manifold chart and original bundle frame. Pulling this cutoff back
and extending by zero recovers the original partition function exactly.

This preserves the original finite partition when constructing localized
product operators; no new cover, frame or partition is substituted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] {A : SmoothComplexBundleAtlas (n := n) E}

namespace AtlasBundlePresentation

/-- The original partition weight expressed in its own original coordinate and bundle chart. -/
def chartCutoff (L : AtlasBundlePresentation A) (j : Fin L.size) :
    AtlasChartCutoff A (L.chart j) := by
  classical
  let c := L.chart j
  let K := c '' tsupport (L.cutoff j)
  let χ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z ↦ if z ∈ c.target then L.cutoff j (c.symm z) else 0
  have hK : IsCompact K := (L.compact_support j).image_of_continuousOn
    (c.continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  have hKsub : K ⊆ c.target ∩ c.symm ⁻¹' (A.chart (L.frameIndex j)).baseSet := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs := (L.support_subset j hx).1
    refine ⟨c.map_source hxs, ?_⟩
    change c.symm (c x) ∈ (A.chart (L.frameIndex j)).baseSet
    rw [c.left_inv hxs]
    exact (L.support_subset j hx).2
  have hs : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hzt : z ∈ c.target := by
      by_contra h
      exact hz (ite_eq_right h)
    have hx : c.symm z ∈ tsupport (L.cutoff j) := by
      apply subset_tsupport
      intro hzero
      exact hz (by simp only [χ, ite_eq_left hzt, hzero])
    exact ⟨c.symm z, hx, c.right_inv hzt⟩
  refine {
    frameIndex := L.frameIndex j
    cutoff := χ
    compact_support := hK.of_isClosed_subset (isClosed_tsupport χ) hs
    support_subset := hs.trans hKsub
    smooth_cutoff := ?_ }
  -- The original compact support avoids both chart boundaries.
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ K
  · have hzt := (hKsub hz).1
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (L.chart_mem_atlas j)) hzt
    have hlocal := ((L.smooth_cutoff j).contMDiffAt.comp z hchart).contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds hzt] with y hy
    exact ite_eq_left hy
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hs h))

include hM hT in
-- These instances construct chartCutoff; the pullback identity only reads its cutoff field.
set_option linter.unusedSectionVars false in
open Classical in
/-- Pullback and zero extension recover precisely the original finite partition weight. -/
theorem chartCutoff_pullback (L : AtlasBundlePresentation A) (j : Fin L.size) (x : M) :
    (if x ∈ (L.chart j).source then (L.chartCutoff j).cutoff (L.chart j x) else 0) =
      L.cutoff j x := by
  classical
  by_cases hx : x ∈ (L.chart j).source
  · change (if x ∈ (L.chart j).source then
      (if L.chart j x ∈ (L.chart j).target then
        L.cutoff j ((L.chart j).symm (L.chart j x)) else 0) else 0) = L.cutoff j x
    rw [ite_eq_left hx, ite_eq_left ((L.chart j).map_source hx), (L.chart j).left_inv hx]
  · rw [ite_eq_right hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h ↦ hx (L.support_subset j h).1)).symm

end AtlasBundlePresentation

end AtiyahSinger
