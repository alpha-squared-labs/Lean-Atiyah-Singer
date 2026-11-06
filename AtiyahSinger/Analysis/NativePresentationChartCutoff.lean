/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import AtiyahSinger.Geometry.AtlasPresentationChartCutoff
public import AtiyahSinger.Geometry.ChartLocalization

/-!
# The same finite native partition as bundle chart cutoffs

Public module ID: M0814.

The original native presentation is passed through its existing atlas adapter.
This retains each native frame and scalar cutoff. The two support and pullback
identities let a presentation subordinate to a principal cover provide the
actual base cutoffs for local associated operators.

The chart cutoffs use the same native partition throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Topology

variable {n a : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B] [T2Space B]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]

namespace SmoothBundlePresentation

/-- The original native frame with its original partition in chart coordinates. -/
def chartCutoff (L : SmoothBundlePresentation (n := n) (r := a) E) (j : Fin L.size) :
    BundleChartCutoff (r := a) E (L.chart j) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let K := L.toAtlasBundlePresentation.chartCutoff j
  { frame := L.frame j
    frame_mem_atlas := L.frame_mem_atlas j
    cutoff := K.cutoff
    smooth_cutoff := K.smooth_cutoff
    compact_support := K.compact_support
    support_subset := K.support_subset }

omit [T2Space B] in
/-- The coordinate cutoff remains within the support of the same native partition function. -/
theorem chartCutoff_support_subset (L : SmoothBundlePresentation (n := n) (r := a) E)
    (j : Fin L.size) :
    (L.chart j).symm '' tsupport (L.chartCutoff E j).cutoff ⊆ tsupport (L.cutoff j) := by
  classical
  let c := L.chart j
  have hK : IsCompact (c '' tsupport (L.cutoff j)) :=
    (L.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  have hs : tsupport (L.chartCutoff E j).cutoff ⊆ c '' tsupport (L.cutoff j) := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    change (if z ∈ c.target then L.cutoff j (c.symm z) else 0) ≠ 0 at hz
    have hzt : z ∈ c.target := by
      by_contra h
      exact hz (ite_eq_right h)
    have hx : c.symm z ∈ tsupport (L.cutoff j) := by
      apply subset_tsupport
      intro hzero
      exact hz (by rw [ite_eq_left hzt, hzero])
    exact ⟨c.symm z, hx, c.right_inv hzt⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hs hz
  rwa [c.left_inv (L.support_subset j hx).1]

open Classical in
/-- Pullback and zero extension recover the same native partition weight. -/
theorem chartCutoff_pullback (L : SmoothBundlePresentation (n := n) (r := a) E)
    (j : Fin L.size) (x : B) :
    (if x ∈ (L.chart j).source then (L.chartCutoff E j).cutoff (L.chart j x) else 0) =
      L.cutoff j x := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  exact L.toAtlasBundlePresentation.chartCutoff_pullback j x

end SmoothBundlePresentation

end AtiyahSinger
