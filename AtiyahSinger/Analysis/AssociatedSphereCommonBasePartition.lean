/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativePresentationChartCutoff
public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.CommonSmoothBundlePresentation

/-!
# One actual native base partition for both vertical corners

Public module ID: M0109.

Both coefficient bundles use the same indexing, chart and cutoff family.
Its guarded associated-chart weights sum to
one because each is the original base partition weight at the projection.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [CompactSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle

set_option maxSynthPendingDepth 40 in
open scoped Classical in
/-- Both original coefficient bundles share one base partition and its associated weights. -/
theorem exists_associatedSphere_common_base_partition :
    ∃ (J : SmoothBundlePresentation (n := n) (r := a) E)
      (frame' : Fin J.size → Trivialization (EuclideanSpace ℂ (Fin a'))
        (π (EuclideanSpace ℂ (Fin a')) E'))
      (hframe' : ∀ j, MemTrivializationAtlas (frame' j))
      (hsframe' : ∀ j, tsupport (J.cutoff j) ⊆ (frame' j).baseSet)
      (b : Fin J.size → B)
      (_hJ : ∀ j, tsupport (J.cutoff j) ⊆ (S.trivialization (b j)).baseSet),
      let J' : SmoothBundlePresentation (n := n) (r := a') E' := {
        size := J.size
        chart := J.chart
        chart_mem_atlas := J.chart_mem_atlas
        frame := frame'
        frame_mem_atlas := hframe'
        cutoff := J.cutoff
        smooth_cutoff := J.smooth_cutoff
        cutoff_nonneg := J.cutoff_nonneg
        compact_support := J.compact_support
        support_subset := fun j _ hx ↦ ⟨(J.support_subset j hx).1, hsframe' j hx⟩
        sum_cutoff := J.sum_cutoff }
      (∀ j, (J'.chartCutoff E' j).cutoff = (J.chartCutoff E j).cutoff) ∧
      ∀ z : Z, ∑ j : Fin J.size,
        (if z ∈ (associatedSphereTrivialization S (b j)).source ∧
            (associatedSphereTrivialization S (b j) z).1 ∈ (J.chart j).source then
          (J.chartCutoff E j).cutoff
            (J.chart j (associatedSphereTrivialization S (b j) z).1)
        else 0) = 1 := by
  classical
  -- Choose both native frame families inside the same original principal cover.
  obtain ⟨J, Jother, e, b, hchart, hcutoff, hJ⟩ :=
    exists_common_smoothBundlePresentation_subordinate (n := n) (r := a) (q := a') E E'
      (fun b ↦ (S.trivialization b).baseSet)
      (fun b ↦ (S.trivialization b).open_baseSet) (fun x ↦ ⟨x, S.mem_baseSet x⟩)
  let frame' := fun j ↦ Jother.frame (e j)
  have hframe' (j : Fin J.size) : MemTrivializationAtlas (frame' j) :=
    Jother.frame_mem_atlas (e j)
  have hsframe' (j : Fin J.size) : tsupport (J.cutoff j) ⊆ (frame' j).baseSet := by
    intro x hx
    exact (Jother.support_subset (e j) (by rwa [hcutoff])).2
  refine ⟨J, frame', hframe', hsframe', b, hJ, ?_⟩
  intro J'
  constructor
  · intro j
    rfl
  intro z
  -- A guarded associated-chart weight is the original cutoff at the same projection.
  have hweight (j : Fin J.size) :
      (if z ∈ (associatedSphereTrivialization S (b j)).source ∧
          (associatedSphereTrivialization S (b j) z).1 ∈ (J.chart j).source then
        (J.chartCutoff E j).cutoff
          (J.chart j (associatedSphereTrivialization S (b j) z).1)
      else 0) = J.cutoff j (πS z) := by
    let t := associatedSphereTrivialization S (b j)
    have htbase : t.baseSet = (S.trivialization (b j)).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization (b j)) (S.equivariant (b j))).choose_spec.1
    by_cases hz : z ∈ t.source
    · have hfst : (t z).1 = πS z := t.coe_fst hz
      change (if z ∈ t.source ∧ (t z).1 ∈ (J.chart j).source then
        (J.chartCutoff E j).cutoff (J.chart j (t z).1) else 0) = _
      rw [hfst]
      simpa only [hz, true_and] using J.chartCutoff_pullback E j (πS z)
    · have hzero : J.cutoff j (πS z) = 0 := by
        by_contra h
        have hs : πS z ∈ tsupport (J.cutoff j) := subset_tsupport _ h
        exact hz (t.mem_source.mpr (htbase.symm ▸ hJ j hs))
      change (if z ∈ t.source ∧ (t z).1 ∈ (J.chart j).source then
        (J.chartCutoff E j).cutoff (J.chart j (t z).1) else 0) = _
      simp only [hz, false_and, ite_false, hzero]
  simp_rw [hweight]
  exact J.sum_cutoff (πS z)

end AtiyahSinger
