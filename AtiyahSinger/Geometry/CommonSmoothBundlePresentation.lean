/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundlePresentationSubordinate

/-!
# Common native bundle presentations subordinate to an open cover

Public module ID: M1128.

Two bundles over a compact smooth base admit presentations with the same
manifold charts and partition, retaining a selected member of the prescribed
open cover for every support. The two frame families remain in their original
bundle atlases. This simultaneous choice supplies the common base cutoffs for
the two vertical corners of the associated graded operator.

The construction refines the cover by the second bundle's frame domains and
then uses the existing subordinate presentation theorem for the first bundle.
It permits distinct ranks and an empty base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]
  (E F : M → Type*) [∀ x, TopologicalSpace (E x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]

/-- Two native presentations retain one chart partition and one prescribed support cover. -/
theorem exists_common_smoothBundlePresentation_subordinate {ι : Type*}
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ (L₀ : SmoothBundlePresentation (n := n) (r := r) E)
      (L₁ : SmoothBundlePresentation (n := n) (r := q) F)
      (e : Fin L₀.size ≃ Fin L₁.size) (i : Fin L₀.size → ι),
      (∀ j, L₁.chart (e j) = L₀.chart j) ∧
      (∀ j, L₁.cutoff (e j) = L₀.cutoff j) ∧
      (∀ j, tsupport (L₀.cutoff j) ⊆ U (i j)) := by
  classical
  -- Refine only the prescribed cover; the first theorem retains its native atlas choices.
  let frame (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  let V (p : ι × M) := U p.1 ∩ (frame p.2).baseSet
  have hV (p : ι × M) : IsOpen (V p) := (hU p.1).inter (frame p.2).open_baseSet
  have hcoverV (x : M) : ∃ p, x ∈ V p := by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨(i, x), hi, mem_baseSet_trivializationAt _ _ x⟩
  obtain ⟨L₀, index, hsupport⟩ :=
    exists_smoothBundlePresentation_subordinate (n := n) (r := r) E V hV hcoverV
  -- Reuse the complete partition and chart family, changing only the bundle frames.
  let L₁ : SmoothBundlePresentation (n := n) (r := q) F := {
    size := L₀.size
    chart := L₀.chart
    chart_mem_atlas := L₀.chart_mem_atlas
    frame := fun j ↦ frame (index j).2
    frame_mem_atlas := fun _ ↦ inferInstance
    cutoff := L₀.cutoff
    smooth_cutoff := L₀.smooth_cutoff
    cutoff_nonneg := L₀.cutoff_nonneg
    compact_support := L₀.compact_support
    support_subset := fun j x hx ↦ ⟨(L₀.support_subset j hx).1, (hsupport j hx).2⟩
    sum_cutoff := L₀.sum_cutoff }
  exact ⟨L₀, L₁, Equiv.refl _, fun j ↦ (index j).1,
    fun _ ↦ rfl, fun _ ↦ rfl, fun j x hx ↦ (hsupport j hx).1⟩

end AtiyahSinger
