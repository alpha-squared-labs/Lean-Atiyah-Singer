/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundlePresentation

/-!
# Changing bundle frames while retaining a fixed scalar partition

Public module ID: M1380.

A presentation for a second bundle can use the same finite index set, manifold
charts and scalar partition as a given presentation. The supplied new frames
must belong to their bundle atlas and contain the existing cutoff supports.
The construction retains the old size, chart and cutoff data definitionally.

This is used twice in the associated-sphere proof, for its common sphere and
base partitions. The projection formulas below record exactly the scalar
presentation data retained by the construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothBundlePresentation

open Bundle
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]

/-- Retain the same scalar presentation and use the supplied frames of another bundle. -/
def withFrame (A : SmoothBundlePresentation (n := n) (r := r) E)
    (frame : Fin A.size → Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    (hframe : ∀ j, MemTrivializationAtlas (frame j))
    (hsupport : ∀ j, tsupport (A.cutoff j) ⊆ (frame j).baseSet) :
    SmoothBundlePresentation (n := n) (r := q) F where
  size := A.size
  chart := A.chart
  chart_mem_atlas := A.chart_mem_atlas
  frame := frame
  frame_mem_atlas := hframe
  cutoff := A.cutoff
  smooth_cutoff := A.smooth_cutoff
  cutoff_nonneg := A.cutoff_nonneg
  compact_support := A.compact_support
  support_subset := fun j _ hx ↦ ⟨(A.support_subset j hx).1, hsupport j hx⟩
  sum_cutoff := A.sum_cutoff

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (frame : Fin A.size → Trivialization (EuclideanSpace ℂ (Fin q))
    (π (EuclideanSpace ℂ (Fin q)) F))
  (hframe : ∀ j, MemTrivializationAtlas (frame j))
  (hsupport : ∀ j, tsupport (A.cutoff j) ⊆ (frame j).baseSet)

/-- Changing the bundle frame retains the original finite index type. -/
@[simp] theorem withFrame_size : (A.withFrame frame hframe hsupport).size = A.size := rfl

/-- The manifold charts are the supplied presentation's original charts. -/
@[simp] theorem withFrame_chart : (A.withFrame frame hframe hsupport).chart = A.chart := rfl

/-- The scalar partition is unchanged by the change of bundle frame. -/
@[simp] theorem withFrame_cutoff : (A.withFrame frame hframe hsupport).cutoff = A.cutoff := rfl

end AtiyahSinger.SmoothBundlePresentation
