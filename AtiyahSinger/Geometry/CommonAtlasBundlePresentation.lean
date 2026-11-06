/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundlePresentation

/-!
# A common finite presentation for two original bundle atlases (M2316)

A single finite manifold chart cover and smooth partition can be subordinate
to frames of two locally finite-rank bundle atlases. The returned presentation
uses the first atlas; each second frame domain contains the same cutoff support.
It therefore gives a presentation for the second atlas with literally the same
size, charts and scalar weights by changing only the frame fields.

This is the common-cover form of the finite partition construction used for
bundle localization. It synchronizes the two sphere coefficient bundles in
the associated graded tensor construction, without comparing their ranks or
assuming equality of independently chosen cutoffs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (Bundle.TotalSpace Unit F)]

/-- One finite scalar partition is subordinate to both specified bundle atlases. -/
theorem exists_atlasBundlePresentation_common_frames
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F) :
    ∃ (J : AtlasBundlePresentation A) (i : Fin J.size → B.Index),
      ∀ j, tsupport (J.cutoff j) ⊆ (B.chart (i j)).baseSet := by
  classical
  -- Intersect the two original frame domains before taking a finite manifold chart cover.
  choose e he using A.covers
  choose f hf using B.covers
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let U (x : M) := ((c x).source ∩ (A.chart (e x)).baseSet) ∩ (B.chart (f x)).baseSet
  have hU (x : M) : IsOpen (U x) :=
    ((c x).open_source.inter (A.chart (e x)).open_baseSet).inter
      (B.chart (f x)).open_baseSet
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, ⟨mem_chart_source _ x, he x⟩, hf x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (index j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩,
      by simpa only [V, index.apply_symm_apply] using hxy⟩
  -- Construct the weights once; both frame families use this same partition.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V (fun j ↦ hU (index j)) hfinitecover
  let J : AtlasBundlePresentation A := {
    size := s.card
    chart := fun j ↦ c (index j)
    chart_mem_atlas := fun j ↦ chart_mem_atlas _ (index j : M)
    frameIndex := fun j ↦ e (index j)
    cutoff := fun j ↦ ρ j
    smooth_cutoff := fun j ↦ (ρ j).contMDiff
    cutoff_nonneg := ρ.nonneg
    compact_support := fun j ↦ HasCompactSupport.of_compactSpace (ρ j)
    support_subset := fun j x hx ↦ (hρ j hx).1
    sum_cutoff := fun x ↦ by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x) }
  exact ⟨J, fun j ↦ f (index j), fun j x hx ↦ (hρ j hx).2⟩

end AtiyahSinger
