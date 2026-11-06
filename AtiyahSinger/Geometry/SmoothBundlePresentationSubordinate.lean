/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundlePresentation

/-!
# Native finite bundle presentations subordinate to a specified open cover

Public module ID: M1381.

A compact Hausdorff smooth base admits a presentation in the original manifold
and bundle
atlases whose partition supports also lie in selected members of a prescribed
open cover. The returned cover indices retain those choices for later local
operator assembly. In particular, a principal-bundle cover can be used without
replacing either native atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]
  (E : M → Type*)
  [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]

/-- A native finite presentation can retain the specified covering set for every support. -/
theorem exists_smoothBundlePresentation_subordinate {ι : Type*}
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ (L : SmoothBundlePresentation (n := n) (r := r) E) (i : Fin L.size → ι),
      ∀ j, tsupport (L.cutoff j) ⊆ U (i j) := by
  classical
  -- Refine the supplied cover by the two original atlases at each point.
  choose i hi using hcover
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let V (x : M) := ((c x).source ∩ (e x).baseSet) ∩ U (i x)
  have hV (x : M) : IsOpen (V x) :=
    ((c x).open_source.inter (e x).open_baseSet).inter (hU (i x))
  have hcoverV : Set.univ ⊆ ⋃ x, V x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,
      ⟨mem_chart_source _ x, mem_baseSet_trivializationAt _ _ x⟩, hi x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV hcoverV
  let f : Fin s.card ≃ s := s.equivFin.symm
  let W (j : Fin s.card) := V (f j)
  have hcoverW : Set.univ ⊆ ⋃ j, W j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨f.symm ⟨y, hy⟩, by simpa only [W, f.apply_symm_apply] using hxy⟩
  -- The single finite partition satisfies both frame support and prescribed-cover support.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ W (fun j ↦ hV (f j)) hcoverW
  let L : SmoothBundlePresentation (n := n) (r := r) E := {
    size := s.card
    chart := fun j ↦ c (f j)
    chart_mem_atlas := fun j ↦ chart_mem_atlas _ (f j : M)
    frame := fun j ↦ e (f j)
    frame_mem_atlas := fun _ ↦ inferInstance
    cutoff := fun j ↦ ρ j
    smooth_cutoff := fun j ↦ (ρ j).contMDiff
    cutoff_nonneg := ρ.nonneg
    compact_support := fun j ↦ HasCompactSupport.of_compactSpace (ρ j)
    support_subset := fun j x hx ↦ (hρ j hx).1
    sum_cutoff := fun x ↦ by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x) }
  exact ⟨L, fun j ↦ i (f j), fun j x hx ↦ (hρ j hx).2⟩

end AtiyahSinger
