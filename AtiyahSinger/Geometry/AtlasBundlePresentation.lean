/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.VariableRankDifferentialOperator
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite localization data for a locally finite-rank smooth bundle

Public module ID: M1087.

D04: a finite presentation selects actual manifold charts, indices of the
given smooth bundle atlas, and a subordinate smooth partition of unity with
compact supports. Its coordinate spaces retain the rank of each selected
chart. No common rank, new fiber norm, or replacement total-space topology
is chosen. A compact smooth base admits these standard localization data.

The localized section is the explicit cutoff product in the selected chart,
extended by zero outside its target. Smoothness and compact support are
proved as a grouped implementation certificate for its Schwartz packaging.
No Sobolev estimate or result about a completion is a presentation field.

Sources: Spin Geometry III.2.2 and (2.17), pp.170-176. As in the existing
SmoothBundlePresentation, arbitrary open coordinate targets replace the
book's ball coordinates; compact support inside the chart overlap is the
property used by localization. The finite partition is constructed directly
from mathlib's smooth partition-of-unity theorem after taking a finite subcover.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Topology
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)

/-- Finite manifold charts and original atlas frames with a subordinate smooth partition. -/
structure AtlasBundlePresentation where
  /-- The number of localizations; it may be zero when the base is empty. -/
  size : ℕ
  /-- The actual manifold chart used for each localization. -/
  chart : Fin size → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- Each chosen manifold chart belongs to the given smooth atlas. -/
  chart_mem_atlas : ∀ j, chart j ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- The index of the original bundle chart used for each localization. -/
  frameIndex : Fin size → A.Index
  /-- The real partition weights on the base. -/
  cutoff : Fin size → M → ℝ
  /-- Every partition weight is smooth. -/
  smooth_cutoff : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ (cutoff j)
  /-- The partition weights are nonnegative. -/
  cutoff_nonneg : ∀ j x, 0 ≤ cutoff j x
  /-- Every weight has compact topological support. -/
  compact_support : ∀ j, HasCompactSupport (cutoff j)
  /-- The support stays inside the selected manifold and original bundle chart overlap. -/
  support_subset : ∀ j,
    tsupport (cutoff j) ⊆ (chart j).source ∩ (A.chart (frameIndex j)).baseSet
  /-- The weights form a partition of unity on the entire base. -/
  sum_cutoff : ∀ x, ∑ j, cutoff j x = 1

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC

-- Compactness supplies sigma-compactness for the partition-of-unity construction.
set_option linter.unusedSectionVars false in
/-- A compact smooth base admits finite localization data in the specified bundle atlas. -/
theorem nonempty_atlasBundlePresentation [CompactSpace M] :
    Nonempty (AtlasBundlePresentation A) := by
  /- Stage 1: at each base point choose a manifold chart and a covering index
  from A.covers. Their open intersection gives a cover by actual chart overlaps.
  Stage 2: compactness gives a finite subcover; reindex those chosen overlaps
  by Fin size. Apply mathlib's smooth partition-of-unity theorem to that finite
  open cover. Each resulting support is compact because the base is compact.
  Stage 3: retain the original manifold charts and bundle indices, together
  with the weights' smoothness, nonnegativity and support subordination. The
  partition's finsum equals the finite sum over the same Fin size index.
  Source charts can have different ranks on different components, and their
  ranks need neither agree nor be bounded in advance. No analytic estimate
  is used to construct this standard auxiliary presentation. -/
  classical
  choose frame hframe using A.covers
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let U (x : M) := (c x).source ∩ (A.chart (frame x)).baseSet
  have hopen (x : M) : IsOpen (U x) :=
    (c x).open_source.inter (A.chart (frame x)).open_baseSet
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x, hframe x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  -- Reindex the finite subcover before constructing the partition of unity.
  let e : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (e j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V (fun j ↦ hopen (e j)) hfinitecover
  refine ⟨{
    size := s.card
    chart := fun j ↦ c (e j)
    chart_mem_atlas := fun j ↦ chart_mem_atlas _ (e j : M)
    frameIndex := fun j ↦ frame (e j)
    cutoff := fun j ↦ ρ j
    smooth_cutoff := fun j ↦ (ρ j).contMDiff
    cutoff_nonneg := ρ.nonneg
    compact_support := fun j ↦ HasCompactSupport.of_compactSpace (ρ j)
    support_subset := hρ
    sum_cutoff := ?_ }⟩
  -- The finite-index finsum is the unchanged partition sum on the entire base.
  intro x
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

namespace AtlasBundlePresentation

variable {A} (L : AtlasBundlePresentation A)

/-- The actual cutoff section in the selected coordinates, extended by zero off the chart. -/
def localizedFunction (j : Fin L.size) (u : A.smoothSections)
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))) := by
  classical
  exact if z ∈ (L.chart j).target then
    (L.cutoff j ((L.chart j).symm z) : ℂ) •
      atlasSectionInChart A (L.chart j) (L.frameIndex j) u.val z
  else 0

-- The compact coordinate image of the cutoff support is closed.
set_option linter.unusedSectionVars false in
/-- The smoothness and fixed compact support needed to package a localized Schwartz function.
These are implementation certificates for the single localization construction. -/
theorem localizedFunction_properties (j : Fin L.size) (u : A.smoothSections) :
    ContDiff ℝ ∞ (L.localizedFunction j u) ∧
      tsupport (L.localizedFunction j u) ⊆ (L.chart j) '' tsupport (L.cutoff j) ∧
        HasCompactSupport (L.localizedFunction j u) := by
  /- Stage 1: every nonzero localized value has a nonzero cutoff at
  its inverse chart point. The chart image of the compact cutoff
  support is compact, hence closed; taking closures puts the
  localized support inside that fixed coordinate set.
  Stage 2: at a point of that set, subordination gives the manifold
  and frame overlap. Compose the original smooth section coordinates
  and cutoff with the inverse smooth manifold chart and the fixed
  Euclidean coordinate equivalence, then multiply them.
  Stage 3: outside the closed compact coordinate set the extension
  vanishes on a neighborhood. These two regions cover coordinate
  space and prove smoothness across the zero-extension boundary. -/
  classical
  let c := L.chart j
  let K := c '' tsupport (L.cutoff j)
  have hcompact : IsCompact K :=
    (L.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  -- Nonzero coordinates can only occur in the fixed compact image of the cutoff support.
  have hsupport : tsupport (L.localizedFunction j u) ⊆ K := by
    apply closure_minimal ?_ hcompact.isClosed
    intro z hz
    have htarget : z ∈ c.target := by
      by_contra houtside
      change z ∉ (L.chart j).target at houtside
      exact hz (by simp [localizedFunction, houtside])
    have hcut : c.symm z ∈ tsupport (L.cutoff j) := by
      by_contra houtside
      have hzero := image_eq_zero_of_notMem_tsupport houtside
      change L.cutoff j ((L.chart j).symm z) = 0 at hzero
      exact hz (by simp [localizedFunction, hzero])
    exact ⟨c.symm z, hcut, c.right_inv htarget⟩
  refine ⟨?_, hsupport, hcompact.of_isClosed_subset (isClosed_tsupport _) hsupport⟩
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ K
  · obtain ⟨x, hx, rfl⟩ := hz
    have hxsource := (L.support_subset j hx).1
    have htarget : c x ∈ c.target := c.map_source hxsource
    have hframe : c.symm (c x) ∈ (A.chart (L.frameIndex j)).baseSet := by
      rw [c.left_inv hxsource]
      exact (L.support_subset j hx).2
    -- Compose the original smooth cutoff and frame coordinates with the actual inverse chart.
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (L.chart_mem_atlas j)) htarget
    have hsection := (u.property (L.frameIndex j)).contMDiffAt
      ((A.chart (L.frameIndex j)).open_baseSet.mem_nhds hframe)
    let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
    have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp (c x)
      (hsection.comp (c x) hchart)
    have hcut := (L.smooth_cutoff j).contMDiffAt.comp (c x) hchart
    have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
    have hlocal := hscalar.contDiffAt.smul hcoords.contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds htarget] with y hy
    change y ∈ (L.chart j).target at hy
    simp [localizedFunction, atlasSectionInChart, hy, c, e]
  · -- The complement of the fixed compact coordinate set is an open zero region.
    apply (contDiffAt_const
      (c := (0 : EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))))).congr_of_eventuallyEq
    filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun hmem ↦ hy (hsupport hmem))

/-- The actual Schwartz localization, with the finite rank of its selected original chart. -/
def localize (j : Fin L.size) (u : A.smoothSections) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) :=
  (L.localizedFunction_properties j u).2.2.toSchwartzMap
    (L.localizedFunction_properties j u).1

/-- Complex linearity of the concrete Schwartz localization.
This single certificate supplies the fields of the localization linear map. -/
theorem isLinearMap_localize (j : Fin L.size) : IsLinearMap ℂ (L.localize j) := by
  /- Evaluate the Schwartz functions pointwise. Where the cutoff is nonzero,
  subordination puts the point in the selected frame base set, and A.linear
  makes the actual frame coordinates complex linear. The Euclidean coordinate
  equivalence is complex linear as well. Multiplication by the fixed cutoff
  preserves addition and scalar multiplication. Everywhere else all localized
  values vanish. Schwartz extensionality gives both linearity laws. -/
  classical
  constructor
  · intro u v
    apply DFunLike.ext
    intro z
    change L.localizedFunction j (u + v) z = L.localizedFunction j u z + L.localizedFunction j v z
    by_cases hz : z ∈ (L.chart j).target
    · by_cases hcut : (L.chart j).symm z ∈ tsupport (L.cutoff j)
      · have hframe := (L.support_subset j hcut).2
        simp only [localizedFunction, ite_eq_left hz, atlasSectionInChart,
          Submodule.coe_add, Pi.add_apply]
        rw [(A.linear (L.frameIndex j) ((L.chart j).symm z) hframe).map_add]
        simp only [map_add, smul_add]
      · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hcut]
    · simp [localizedFunction, hz]
  · intro a u
    apply DFunLike.ext
    intro z
    change L.localizedFunction j (a • u) z = a • L.localizedFunction j u z
    by_cases hz : z ∈ (L.chart j).target
    · by_cases hcut : (L.chart j).symm z ∈ tsupport (L.cutoff j)
      · have hframe := (L.support_subset j hcut).2
        simp only [localizedFunction, ite_eq_left hz, atlasSectionInChart,
          Submodule.coe_smul, Pi.smul_apply]
        rw [(A.linear (L.frameIndex j) ((L.chart j).symm z) hframe).map_smul]
        simp only [map_smul, smul_comm (L.cutoff j ((L.chart j).symm z) : ℂ) a]
      · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hcut]
    · simp [localizedFunction, hz]

/-- The complex-linear map defined by the original cutoff coordinate formula. -/
def localizeLinearMap (j : Fin L.size) :
    A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) :=
  IsLinearMap.mk' (L.localize j) (L.isLinearMap_localize j)

end AtlasBundlePresentation

end AtiyahSinger
