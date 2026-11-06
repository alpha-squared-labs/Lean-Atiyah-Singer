/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite smooth bundle presentations and localization

Public module ID: M1379.

D04 and the required part of E01. A presentation consists of finitely many manifold
charts, bundle frames and a subordinate smooth partition of unity with compact supports.
Sobolev estimates are proved separately. Localization multiplies by a
cutoff and then extends by zero outside the coordinate chart target.

This is the usual auxiliary data behind Spin Geometry III.2.2 and (2.17). We allow
general open chart targets instead of imposing SG's particular unit-ball coordinates;
the compact support inside each chart is the condition needed by the subsequent norms.
On a compact Hausdorff second-countable smooth base, existence uses a finite
subcover of the original chart/frame overlaps and mathlib's
smooth partition of unity on this finite cover. No external project dependency
is required; the original frames and their base sets are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- A finite atlas/frame presentation with a compactly supported smooth partition of unity. -/
structure SmoothBundlePresentation where
  /-- The number of localizations; zero is permitted for an empty base. -/
  size : ℕ
  /-- A manifold chart for each localization. -/
  chart : Fin size → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- Each chosen chart belongs to the given smooth atlas. -/
  chart_mem_atlas : ∀ j, chart j ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- A complex-linear bundle chart for each localization. -/
  frame : Fin size → Trivialization (EuclideanSpace ℂ (Fin r))
    (π (EuclideanSpace ℂ (Fin r)) E)
  /-- Each frame belongs to the specified bundle atlas. -/
  frame_mem_atlas : ∀ j, MemTrivializationAtlas (frame j)
  /-- The real-valued partition weights on the base. -/
  cutoff : Fin size → M → ℝ
  /-- The weights are smooth over the real manifold. -/
  smooth_cutoff : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ (cutoff j)
  /-- Nonnegativity of the partition weights. -/
  cutoff_nonneg : ∀ j x, 0 ≤ cutoff j x
  /-- Every weight has compact topological support. -/
  compact_support : ∀ j, HasCompactSupport (cutoff j)
  /-- Supports lie inside both the manifold chart and the bundle frame. -/
  support_subset : ∀ j, tsupport (cutoff j) ⊆ (chart j).source ∩ (frame j).baseSet
  /-- The weights sum to one everywhere on the base. -/
  sum_cutoff : ∀ x, ∑ j, cutoff j x = 1

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

-- Preserve the original ambient assumptions while using only the partition prerequisites.
set_option linter.unusedSectionVars false in
/-- A compact Hausdorff second-countable smooth base admits the finite presentation
required for Sobolev localization. -/
theorem nonempty_smoothBundlePresentation [CompactSpace M] :
    Nonempty (SmoothBundlePresentation (n := n) (r := r) E) := by
  /- Stage 1: cover the base by intersections of manifold-chart sources and smooth
  bundle-frame base sets. These sets are open and cover M.
  Stage 2: take a finite subcover and reindex it by Fin N. Apply the native
  smooth partition theorem to this finite open cover of the whole base.
  Stage 3: retain the chosen original charts and frames. Compactness of the
  base supplies compact support, and the finite partition identity is unchanged. -/
  classical
  -- Take a finite cover by intersections of the original manifold and bundle charts.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let U (x : M) := (c x).source ∩ (e x).baseSet
  have hopen (x : M) : IsOpen (U x) := (c x).open_source.inter (e x).open_baseSet
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x, mem_baseSet_trivializationAt _ _ x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  let f : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (f j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨f.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  -- Construct the partition on exactly this finite family, retaining its chosen frames.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V (fun j ↦ hopen (f j)) hfinitecover
  refine ⟨{
    size := s.card
    chart := fun j ↦ c (f j)
    chart_mem_atlas := fun j ↦ chart_mem_atlas _ (f j : M)
    frame := fun j ↦ e (f j)
    frame_mem_atlas := fun _ ↦ inferInstance
    cutoff := fun j ↦ ρ j
    smooth_cutoff := fun j ↦ (ρ j).contMDiff
    cutoff_nonneg := ρ.nonneg
    compact_support := fun j ↦ HasCompactSupport.of_compactSpace (ρ j)
    support_subset := hρ
    sum_cutoff := ?_ }⟩
  intro x
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

namespace SmoothBundlePresentation

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The compactly supported coordinate function of a global smooth section.
The explicit zero extension prevents evaluation of the inverse chart outside its target. -/
def localizedFunction (j : Fin A.size) (u : smoothSections (n := n) (r := r) E)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin r) := by
  classical
  exact if z ∈ (A.chart j).target then
    (A.cutoff j ((A.chart j).symm z) : ℂ) •
      sectionInChart E (A.chart j) (A.frame j) u.val z
  else 0

-- The support estimate retains the original smooth ambient interface.
set_option linter.unusedSectionVars false in
/-- Localization has support in the fixed coordinate image of the cutoff support. -/
theorem tsupport_localizedFunction_subset (j : Fin A.size)
    (u : smoothSections (n := n) (r := r) E) :
    tsupport (A.localizedFunction j u) ⊆ (A.chart j) '' tsupport (A.cutoff j) := by
  /- Nonzero values require a nonzero cutoff at the inverse-chart point, giving the
  inclusion before closure. The chart is continuous on the compact cutoff support;
  its image is compact and hence closed in Euclidean space. Take the closure. -/
  classical
  -- The coordinate image of the cutoff support is compact, so it is closed.
  have hcompact : IsCompact ((A.chart j) '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  apply closure_minimal ?_ hcompact.isClosed
  intro z hz
  have htarget : z ∈ (A.chart j).target := by
    by_contra houtside
    exact hz (by simp [localizedFunction, houtside])
  have hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j) := by
    by_contra houtside
    have hzero := image_eq_zero_of_notMem_tsupport houtside
    exact hz (by simp [localizedFunction, hzero])
  exact ⟨(A.chart j).symm z, hcut, (A.chart j).right_inv htarget⟩

/-- Every localized section has compact support in Euclidean space. -/
theorem hasCompactSupport_localizedFunction (j : Fin A.size)
    (u : smoothSections (n := n) (r := r) E) :
    HasCompactSupport (A.localizedFunction j u) := by
  /- The preceding support inclusion places the closed topological support in the
  compact image of the cutoff support. A closed subset of that compact set is compact. -/
  have hcompact : IsCompact ((A.chart j) '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  exact hcompact.of_isClosed_subset (isClosed_tsupport _)
    (A.tsupport_localizedFunction_subset j u)

/-- Zero extension of the localized section is smooth across the chart boundary. -/
theorem contDiff_localizedFunction (j : Fin A.size)
    (u : smoothSections (n := n) (r := r) E) :
    ContDiff ℝ ∞ (A.localizedFunction j u) := by
  /- Inside the coordinate image of the chart/frame overlap this is a product of
  smooth functions. The cutoff support is a compact subset of that open overlap.
  Away from its compact coordinate image the extension vanishes on a neighborhood.
  These two regions cover Euclidean space, so the piecewise definition is smooth. -/
  classical
  let c := A.chart j
  let K := c '' tsupport (A.cutoff j)
  have hcompact : IsCompact K :=
    (A.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ K
  · -- On the support use the original section coordinates in the selected frame.
    obtain ⟨x, hx, rfl⟩ := hz
    have hxsource := (A.support_subset j hx).1
    have htarget : c x ∈ c.target := c.map_source hxsource
    have hframe : c.symm (c x) ∈ (A.frame j).baseSet := by
      rw [c.left_inv hxsource]
      exact (A.support_subset j hx).2
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (A.chart_mem_atlas j)) htarget
    have hsection := (u.property (A.frame j) (A.frame_mem_atlas j)).contMDiffAt
      ((A.frame j).open_baseSet.mem_nhds hframe)
    have hcoords := hsection.comp (c x) hchart
    have hcut := (A.smooth_cutoff j).contMDiffAt.comp (c x) hchart
    have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
    have hlocal := hscalar.contDiffAt.smul hcoords.contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds htarget] with y hy
    change y ∈ (A.chart j).target at hy
    simp [localizedFunction, sectionInChart, hy, c]
  · -- Away from the closed coordinate support the prescribed zero extension is locally zero.
    apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport
      (fun hmem ↦ hy (A.tsupport_localizedFunction_subset j u hmem))

/-- The actual Schwartz function obtained by smooth compact-support localization. -/
def localize (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (A.hasCompactSupport_localizedFunction j u).toSchwartzMap
    (A.contDiff_localizedFunction j u)

/-- The Schwartz localization respects addition of global sections. -/
theorem localize_add (j : Fin A.size) (u v : smoothSections (n := n) (r := r) E) :
    A.localize j (u + v) = A.localize j u + A.localize j v := by
  /- Work pointwise. Outside the chart target every term is zero. On the cutoff
  support the chosen frame is fiberwise linear; outside that support the cutoff is
  zero. Distributivity proves the equality of functions, hence of Schwartz maps. -/
  classical
  let := A.frame_mem_atlas j
  apply DFunLike.ext
  intro z
  change A.localizedFunction j (u + v) z = A.localizedFunction j u z +
    A.localizedFunction j v z
  by_cases hz : (A.chart j).symm z ∈ tsupport (A.cutoff j)
  · have hframe := (A.support_subset j hz).2
    by_cases htarget : z ∈ (A.chart j).target
    · simp only [localizedFunction, ite_eq_left htarget, sectionInChart,
        Submodule.coe_add, Pi.add_apply]
      have hadd : (A.frame j ⟨(A.chart j).symm z,
          u.val ((A.chart j).symm z) + v.val ((A.chart j).symm z)⟩).2 =
            (A.frame j ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2 +
              (A.frame j ⟨(A.chart j).symm z, v.val ((A.chart j).symm z)⟩).2 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_add _ _
      rw [hadd, smul_add]
    · simp [localizedFunction, htarget]
  · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]

/-- The Schwartz localization respects complex scalar multiplication. -/
theorem localize_smul (j : Fin A.size) (c : ℂ)
    (u : smoothSections (n := n) (r := r) E) :
    A.localize j (c • u) = c • A.localize j u := by
  /- On the cutoff support use complex linearity of the frame and commutation of
  complex scalars. Everywhere else the localized functions vanish. Extensionality
  promotes this pointwise identity to an equality of Schwartz maps. -/
  classical
  let := A.frame_mem_atlas j
  apply DFunLike.ext
  intro z
  change A.localizedFunction j (c • u) z = c • A.localizedFunction j u z
  by_cases hz : (A.chart j).symm z ∈ tsupport (A.cutoff j)
  · have hframe := (A.support_subset j hz).2
    by_cases htarget : z ∈ (A.chart j).target
    · simp only [localizedFunction, ite_eq_left htarget, sectionInChart,
        Submodule.coe_smul, Pi.smul_apply]
      have hsmul : (A.frame j ⟨(A.chart j).symm z,
          c • u.val ((A.chart j).symm z)⟩).2 =
            c • (A.frame j ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_smul _ _
      rw [hsmul, smul_comm]
    · simp [localizedFunction, htarget]
  · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]

/-- Localization as a complex-linear map, with its concrete function formula above. -/
def localizeLinearMap (j : Fin A.size) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) where
  toFun := A.localize j
  map_add' := A.localize_add j
  map_smul' := A.localize_smul j

end SmoothBundlePresentation

end AtiyahSinger
