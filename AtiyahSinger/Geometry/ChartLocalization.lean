/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Cutoff localization and extension in a single bundle chart

Public module ID: M1118.

D01/D05: the two concrete maps needed to transport a local Schwartz operator to
global smooth sections. The auxiliary data are a bundle frame and a real smooth
cutoff with compact closed support inside the coordinate/frame overlap. They need
not belong to a partition of unity. Extension uses the inverse frame and is zero
outside the chart source. It needs no global compactness, density or fiber metric.

Sources: Spin Geometry III.2.2 and III.3.15, pp.186-187. These maps include cutoff
factors: their round trip multiplies by the square of the cutoff, not by one.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Auxiliary frame and compact cutoff data in a specified manifold chart. -/
structure BundleChartCutoff (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) where
  /-- The frame used for both restriction and extension. -/
  frame : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E)
  /-- The frame is in the specified complex-linear bundle atlas. -/
  frame_mem_atlas : MemTrivializationAtlas frame
  /-- The real cutoff on coordinate space. -/
  cutoff : EuclideanSpace ℝ (Fin n) → ℝ
  /-- The cutoff is smooth over the real coordinates. -/
  smooth_cutoff : ContDiff ℝ ∞ cutoff
  /-- Its closed support is compact in coordinate space. -/
  compact_support : HasCompactSupport cutoff
  /-- Its closed support avoids both the chart and frame boundaries. -/
  support_subset : tsupport cutoff ⊆ c.target ∩ c.symm ⁻¹' frame.baseSet

namespace BundleChartCutoff

variable {E} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (A : BundleChartCutoff (r := r) E c)

/-- Restrict a global section, multiply by the coordinate cutoff, and extend by zero. -/
def localizedFunction (u : smoothSections (n := n) (r := r) E)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin r) := by
  classical
  exact if z ∈ c.target then
    (A.cutoff z : ℂ) • sectionInChart E c A.frame u.val z else 0

/-- The localized function has support in the fixed coordinate cutoff support. -/
theorem tsupport_localizedFunction_subset (u : smoothSections (n := n) (r := r) E) :
    tsupport (A.localizedFunction u) ⊆ tsupport A.cutoff := by
  /- Outside the cutoff support the scalar multiplier is zero, including where the
  zero-extension branch is taken. The nonzero set is contained in the closed cutoff
  support. Taking closure gives the stated inclusion without any chart smoothness. -/
  classical
  apply closure_minimal ?_ (isClosed_tsupport A.cutoff)
  intro z hz
  by_contra houtside
  have hzero := image_eq_zero_of_notMem_tsupport houtside
  exact hz (by simp [localizedFunction, hzero])

/-- Compact support of the cutoff gives compact support of every localization. -/
theorem hasCompactSupport_localizedFunction (u : smoothSections (n := n) (r := r) E) :
    HasCompactSupport (A.localizedFunction u) := by
  /- The topological support is closed in Euclidean space and lies in the compact
  support of A.cutoff by the preceding inclusion. A closed subset of a compact set
  is compact; no compactness of the manifold itself is required. -/
  exact A.compact_support.of_isClosed_subset (isClosed_tsupport _)
    (A.tsupport_localizedFunction_subset u)

/-- Send coordinate values back by the inverse frame, with a cutoff and zero extension. -/
def extendedFunction (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : M) : E x := by
  classical
  letI := A.frame_mem_atlas
  exact if x ∈ c.source then
    (A.cutoff (c x) : ℂ) • A.frame.symmL ℂ x (v (c x)) else 0

set_option linter.unusedSectionVars false in
/-- Extension vanishes outside the inverse coordinate image of the cutoff support. -/
theorem extendedFunction_eq_zero (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : M) (hx : x ∉ c.symm '' tsupport A.cutoff) : A.extendedFunction v x = 0 := by
  /- If x is outside the source, use the zero-extension branch. Otherwise c.symm
  (c x)=x, so hx forces c x outside the cutoff support and the scalar is zero.
  No pointwise norm comparison between different bundle fibers is involved. -/
  classical
  by_cases hsource : x ∈ c.source
  · have hcutoff : c x ∉ tsupport A.cutoff := by
      intro hcutoff
      exact hx ⟨c x, hcutoff, c.left_inv hsource⟩
    simp [extendedFunction, hsource, image_eq_zero_of_notMem_tsupport hcutoff]
  · simp [extendedFunction, hsource]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [IsSmoothComplexBundle (n := n) (r := r) E]
  (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)

include hc in
set_option linter.unusedSectionVars false in
/-- The cutoff localization is globally smooth in Euclidean coordinates. -/
theorem contDiff_localizedFunction (u : smoothSections (n := n) (r := r) E) :
    ContDiff ℝ ∞ (A.localizedFunction u) := by
  /- Stage 1: in the open coordinate/frame overlap, compose the smooth section
  coordinates with the inverse smooth atlas chart and multiply by the smooth cutoff.
  Stage 2: outside its closed support the expression is locally zero. The support
  lies inside that overlap, so these two open regions cover all coordinate space. -/
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ tsupport A.cutoff
  · -- On the supported overlap, retain the original section and inverse atlas chart.
    have hzchart := (A.support_subset hz).1
    have hzframe := (A.support_subset hz).2
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) hzchart
    have hsection := (u.property A.frame A.frame_mem_atlas).contMDiffAt
      (A.frame.open_baseSet.mem_nhds hzframe)
    have hcoords := hsection.comp z hchart
    have hlocal := (Complex.ofRealCLM.contDiff.comp A.smooth_cutoff).contDiffAt.smul
      hcoords.contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds hzchart] with y hy
    simp [localizedFunction, sectionInChart, hy]
  · -- Off the closed cutoff support, the same zero-extension formula vanishes locally.
    apply (contDiffAt_const
      (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport A.cutoff).isOpen_compl.mem_nhds hz] with y hy
    simp [localizedFunction, image_eq_zero_of_notMem_tsupport hy]

include hc in
/-- The inverse-frame formula is smooth across the chart boundary. -/
theorem isSmoothSection_extendedFunction
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    IsSmoothSection (n := n) (r := r) E (A.extendedFunction v) := by
  /- Stage 1: transport the compact cutoff support through the inverse chart.
  Its image lies in the source/frame overlap and is closed in Hausdorff M.
  Stage 2: on this image, express the output in any original frame.
  Its smooth complex-linear transition map acts on cutoff(c x) v(c x),
  whose factors are real smooth.
  Stage 3: outside the closed image the extension is locally zero,
  including at the chart boundary. These regions give global smoothness. -/
  classical
  let := A.frame_mem_atlas
  have hcompact : IsCompact (c.symm '' tsupport A.cutoff) :=
    A.compact_support.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ (A.support_subset hz).1))
  intro e he x hxe
  let := he
  by_cases hx : x ∈ c.symm '' tsupport A.cutoff
  · obtain ⟨z, hz, rfl⟩ := hx
    have hzchart := (A.support_subset hz).1
    have hxsource := c.map_target hzchart
    have hxframe := (A.support_subset hz).2
    have hchart := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) hxsource
    -- In each output frame the original inverse frame is its smooth transition map.
    have htransition := (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n)
      A.frame e).contMDiffAt
        ((A.frame.open_baseSet.inter e.open_baseSet).mem_nhds ⟨hxframe, hxe⟩)
    have hvector := (v.smooth ⊤).comp_contMDiffAt hchart
    have happly : ContDiff ℝ ∞
        (fun p : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ×
          EuclideanSpace ℂ (Fin r) ↦ p.1 p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hcoords := happly.comp_contMDiffAt (htransition.prodMk_space hvector)
    have hcutoff :=
      (Complex.ofRealCLM.contDiff.comp A.smooth_cutoff).comp_contMDiffAt hchart
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × EuclideanSpace ℂ (Fin r) ↦ p.1 • p.2) := contDiff_smul
    have hlocal := hmul.comp_contMDiffAt (hcutoff.prodMk_space hcoords)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [c.open_source.mem_nhds hxsource,
      A.frame.open_baseSet.mem_nhds hxframe, e.open_baseSet.mem_nhds hxe]
      with y hyc hyframe hye
    simp only [extendedFunction, ite_eq_left hyc]
    change (e.linearEquivAt ℂ y hye)
      ((A.cutoff (c y) : ℂ) • A.frame.symmL ℂ y (v (c y))) =
        (A.cutoff (c y) : ℂ) • (A.frame.coordChangeL ℂ e y) (v (c y))
    rw [map_smul, A.frame.coordChangeL_apply e ⟨hyframe, hye⟩,
      A.frame.symmL_apply hyframe]
    rfl
  · -- Hausdorffness makes the compact inverse-chart image closed, including its boundary.
    have hzero : ∀ᶠ y in nhds x, (e ⟨y, A.extendedFunction v y⟩).2 = 0 := by
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hx,
        e.open_baseSet.mem_nhds hxe] with y hy hye
      rw [A.extendedFunction_eq_zero v y hy]
      exact (e.linearEquivAt ℂ y hye).map_zero
    exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt

/-- The actual compactly supported Schwartz localization of a global smooth section. -/
def localize (u : smoothSections (n := n) (r := r) E) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (A.hasCompactSupport_localizedFunction u).toSchwartzMap (A.contDiff_localizedFunction hc u)

/-- The actual smooth section obtained by cutoff extension of a Schwartz function. -/
def extend (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    smoothSections (n := n) (r := r) E :=
  ⟨A.extendedFunction v, A.isSmoothSection_extendedFunction hc v⟩

/-- Localization respects addition through the complex-linear frame. -/
theorem localize_add (u v : smoothSections (n := n) (r := r) E) :
    A.localize hc (u + v) = A.localize hc u + A.localize hc v := by
  /- Work pointwise. On the cutoff support the inverse-chart point belongs to the
  frame base set, so the frame is additive on that fiber. Off this support all
  localized values vanish. Schwartz extensionality finishes the equality. -/
  classical
  let := A.frame_mem_atlas
  apply DFunLike.ext
  intro z
  change A.localizedFunction (u + v) z = A.localizedFunction u z + A.localizedFunction v z
  by_cases hz : z ∈ tsupport A.cutoff
  · have hzchart := (A.support_subset hz).1
    have hzframe := (A.support_subset hz).2
    simp only [localizedFunction, ite_eq_left hzchart, sectionInChart,
      Submodule.coe_add, Pi.add_apply]
    have hlinear := (A.frame.linearEquivAt ℂ (c.symm z) hzframe).map_add
      (u.val (c.symm z)) (v.val (c.symm z))
    simp only [Trivialization.linearEquivAt_apply] at hlinear
    rw [hlinear, smul_add]
  · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]

/-- Localization respects complex scalar multiplication. -/
theorem localize_smul (a : ℂ) (u : smoothSections (n := n) (r := r) E) :
    A.localize hc (a • u) = a • A.localize hc u := by
  /- On the cutoff support use complex linearity of the frame and commute the two
  scalar factors. Outside the support each side is zero, including the extension
  branch. Equality of values identifies the packaged Schwartz functions. -/
  classical
  let := A.frame_mem_atlas
  apply DFunLike.ext
  intro z
  change A.localizedFunction (a • u) z = a • A.localizedFunction u z
  by_cases hz : z ∈ tsupport A.cutoff
  · have hzchart := (A.support_subset hz).1
    have hzframe := (A.support_subset hz).2
    simp only [localizedFunction, ite_eq_left hzchart, sectionInChart,
      Submodule.coe_smul, Pi.smul_apply]
    have hlinear := (A.frame.linearEquivAt ℂ (c.symm z) hzframe).map_smul
      a (u.val (c.symm z))
    simp only [Trivialization.linearEquivAt_apply] at hlinear
    rw [hlinear, smul_comm]
  · simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]

/-- Extension respects addition through the inverse complex-linear frame. -/
theorem extend_add (u v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    A.extend hc (u + v) = A.extend hc u + A.extend hc v := by
  /- The chart-source branch uses the additive map frame.symmL followed by scalar
  multiplication; the other branch is zero. Equality at every point gives equality
  of the underlying dependent functions and hence of smooth sections. -/
  classical
  apply Subtype.ext
  funext x
  change A.extendedFunction (u + v) x = A.extendedFunction u x + A.extendedFunction v x
  by_cases hx : x ∈ c.source
  · simp [extendedFunction, hx, map_add, smul_add]
  · simp [extendedFunction, hx]

/-- Extension respects complex scalar multiplication. -/
theorem extend_smul (a : ℂ)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    A.extend hc (a • v) = a • A.extend hc v := by
  /- In the chart source, use complex linearity of symmL and commute the scalar
  factors. Outside the source both sections vanish. Subtype extensionality passes
  from the pointwise formula to the actual smooth section space. -/
  classical
  apply Subtype.ext
  funext x
  change A.extendedFunction (a • v) x = a • A.extendedFunction v x
  by_cases hx : x ∈ c.source
  · simp [extendedFunction, hx, map_smul, smul_comm (A.cutoff (c x) : ℂ) a]
  · simp [extendedFunction, hx]

/-- Localization as the complex-linear map specified by the explicit coordinate formula. -/
def localizeLinearMap : smoothSections (n := n) (r := r) E →ₗ[ℂ]
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) where
  toFun := A.localize hc
  map_add' := A.localize_add hc
  map_smul' := A.localize_smul hc

/-- Cutoff extension as a complex-linear map to the actual smooth section space. -/
def extendLinearMap : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →ₗ[ℂ]
    smoothSections (n := n) (r := r) E where
  toFun := A.extend hc
  map_add' := A.extend_add hc
  map_smul' := A.extend_smul hc

/-- The round trip is cutoff squared; these two maps are not unqualified inverses. -/
theorem localize_extend_apply
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (z : EuclideanSpace ℝ (Fin n)) :
    A.localize hc (A.extend hc v) z = (A.cutoff z : ℂ) ^ 2 • v z := by
  /- On the cutoff support, the chart and inverse chart cancel, as do the forward
  frame and symmL on the valid fiber. Each construction contributes one cutoff.
  Off that support the cutoff is zero, so both sides vanish even outside the target. -/
  classical
  let := A.frame_mem_atlas
  by_cases hz : z ∈ tsupport A.cutoff
  · -- Both chart cancellations occur at the same supported point and in the same frame.
    have hzchart := (A.support_subset hz).1
    have hzframe := (A.support_subset hz).2
    have hxsource := c.map_target hzchart
    have hforward := c.right_inv hzchart
    change A.localizedFunction (A.extend hc v) z = _
    simp only [localizedFunction, ite_eq_left hzchart, sectionInChart, extend,
      extendedFunction, ite_eq_left hxsource, hforward]
    change (A.cutoff z : ℂ) • (A.frame.linearEquivAt ℂ (c.symm z) hzframe)
      ((A.cutoff z : ℂ) • A.frame.symmL ℂ (c.symm z) (v z)) = _
    rw [map_smul, A.frame.symmL_apply hzframe]
    change (A.cutoff z : ℂ) • ((A.cutoff z : ℂ) •
      (A.frame.linearEquivAt ℂ (c.symm z) hzframe)
        ((A.frame.linearEquivAt ℂ (c.symm z) hzframe).symm (v z))) = _
    simp only [LinearEquiv.apply_symm_apply, smul_smul, pow_two]
  · -- Off support both cutoff factors and the localized value vanish.
    change A.localizedFunction (A.extend hc v) z = _
    simp [localizedFunction, image_eq_zero_of_notMem_tsupport hz]

end BundleChartCutoff

end AtiyahSinger
