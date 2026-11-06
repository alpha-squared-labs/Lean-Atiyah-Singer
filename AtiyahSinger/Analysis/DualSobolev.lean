/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SobolevDuality
public import AtiyahSinger.Geometry.DualSections

import AtiyahSinger.Analysis.SobolevEvaluationLocal
import AtiyahSinger.Analysis.SobolevMultiplication
import AtiyahSinger.Geometry.DualBundle

/-!
# Sobolev spaces of the actual dual bundle and bilinear duality

Public module ID: M0445.

A01/SR03, Spin Geometry III.2.14 and 2.15(2). Localized covector coefficients give
an independent Bessel-coordinate completion of smooth E* sections. Neither this
completion nor its bilinear perfect pairing requires a Hermitian bundle metric.
The last section identifies it with the earlier Hermitian version, preserving
the actual same-point integral and the conjugate-linear metric identification.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The cutoff dual coefficients, explicitly extended by zero outside the chart. -/
def localizedDualFunction (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin r) := by
  classical
  letI := A.frame_mem_atlas j
  exact if z ∈ (A.chart j).target then
    (A.cutoff j ((A.chart j).symm z) : ℂ) •
      dualSectionInFrame E (A.frame j) α.val ((A.chart j).symm z)
  else 0


set_option linter.unusedSectionVars false in
/-- Localized dual coefficients are smooth functions on the whole coordinate space. -/
theorem contDiff_localizedDualFunction (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E) :
    ContDiff ℝ ∞ (A.localizedDualFunction j α) := by
  /- On the chart/frame overlap use smooth dual coefficients and the smooth cutoff.
  The support of the cutoff is compactly contained in that overlap. Its coordinate
  image is compact, and the zero extension vanishes locally outside this image.
  These neighborhoods establish real smoothness across the boundary as well. -/
  classical
  let c := A.chart j
  let K := c '' tsupport (A.cutoff j)
  have hcompact : IsCompact K :=
    (A.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ K
  · -- On the supported overlap, differentiate the original covector coefficients.
    obtain ⟨x, hx, rfl⟩ := hz
    have hxsource := (A.support_subset j hx).1
    have htarget : c x ∈ c.target := c.map_source hxsource
    have hframe : c.symm (c x) ∈ (A.frame j).baseSet := by
      rw [c.left_inv hxsource]
      exact (A.support_subset j hx).2
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (A.chart_mem_atlas j)) htarget
    have hsection := (α.property (A.frame j) (A.frame_mem_atlas j)).contMDiffAt
      ((A.frame j).open_baseSet.mem_nhds hframe)
    have hcoords := hsection.comp (c x) hchart
    have hcut := (A.smooth_cutoff j).contMDiffAt.comp (c x) hchart
    have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
    have hlocal := hscalar.contDiffAt.smul hcoords.contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds htarget] with y hy
    change y ∈ (A.chart j).target at hy
    simp [localizedDualFunction, hy, c]
  · -- The same zero extension vanishes near every point outside the compact support image.
    apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
    by_cases htarget : y ∈ c.target
    · have hcut : c.symm y ∉ tsupport (A.cutoff j) := by
        intro hmem
        exact hy ⟨c.symm y, hmem, c.right_inv htarget⟩
      simp [localizedDualFunction, c, image_eq_zero_of_notMem_tsupport hcut]
    · simp [localizedDualFunction, c, htarget]


set_option linter.unusedSectionVars false in
/-- Every localized dual section has compact support with a bound independent of the section. -/
theorem tsupport_localizedDualFunction_subset (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E) :
    tsupport (A.localizedDualFunction j α) ⊆ (A.chart j) '' tsupport (A.cutoff j) := by
  /- Off the compact coordinate image of the cutoff support the function vanishes.
  That image is closed in Euclidean space, so it also contains the closure of the
  nonzero locus. The zero extension gives the assertion outside the chart target. -/
  classical
  -- Compactness of the fixed support image allows us to pass from support to tsupport.
  have hcompact : IsCompact ((A.chart j) '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  apply closure_minimal ?_ hcompact.isClosed
  intro z hz
  have htarget : z ∈ (A.chart j).target := by
    by_contra houtside
    exact hz (by simp [localizedDualFunction, houtside])
  have hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j) := by
    by_contra houtside
    exact hz (by simp [localizedDualFunction, image_eq_zero_of_notMem_tsupport houtside])
  exact ⟨(A.chart j).symm z, hcut, (A.chart j).right_inv htarget⟩

/-- Compact support permits the usual Schwartz-function packaging. -/
theorem hasCompactSupport_localizedDualFunction (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E) :
    HasCompactSupport (A.localizedDualFunction j α) := by
  /- The preceding support bound lies in the compact image of the cutoff support.
  The chart is continuous there. The closed topological support is therefore compact. -/
  have hcompact : IsCompact ((A.chart j) '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  exact hcompact.of_isClosed_subset (isClosed_tsupport _)
    (A.tsupport_localizedDualFunction_subset j α)

/-- The actual Schwartz function of localized dual coefficients. -/
def localizeDual (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (A.hasCompactSupport_localizedDualFunction j α).toSchwartzMap
    (A.contDiff_localizedDualFunction j α)

/-- Dual localization is additive. -/
theorem localizeDual_add (j : Fin A.size)
    (α β : smoothDualSections (n := n) (r := r) E) :
    A.localizeDual j (α + β) = A.localizeDual j α + A.localizeDual j β := by
  /- Evaluate on every basis vector. Addition of covectors and scalar cutoff
  multiplication distribute. Outside the chart target both sides vanish, giving
  equality of functions and hence of their Schwartz-map packages. -/
  classical
  let := A.frame_mem_atlas j
  apply DFunLike.ext
  intro z
  change A.localizedDualFunction j (α + β) z =
    A.localizedDualFunction j α z + A.localizedDualFunction j β z
  by_cases htarget : z ∈ (A.chart j).target
  · have hadd :
        dualSectionInFrame E (A.frame j) (α + β).val ((A.chart j).symm z) =
          dualSectionInFrame E (A.frame j) α.val ((A.chart j).symm z) +
            dualSectionInFrame E (A.frame j) β.val ((A.chart j).symm z) := by
      ext i
      rfl
    simp only [localizedDualFunction, ite_eq_left htarget, hadd, smul_add]
  · simp [localizedDualFunction, htarget]

/-- Dual localization is complex-linear, with no conjugation of the scalar. -/
theorem localizeDual_smul (j : Fin A.size) (c : ℂ)
    (α : smoothDualSections (n := n) (r := r) E) :
    A.localizeDual j (c • α) = c • A.localizeDual j α := by
  /- Covector evaluation is linear in the covector, so each coordinate is multiplied
  by c. This commutes with the real cutoff and the zero extension. Use extensionality. -/
  classical
  let := A.frame_mem_atlas j
  apply DFunLike.ext
  intro z
  change A.localizedDualFunction j (c • α) z = c • A.localizedDualFunction j α z
  by_cases htarget : z ∈ (A.chart j).target
  · have hsmul :
        dualSectionInFrame E (A.frame j) (c • α).val ((A.chart j).symm z) =
          c • dualSectionInFrame E (A.frame j) α.val ((A.chart j).symm z) := by
      ext i
      rfl
    simp only [localizedDualFunction, ite_eq_left htarget, hsmul]
    exact smul_comm _ _ _
  · simp [localizedDualFunction, htarget]

/-- Dual localization packaged as its actual complex-linear map. -/
def localizeDualLinearMap (j : Fin A.size) :
    smoothDualSections (n := n) (r := r) E →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) where
  toFun := A.localizeDual j
  map_add' := A.localizeDual_add j
  map_smul' := A.localizeDual_smul j

/-- The tuple of Bessel coordinates of the localized dual coefficients. -/
def dualSobolevCoordinates (s : ℝ) :
    smoothDualSections (n := n) (r := r) E →ₗ[ℂ] A.SobolevCoordinates :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (LinearMap.pi fun j ↦
      (schwartzSobolevCoordinateLinearMap n r s).comp (A.localizeDualLinearMap j))

/-- The real-order Sobolev completion of actual smooth dual sections. -/
abbrev DualSobolevSpace (s : ℝ) : Type :=
  (A.dualSobolevCoordinates s).range.topologicalClosure

/-- The canonical dense map from actual smooth covector sections into their completion. -/
def dualSmoothToSobolev (s : ℝ) :
    smoothDualSections (n := n) (r := r) E →ₗ[ℂ] A.DualSobolevSpace s :=
  (Submodule.inclusion (A.dualSobolevCoordinates s).range.le_topologicalClosure).comp
    (A.dualSobolevCoordinates s).rangeRestrict

/-- The completion map does not identify different smooth covector sections. -/
theorem dualSmoothToSobolev_injective (s : ℝ) :
    Function.Injective (A.dualSmoothToSobolev s) := by
  /- Cancel each invertible Bessel weight to recover the localized smooth dual
  coefficients. Equality of these coefficients gives equality of the cutoff covectors.
  Sum the partition of unity to recover equality of the original covector sections. -/
  classical
  intro α β hαβ
  -- Recover each original localized covector from its Bessel L² coordinate.
  have hlocal (j : Fin A.size) : A.localizeDual j α = A.localizeDual j β := by
    have hcoord := congrArg (fun f : A.DualSobolevSpace s ↦ f.val j) hαβ
    change schwartzSobolevCoordinate s (A.localizeDual j α) =
      schwartzSobolevCoordinate s (A.localizeDual j β) at hcoord
    have hdist := congrArg (besselRealization n r s) hcoord
    rw [besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate] at hdist
    apply (SchwartzMap.injective_toLp 2 volume)
    apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
    change ((A.localizeDual j α).toLp 2 volume :
        𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) =
      ((A.localizeDual j β).toLp 2 volume :
        𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    simpa only [Lp.toTemperedDistribution_toLp_eq] using hdist
  apply Subtype.ext
  funext x
  -- A genuine dual frame identifies cutoff covectors only on its valid base set.
  have hcut (j : Fin A.size) :
      (A.cutoff j x : ℂ) • α.val x = (A.cutoff j x : ℂ) • β.val x := by
    by_cases hx : x ∈ tsupport (A.cutoff j)
    · let := A.frame_mem_atlas j
      have hsource := (A.support_subset j hx).1
      have hframe := (A.support_subset j hx).2
      have hcoords := congrArg (fun f ↦ f ((A.chart j) x)) (hlocal j)
      change A.localizedDualFunction j α ((A.chart j) x) =
        A.localizedDualFunction j β ((A.chart j) x) at hcoords
      simp only [localizedDualFunction, ite_eq_left ((A.chart j).map_source hsource),
        (A.chart j).left_inv hsource] at hcoords
      have hdualframe : x ∈ (dualFrame E (A.frame j)).baseSet := by
        simpa only [dualFrame_baseSet] using hframe
      apply ((dualFrame E (A.frame j)).linearEquivAt ℂ x hdualframe).injective
      rw [map_smul, map_smul]
      change (A.cutoff j x : ℂ) • (dualFrame E (A.frame j) ⟨x, α.val x⟩).2 =
        (A.cutoff j x : ℂ) • (dualFrame E (A.frame j) ⟨x, β.val x⟩).2
      rw [dualFrame_apply_snd E (A.frame j) α.val x hframe,
        dualFrame_apply_snd E (A.frame j) β.val x hframe]
      exact hcoords
    · apply ContinuousLinearMap.ext
      intro v
      simp [image_eq_zero_of_notMem_tsupport hx]
  -- The supplied partition sums to one in the original covector fibers.
  have hsum : ∑ j, (A.cutoff j x : ℂ) = 1 := by exact_mod_cast A.sum_cutoff x
  apply ContinuousLinearMap.ext
  intro v
  have heval (j : Fin A.size) :
      (A.cutoff j x : ℂ) * α.val x v = (A.cutoff j x : ℂ) * β.val x v := by
    exact congrArg (fun f : DualBundle E x ↦ f v) (hcut j)
  calc
    α.val x v = (∑ j, (A.cutoff j x : ℂ)) * α.val x v := by rw [hsum, one_mul]
    _ = ∑ j, (A.cutoff j x : ℂ) * α.val x v := Finset.sum_mul _ _ _
    _ = ∑ j, (A.cutoff j x : ℂ) * β.val x v := Finset.sum_congr rfl (fun j _ ↦ heval j)
    _ = (∑ j, (A.cutoff j x : ℂ)) * β.val x v := (Finset.sum_mul _ _ _).symm
    _ = β.val x v := by rw [hsum, one_mul]

/-- Smooth dual sections are dense in the stated closed-range completion. -/
theorem denseRange_dualSmoothToSobolev (s : ℝ) : DenseRange (A.dualSmoothToSobolev s) := by
  /- Its range is the original linear coordinate range, viewed in its own closure.
  The defining property of topological closure gives precisely the claimed density. -/
  have hdense : DenseRange
      (Set.inclusion (A.dualSobolevCoordinates s).range.le_topologicalClosure) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact hdense.comp (A.dualSobolevCoordinates s).surjective_rangeRestrict.denseRange
    (continuous_inclusion _)

/-- The dual Sobolev norm is the finite square sum of the explicit local Bessel norms. -/
theorem norm_dualSmoothToSobolev_sq (s : ℝ)
    (α : smoothDualSections (n := n) (r := r) E) :
    ‖A.dualSmoothToSobolev s α‖ ^ 2 =
      ∑ j, ‖schwartzSobolevCoordinate s (A.localizeDual j α)‖ ^ 2 := by
  /- The subspace norm is inherited from the finite PiLp 2 space. Unfold the
  coordinate map and use the square-sum formula for that norm at its explicit entries. -/
  exact PiLp.norm_sq_eq_of_L2 _ (A.dualSobolevCoordinates s α)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1000000 in
-- Both dense extensions and the local reconstruction elaborate in this single proof.
/-- SG III.2.15(2): the same-point bilinear integral extends to a perfect opposite-order pairing. -/
theorem existsUnique_sobolevEvaluationDuality (s : ℝ) :
    ∃! T : A.DualSobolevSpace (-s) ≃L[ℂ] StrongDual ℂ (A.SobolevSpace s),
      ∀ (α : smoothDualSections (n := n) (r := r) E)
        (u : smoothSections (n := n) (r := r) E),
        T (A.dualSmoothToSobolev (-s) α) (A.smoothToSobolev s u) =
          smoothDualSectionPairing E μ α u := by
  open Set in
  open scoped ComplexConjugate FourierTransform ENNReal in
  /- Extend the actual local Fourier pairings and sum the original partition.
  Riesz representation in the specified closed coordinate subspace supplies local
  L² vectors; inverse-density extension reconstructs their global covector.
  Local tests recover every original covector coordinate and prove injectivity. -/
  classical
  -- The local bilinear pairing is Hermitian pairing after actual conjugation.
  have hconjugation :
      ∃ C : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℝ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        (∀ u x i, C u x i = conj (u x i)) ∧
        ∀ t u, ‖schwartzSobolevCoordinate t (C u)‖ =
          ‖schwartzSobolevCoordinate t u‖ := by
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let c : V →L[ℝ] V :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun i ↦ Complex.conjCLE.toContinuousLinearMap.comp
          ((EuclideanSpace.proj i).restrictScalars ℝ)))
    have hc (v : V) (i : Fin r) : c v i = conj (v i) := rfl
    have hcc (v : V) : c (c v) = v := by
      ext i
      simp only [hc, starRingEnd_self_apply]
    let e : V ≃L[ℝ] V :=
      { toFun := c
        invFun := c
        left_inv := hcc
        right_inv := hcc
        map_add' := c.map_add
        map_smul' := c.map_smul
        continuous_toFun := c.continuous
        continuous_invFun := c.continuous }
    let C : 𝓢(X, V) →L[ℝ] 𝓢(X, V) := SchwartzMap.postcompCLM c
    have hC (u : 𝓢(X, V)) (x : X) : C u x = c (u x) := rfl
    have hcnorm (v : V) : ‖c v‖ = ‖v‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [hc, Complex.norm_conj]
    have hfourier (u : 𝓢(X, V)) (ξ : X) : 𝓕 (C u) ξ = c (𝓕 u (-ξ)) := by
      change 𝓕 (fun x ↦ c (u x)) ξ = e (𝓕 (u : X → V) (-ξ))
      simp only [Real.fourier_eq, inner_neg_right, neg_neg]
      rw [← e.integral_comp_comm]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply PiLp.ext
      intro i
      change (Real.fourierChar (-inner ℝ x ξ) : ℂ) * conj (u x i) =
        conj ((Real.fourierChar (inner ℝ x ξ) : ℂ) * u x i)
      rw [map_mul, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
    refine ⟨C, fun _ _ _ ↦ rfl, ?_⟩
    intro s u
    let w : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
    have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
    have hnorm (v : 𝓢(X, V)) : ‖schwartzSobolevCoordinate s v‖ =
        ‖(SchwartzMap.smulLeftCLM V w (𝓕 v)).toLp 2‖ := by
      unfold schwartzSobolevCoordinate
      rw [← SchwartzMap.norm_fourier_toL2_eq, SchwartzMap.fourierMultiplierCLM_apply,
        FourierTransform.fourier_fourierInv_eq]
    rw [hnorm, hnorm]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num),
      SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    congr 1
    have hpoint (ξ : X) : ‖SchwartzMap.smulLeftCLM V w (𝓕 (C u)) ξ‖ =
        ‖SchwartzMap.smulLeftCLM V w (𝓕 u) (-ξ)‖ := by
      simp only [SchwartzMap.smulLeftCLM_apply_apply hw, hfourier, norm_smul, hcnorm]
      simp [w]
    simp_rw [hpoint]
    exact integral_neg_eq_self
      (fun ξ : X ↦ ‖SchwartzMap.smulLeftCLM V w (𝓕 u) ξ‖ ^ (2 : ℝ≥0∞).toReal)
      (volume : Measure X)
  obtain ⟨C, hC, hCnorm⟩ := hconjugation
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  -- The induced dual presentation has precisely the original covector coordinates.
  let Ad : SmoothBundlePresentation (n := n) (r := r) (DualBundle E) :=
    { size := A.size
      chart := A.chart
      chart_mem_atlas := A.chart_mem_atlas
      frame j := by
        letI := A.frame_mem_atlas j
        exact dualFrame E (A.frame j)
      frame_mem_atlas j := by
        let := A.frame_mem_atlas j
        exact memTrivializationAtlas_dualFrame E (A.frame j)
      cutoff := A.cutoff
      smooth_cutoff := A.smooth_cutoff
      cutoff_nonneg := A.cutoff_nonneg
      compact_support := A.compact_support
      support_subset j := by
        let := A.frame_mem_atlas j
        simpa only [dualFrame_baseSet] using A.support_subset j
      sum_cutoff := A.sum_cutoff }
  have hAdlocal (j : Fin A.size) (α : smoothDualSections (n := n) (r := r) E) :
      Ad.localize j (dualSectionsEquiv E α) = A.localizeDual j α := by
    let := A.frame_mem_atlas j
    apply SchwartzMap.ext
    intro z
    change (if z ∈ (A.chart j).target then
        (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (dualFrame E (A.frame j) ⟨(A.chart j).symm z, α.val ((A.chart j).symm z)⟩).2
        else 0) = A.localizedDualFunction j α z
    by_cases hz : z ∈ (A.chart j).target
    · by_cases hx : (A.chart j).symm z ∈ tsupport (A.cutoff j)
      · simp only [localizedDualFunction, ite_eq_left hz]
        rw [dualFrame_apply_snd E (A.frame j) α.val _ (A.support_subset j hx).2]
      · simp [localizedDualFunction, image_eq_zero_of_notMem_tsupport hx]
    · simp [localizedDualFunction, hz]
  have hAdnorm (t : ℝ) (α : smoothDualSections (n := n) (r := r) E) :
      ‖Ad.smoothToSobolev t (dualSectionsEquiv E α)‖ = ‖A.dualSmoothToSobolev t α‖ := by
    change ‖Ad.sobolevCoordinates t (dualSectionsEquiv E α)‖ =
      ‖A.dualSobolevCoordinates t α‖
    congr 1
    apply PiLp.ext
    intro j
    change schwartzSobolevCoordinate t (Ad.localize j (dualSectionsEquiv E α)) =
      schwartzSobolevCoordinate t (A.localizeDual j α)
    rw [hAdlocal]
  -- Each original cutoff receives a plateau within its own chart/frame overlap.
  let U (j : Fin A.size) :=
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.frame j).baseSet
  let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
  have hU (j : Fin A.size) : IsOpen (U j) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage
      (A.chart j).open_target (A.frame j).open_baseSet
  have hK (j : Fin A.size) : IsCompact (K j) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  have hKU (j : Fin A.size) : K j ⊆ U j := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := (A.support_subset j hx).1
    exact ⟨(A.chart j).map_source hs, by
      change (A.chart j).symm ((A.chart j) x) ∈ (A.frame j).baseSet
      rw [(A.chart j).left_inv hs]
      exact (A.support_subset j hx).2⟩
  have hplateau (j : Fin A.size) : ∃ η : X → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U j ∧
        ∀ z ∈ K j, η z = 1 := by
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hU j) (hKU j)
    obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo (hK j).isClosed hKO
    have hs : tsupport η = closure O := congrArg closure hsη
    refine ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs], ?_⟩
    exact fun z hz ↦ (honeη z).mp hz
  choose η hη hcη hsη honeη using hplateau
  let κ (j : Fin A.size) (z : X) := η j z * A.cutoff j ((A.chart j).symm z)
  have hκ (j : Fin A.size) : ContDiff ℝ ∞ (κ j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport (η j)
    · have hzt := (hsη j hz).1
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
          (A.chart_mem_atlas j)) hzt
      exact (hη j).contDiffAt.mul
        ((A.smooth_cutoff j).contMDiffAt.comp z hchart).contDiffAt
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (η j)).isOpen_compl.mem_nhds hz] with y hy
      simp [κ, image_eq_zero_of_notMem_tsupport hy]
  have hsκ (j : Fin A.size) : tsupport (κ j) ⊆ K j := by
    apply closure_minimal ?_ (hK j).isClosed
    intro z hz
    have hηz : η j z ≠ 0 := left_ne_zero_of_mul (show κ j z ≠ 0 from hz)
    have hχz : A.cutoff j ((A.chart j).symm z) ≠ 0 :=
      right_ne_zero_of_mul (show κ j z ≠ 0 from hz)
    have hzt := (hsη j (subset_tsupport _ hηz)).1
    exact ⟨(A.chart j).symm z, subset_tsupport _ hχz, (A.chart j).right_inv hzt⟩
  have hcκ (j : Fin A.size) : HasCompactSupport (κ j) :=
    (hK j).of_isClosed_subset (isClosed_tsupport _) (hsκ j)
  have hκtarget (j : Fin A.size) (z : X) (hz : z ∈ (A.chart j).target) :
      κ j z = A.cutoff j ((A.chart j).symm z) := by
    by_cases hχ : A.cutoff j ((A.chart j).symm z) = 0
    · simp [κ, hχ]
    · have hzK : z ∈ K j :=
        ⟨(A.chart j).symm z, subset_tsupport _ hχ, (A.chart j).right_inv hz⟩
      simp [κ, honeη j z hzK]
  let L (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
    { frame := A.frame j
      frame_mem_atlas := A.frame_mem_atlas j
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hcκ j
      support_subset := (hsκ j).trans (hKU j) }
  let D (j : Fin A.size) : BundleChartCutoff (r := r) (DualBundle E) (A.chart j) :=
    { frame := Ad.frame j
      frame_mem_atlas := Ad.frame_mem_atlas j
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hcκ j
      support_subset := by
        let := A.frame_mem_atlas j
        simpa only [Ad, dualFrame_baseSet] using (hsκ j).trans (hKU j) }
  let B (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
    { frame := A.frame j
      frame_mem_atlas := A.frame_mem_atlas j
      cutoff := η j
      smooth_cutoff := hη j
      compact_support := hcη j
      support_subset := hsη j }
  have hLlocal (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
      (L j).localize (A.chart_mem_atlas j) u = A.localize j u := by
    apply SchwartzMap.ext
    intro z
    change (if z ∈ (A.chart j).target then
      (κ j z : ℂ) • sectionInChart E (A.chart j) (A.frame j) u.val z else 0) = _
    by_cases hz : z ∈ (A.chart j).target
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction,
        hz, hκtarget j z hz]
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction, hz]
  have hDlocal (j : Fin A.size) (α : smoothDualSections (n := n) (r := r) E) :
      (D j).localize (A.chart_mem_atlas j) (dualSectionsEquiv E α) =
        A.localizeDual j α := by
    rw [← hAdlocal]
    apply SchwartzMap.ext
    intro z
    change (if z ∈ (A.chart j).target then
      (κ j z : ℂ) • sectionInChart (DualBundle E) (A.chart j) (Ad.frame j)
        (dualSectionsEquiv E α).val z else 0) = _
    by_cases hz : z ∈ (A.chart j).target
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction,
        hz, hκtarget j z hz, Ad]
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction, hz, Ad]
  choose ρ hρ hρpos hρmap using
    (fun j : Fin A.size ↦ IsSmoothPositiveMeasure.exists_smooth_density
      (μ := μ) (A.chart j) (A.chart_mem_atlas j))
  let W (j : Fin A.size) : X → V →L[ℂ] V :=
    cutoffMatrix (η j) (fun z ↦ ρ j z • ContinuousLinearMap.id ℂ V)
  let R (j : Fin A.size) : X → V →L[ℂ] V :=
    cutoffMatrix (η j) (fun z ↦ (ρ j z)⁻¹ • ContinuousLinearMap.id ℂ V)
  have hW (j : Fin A.size) : ContDiff ℝ ∞ (W j) :=
    contDiff_cutoffMatrix (A.chart j).target (A.chart j).open_target _
      ((hρ j).smul contDiffOn_const) (η j) (hη j) (fun z hz ↦ (hsη j hz).1)
  have hR (j : Fin A.size) : ContDiff ℝ ∞ (R j) :=
    contDiff_cutoffMatrix (A.chart j).target (A.chart j).open_target _
      (((hρ j).inv (fun z hz ↦ (hρpos j z hz).ne')).smul contDiffOn_const)
      (η j) (hη j) (fun z hz ↦ (hsη j hz).1)
  have hcW (j : Fin A.size) : HasCompactSupport (W j) :=
    hasCompactSupport_cutoffMatrix (η j) _ (hcη j)
  have hcR (j : Fin A.size) : HasCompactSupport (R j) :=
    hasCompactSupport_cutoffMatrix (η j) _ (hcη j)
  -- Conjugation is semilinear, and its Bessel-coordinate realization is bounded.
  let Cₗ : 𝓢(X, V) →ₗ⋆[ℂ] 𝓢(X, V) :=
    { toFun := C
      map_add' := C.map_add
      map_smul' := by
        intro a v
        apply SchwartzMap.ext
        intro z
        apply PiLp.ext
        intro i
        simp [hC, map_mul] }
  let C₀ := (schwartzSobolevCoordinateLinearMap n r (-s)).comp Cₗ
  let C₁ := C₀.extendOfNorm (schwartzSobolevCoordinateLinearMap n r (-s))
  have hC₁ (v : 𝓢(X, V)) : C₁ (schwartzSobolevCoordinate (-s) v) =
      schwartzSobolevCoordinate (-s) (C v) :=
    C₀.extendOfNorm_eq (denseRange_schwartzSobolevCoordinate n r (-s))
      ⟨1, fun v ↦ by
        change ‖schwartzSobolevCoordinate (-s) (C v)‖ ≤
          1 * ‖schwartzSobolevCoordinate (-s) v‖
        rw [one_mul]
        exact (hCnorm (-s) v).le⟩ v
  let F (j : Fin A.size) : smoothSections (n := n) (r := r) E →ₗ[ℂ] Lp V 2 volume :=
    (schwartzSobolevCoordinateLinearMap n r s).comp
      ((matrixMultiplierCLM (W j) (hW j) (hcW j)).toLinearMap.comp
        ((B j).localizeLinearMap (A.chart_mem_atlas j)))
  have hFbound (j : Fin A.size) : ∃ c : ℝ, ∀ u, ‖F j u‖ ≤ c * ‖A.smoothToSobolev s u‖ := by
    obtain ⟨a, ha, hba⟩ := (B j).exists_norm_localize_sobolev_le (A.chart_mem_atlas j) A s
    obtain ⟨b, hb, hbb⟩ := exists_norm_matrixMultiplier_sobolev_le (W j) (hW j) (hcW j) s
    refine ⟨b * a, fun u ↦ ?_⟩
    exact (hbb ((B j).localize (A.chart_mem_atlas j) u)).trans
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hba u) hb)
  let F₁ (j : Fin A.size) : A.SobolevSpace s →L[ℂ] Lp V 2 volume :=
    (F j).extendOfNorm (A.smoothToSobolev s)
  have hF₁ (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
      F₁ j (A.smoothToSobolev s u) = F j u :=
    (F j).extendOfNorm_eq (A.denseRange_smoothToSobolev s) (hFbound j) u
  let d (j : Fin A.size) : A.DualSobolevSpace (-s) →L[ℂ] Lp V 2 volume :=
    (PiLp.proj 2 _ j).comp (A.dualSobolevCoordinates (-s)).range.topologicalClosure.subtypeL
  let e (j : Fin A.size) : A.SobolevSpace s →L[ℂ] Lp V 2 volume :=
    (PiLp.proj 2 _ j).comp (A.sobolevCoordinates s).range.topologicalClosure.subtypeL
  let T : A.DualSobolevSpace (-s) →L[ℂ] StrongDual ℂ (A.SobolevSpace s) :=
    ∑ j, ((ContinuousLinearMap.compL ℂ (A.SobolevSpace s) (Lp V 2 volume) ℂ).flip
      (F₁ j)).comp (((innerSL ℂ).comp C₁).comp (d j))
  have hT (α : A.DualSobolevSpace (-s)) (u : A.SobolevSpace s) :
      T α u = ∑ j, inner ℂ (C₁ (d j α)) (F₁ j u) := by
    simp [T]
  have hCinner (v w : 𝓢(X, V)) (z : X) :
      inner ℂ (C v z) (w z) = ∑ i, v z i * w z i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, hC, mul_comm]
  -- The extension/localization pair reconstructs each original partition summand.
  have hpiece (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) (x : M) :
      ((L j).extend (A.chart_mem_atlas j) ((B j).localize (A.chart_mem_atlas j) u)).val x =
        (A.cutoff j x : ℂ) • u.val x := by
    let := A.frame_mem_atlas j
    change (if x ∈ (A.chart j).source then
      (κ j ((A.chart j) x) : ℂ) • (A.frame j).symmL ℂ x
        ((B j).localizedFunction u ((A.chart j) x)) else 0) = _
    by_cases hx : x ∈ (A.chart j).source
    · simp only [ite_eq_left hx, hκtarget j _ ((A.chart j).map_source hx),
        (A.chart j).left_inv hx, BundleChartCutoff.localizedFunction,
        ite_eq_left ((A.chart j).map_source hx)]
      by_cases hχ : A.cutoff j x = 0
      · simp [hχ]
      have hxK : (A.chart j) x ∈ K j := ⟨x, subset_tsupport _ hχ, rfl⟩
      have hxe := (A.support_subset j (subset_tsupport _ hχ)).2
      change (A.cutoff j x : ℂ) • (A.frame j).symmL ℂ x
        ((η j ((A.chart j) x) : ℂ) • sectionInChart E (A.chart j) (A.frame j) u.val
          ((A.chart j) x)) = _
      rw [honeη j _ hxK]
      simp only [Complex.ofReal_one, one_smul, sectionInChart]
      have hpoint : (⟨(A.chart j).symm ((A.chart j) x),
          u.val ((A.chart j).symm ((A.chart j) x))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, u.val x⟩ :=
        congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          ((A.chart j).left_inv hx)
      rw [hpoint]
      rw [← (A.frame j).continuousLinearMapAt_apply_of_mem ℂ hxe,
        (A.frame j).symmL_continuousLinearMapAt hxe]
    · have hχ : A.cutoff j x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hxK ↦ hx (A.support_subset j hxK).1)
      simp [hx, hχ]
  have hsum (u : smoothSections (n := n) (r := r) E) :
      ∑ j, (L j).extend (A.chart_mem_atlas j) ((B j).localize (A.chart_mem_atlas j) u) = u := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply, hpiece]
    rw [← Finset.sum_smul]
    have hχ : ∑ j, (A.cutoff j x : ℂ) = 1 := by exact_mod_cast A.sum_cutoff x
    rw [hχ, one_smul]
  have hpairingSum (α : smoothDualSections (n := n) (r := r) E)
      (u : smoothSections (n := n) (r := r) E) :
      smoothDualSectionPairing E μ α u = ∑ j, ∫ z, ρ j z •
        ∑ i, A.localizeDual j α z i * (B j).localize (A.chart_mem_atlas j) u z i := by
    let uj (j : Fin A.size) :=
      (L j).extend (A.chart_mem_atlas j) ((B j).localize (A.chart_mem_atlas j) u)
    calc
      _ = ∫ x, ∑ j, α.val x ((uj j).val x) ∂μ := by
        unfold smoothDualSectionPairing
        apply integral_congr_ae
        filter_upwards [] with x
        have hpoint := congrArg (fun v : smoothSections (n := n) (r := r) E ↦ v.val x) (hsum u)
        rw [← hpoint]
        simp only [Submodule.coe_sum, Finset.sum_apply, map_sum, uj]
      _ = ∑ j, ∫ x, α.val x ((uj j).val x) ∂μ :=
        integral_finsetSum _ (fun j _ ↦ integrable_dualSection_eval E μ α (uj j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        have h := (L j).integral_extendDual_eq (D j) (A.chart_mem_atlas j) rfl rfl μ (ρ j)
          (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j)
          (dualSectionsEquiv E α) ((B j).localize (A.chart_mem_atlas j) u)
        rw [hDlocal] at h
        exact h
  have hT_smooth (α : smoothDualSections (n := n) (r := r) E)
      (u : smoothSections (n := n) (r := r) E) :
      T (A.dualSmoothToSobolev (-s) α) (A.smoothToSobolev s u) =
        smoothDualSectionPairing E μ α u := by
    rw [hT, hpairingSum]
    apply Finset.sum_congr rfl
    intro j _
    change inner ℂ (C₁ (schwartzSobolevCoordinate (-s) (A.localizeDual j α)))
      (F₁ j (A.smoothToSobolev s u)) = _
    rw [hC₁, hF₁]
    change inner ℂ (schwartzSobolevCoordinate (-s) (C (A.localizeDual j α)))
      (schwartzSobolevCoordinate s
        (matrixMultiplierCLM (W j) (hW j) (hcW j)
          ((B j).localize (A.chart_mem_atlas j) u))) = _
    have hfourier := sobolev_pairing_schwartz (-s) (C (A.localizeDual j α))
      (matrixMultiplierCLM (W j) (hW j) (hcW j)
        ((B j).localize (A.chart_mem_atlas j) u))
    simp only [neg_neg] at hfourier
    rw [hfourier]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [matrixMultiplierCLM_apply]
    change inner ℂ (C (A.localizeDual j α) z)
      (η j z • (ρ j z • (B j).localize (A.chart_mem_atlas j) u z)) = _
    rw [inner_smul_right_eq_smul, inner_smul_right_eq_smul, hCinner]
    by_cases hz : z ∈ K j
    · rw [honeη j z hz, one_smul]
    · have hzero : A.localizeDual j α z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hz' ↦ hz (A.tsupport_localizedDualFunction_subset j α hz'))
      simp [hzero]
  -- Inverse-density extension recovers the ordinary local pairing on the original support.
  have hdot_smul (t : ℝ) (v w : V) :
      (∑ i, (t • v) i * w i) = t • ∑ i, v i * w i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_mul_assoc t (v i) (w i)
  have hRpoint (j : Fin A.size) (v w : 𝓢(X, V)) (z : X)
      (hw : z ∉ K j → w z = 0) :
      (ρ j z • ∑ i,
        matrixMultiplierCLM (R j) (hR j) (hcR j) (C v) z i * w z i) =
          inner ℂ (v z) (w z) := by
    by_cases hz : z ∈ K j
    · have hρz : ρ j z ≠ 0 := (hρpos j z (hKU j hz).1).ne'
      have hscaled : ρ j z • matrixMultiplierCLM (R j) (hR j) (hcR j) (C v) z =
          C v z := by
        rw [matrixMultiplierCLM_apply]
        change ρ j z • (η j z • ((ρ j z)⁻¹ • C v z)) = _
        rw [honeη j z hz, one_smul, smul_smul, mul_inv_cancel₀ hρz, one_smul]
      rw [← hdot_smul, hscaled]
      rw [← hCinner]
      congr 1
      apply PiLp.ext
      intro i
      simp only [hC, starRingEnd_self_apply]
    · simp [hw hz]
  let G (j : Fin A.size) : 𝓢(X, V) →ₗ⋆[ℂ] A.DualSobolevSpace (-s) :=
    ((A.dualSmoothToSobolev (-s)).comp (dualSectionsEquiv E).symm.toLinearMap).comp
      (((D j).extendLinearMap (A.chart_mem_atlas j)).comp
        ((matrixMultiplierCLM (R j) (hR j) (hcR j)).toLinearMap.comp Cₗ))
  have hGbound (j : Fin A.size) : ∃ c : ℝ,
      ∀ v, ‖G j v‖ ≤ c * ‖schwartzSobolevCoordinate (-s) v‖ := by
    obtain ⟨a, ha, hba⟩ := (D j).exists_norm_extend_sobolev_le (A.chart_mem_atlas j) Ad (-s)
    obtain ⟨b, hb, hbb⟩ := exists_norm_matrixMultiplier_sobolev_le (R j) (hR j) (hcR j) (-s)
    refine ⟨a * b, fun v ↦ ?_⟩
    change ‖A.dualSmoothToSobolev (-s) ((dualSectionsEquiv E).symm
      ((D j).extend (A.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))))‖ ≤ _
    rw [← hAdnorm, LinearEquiv.apply_symm_apply]
    apply (hba _).trans
    have hbv := hbb (C v)
    rw [hCnorm] at hbv
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbv ha
  let G₁ (j : Fin A.size) : Lp V 2 volume →L⋆[ℂ] A.DualSobolevSpace (-s) :=
    (G j).extendOfNorm (schwartzSobolevCoordinateLinearMap n r (-s))
  have hG₁ (j : Fin A.size) (v : 𝓢(X, V)) :
      G₁ j (schwartzSobolevCoordinate (-s) v) = G j v :=
    (G j).extendOfNorm_eq (denseRange_schwartzSobolevCoordinate n r (-s)) (hGbound j) v
  have hGpair_smooth (j : Fin A.size) (v : 𝓢(X, V))
      (u : smoothSections (n := n) (r := r) E) :
      T (G j v) (A.smoothToSobolev s u) =
        inner ℂ (schwartzSobolevCoordinate (-s) v) (e j (A.smoothToSobolev s u)) := by
    change T (A.dualSmoothToSobolev (-s) ((dualSectionsEquiv E).symm
      ((D j).extend (A.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))))) _ = _
    rw [hT_smooth]
    change (∫ x, ((D j).extend (A.chart_mem_atlas j)
      (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))).val x (u.val x) ∂μ) = _
    rw [(L j).integral_dualExtend_eq (D j) (A.chart_mem_atlas j) rfl rfl μ (ρ j)
      (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j), hLlocal]
    change _ = inner ℂ (schwartzSobolevCoordinate (-s) v)
      (schwartzSobolevCoordinate s (A.localize j u))
    have hf := sobolev_pairing_schwartz (-s) v (A.localize j u)
    simp only [neg_neg] at hf
    rw [hf]
    apply integral_congr_ae
    filter_upwards [] with z
    apply hRpoint
    intro hz
    exact image_eq_zero_of_notMem_tsupport
      (fun hz' ↦ hz (A.tsupport_localizedFunction_subset j u hz'))
  have hGpair (j : Fin A.size) (z : Lp V 2 volume) (u : A.SobolevSpace s) :
      T (G₁ j z) u = inner ℂ z (e j u) := by
    have htest (v : 𝓢(X, V)) :
        T (G₁ j (schwartzSobolevCoordinate (-s) v)) u =
          inner ℂ (schwartzSobolevCoordinate (-s) v) (e j u) := by
      rw [hG₁]
      exact (A.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq (T (G j v)).continuous
          (continuous_const.inner (e j).continuous)) (hGpair_smooth j v)
    exact (denseRange_schwartzSobolevCoordinate n r (-s)).induction_on z
      (isClosed_eq ((T.continuous.comp (G₁ j).continuous).clm_apply continuous_const)
        (continuous_id.inner continuous_const)) htest
  have hsurjective : Function.Surjective T := by
    intro f
    let y : A.SobolevSpace s := (InnerProductSpace.toDual ℂ (A.SobolevSpace s)).symm f
    refine ⟨∑ j, G₁ j (e j y), ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    simp only [map_sum, sum_apply, hGpair]
    change (∑ j, inner ℂ (y.val j) (u.val j)) = f u
    rw [← PiLp.inner_apply]
    change inner ℂ y u = f u
    exact InnerProductSpace.toDual_symm_apply
  -- Test each original covector coordinate to establish injectivity.
  let test (j : Fin A.size) (v : 𝓢(X, V)) : smoothSections (n := n) (r := r) E :=
    (L j).extend (A.chart_mem_atlas j) (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))
  have htest_smooth (j : Fin A.size) (v : 𝓢(X, V))
      (α : smoothDualSections (n := n) (r := r) E) :
      T (A.dualSmoothToSobolev (-s) α) (A.smoothToSobolev s (test j v)) =
        inner ℂ (schwartzSobolevCoordinate s v) (d j (A.dualSmoothToSobolev (-s) α)) := by
    rw [hT_smooth]
    change (∫ x, α.val x (((L j).extend (A.chart_mem_atlas j)
      (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))).val x) ∂μ) = _
    have heq := (L j).integral_extendDual_eq (D j) (A.chart_mem_atlas j) rfl rfl μ (ρ j)
      (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j)
      (dualSectionsEquiv E α) (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))
    change (∫ x, α.val x (((L j).extend (A.chart_mem_atlas j)
      (matrixMultiplierCLM (R j) (hR j) (hcR j) (C v))).val x) ∂μ) = _ at heq
    rw [heq, hDlocal]
    change _ = inner ℂ (schwartzSobolevCoordinate s v)
      (schwartzSobolevCoordinate (-s) (A.localizeDual j α))
    rw [sobolev_pairing_schwartz]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [show (∑ i, A.localizeDual j α z i *
        matrixMultiplierCLM (R j) (hR j) (hcR j) (C v) z i) =
        ∑ i, matrixMultiplierCLM (R j) (hR j) (hcR j) (C v) z i *
          A.localizeDual j α z i from Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)]
    apply hRpoint
    intro hz
    exact image_eq_zero_of_notMem_tsupport
      (fun hz' ↦ hz (A.tsupport_localizedDualFunction_subset j α hz'))
  have htest (j : Fin A.size) (v : 𝓢(X, V)) (α : A.DualSobolevSpace (-s)) :
      T α (A.smoothToSobolev s (test j v)) =
        inner ℂ (schwartzSobolevCoordinate s v) (d j α) :=
    (A.denseRange_dualSmoothToSobolev (-s)).induction_on α
      (isClosed_eq (T.continuous.clm_apply continuous_const)
        (continuous_const.inner (d j).continuous)) (htest_smooth j v)
  have hinjective : Function.Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    intro α hα
    apply Subtype.ext
    apply PiLp.ext
    intro j
    change d j α = 0
    have hp (v : 𝓢(X, V)) : inner ℂ (schwartzSobolevCoordinate s v) (d j α) = 0 := by
      rw [← htest, hα]
      rfl
    have hall (z : Lp V 2 volume) : inner ℂ z (d j α) = 0 :=
      (denseRange_schwartzSobolevCoordinate n r s).induction_on z
        (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hp
    exact inner_self_eq_zero.mp (hall (d j α))
  let Q : A.DualSobolevSpace (-s) ≃L[ℂ] StrongDual ℂ (A.SobolevSpace s) :=
    ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hinjective)
      (LinearMap.range_eq_top.mpr hsurjective)
  refine ⟨Q, hT_smooth, ?_⟩
  intro S hS
  apply ContinuousLinearEquiv.ext
  funext α
  exact (A.denseRange_dualSmoothToSobolev (-s)).induction_on α
    (isClosed_eq S.continuous Q.continuous) (fun β ↦ by
      apply ContinuousLinearMap.ext
      intro u
      exact (A.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq (S _).continuous (Q _).continuous)
        (fun v ↦ (hS β v).trans (hT_smooth β v).symm))

/-- The linear duality map, specified by covector evaluation rather than Hermitian pairing. -/
def sobolevEvaluationDuality (s : ℝ) :
    A.DualSobolevSpace (-s) ≃L[ℂ] StrongDual ℂ (A.SobolevSpace s) :=
  Classical.choose (A.existsUnique_sobolevEvaluationDuality μ s).exists

/-- The geometric bilinear pairing between opposite Sobolev orders of E* and E. -/
def sobolevEvaluationPairing (s : ℝ) (α : A.DualSobolevSpace (-s))
    (u : A.SobolevSpace s) : ℂ :=
  A.sobolevEvaluationDuality μ s α u

/-- The completed bilinear pairing agrees with the original integral on smooth inputs. -/
theorem sobolevEvaluationPairing_smooth (s : ℝ)
    (α : smoothDualSections (n := n) (r := r) E)
    (u : smoothSections (n := n) (r := r) E) :
    A.sobolevEvaluationPairing μ s (A.dualSmoothToSobolev (-s) α)
      (A.smoothToSobolev s u) = smoothDualSectionPairing E μ α u := by
  /- Apply the specifying property of the chosen unique equivalence. In particular
  the two inputs are evaluated at the same base point in the defining integral. -/
  exact Classical.choose_spec (A.existsUnique_sobolevEvaluationDuality μ s).exists α u

end SmoothBundlePresentation

end AtiyahSinger

namespace AtiyahSinger.SmoothBundlePresentation

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]
  (A : SmoothBundlePresentation (n := n) (r := r) E)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Fiberwise Hermitian identification extends to an equivalence at every real Sobolev order. -/
theorem existsUnique_sobolevHermitianDual (s : ℝ) :
    ∃! T : A.SobolevSpace s ≃L⋆[ℂ] A.DualSobolevSpace s,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) =
          A.dualSmoothToSobolev s (smoothHermitianDualEquiv E u) := by
  /- A finite compactly supported partition already forces the base to be compact.
  Choose a smooth positive measure only inside this proof. The two opposite-order
  perfect pairings identify the same continuous dual; their composite extends the
  original native metric map. Its dense smooth specification removes dependence
  on that auxiliary measure and supplies uniqueness. -/
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : CompactSpace M := by
    refine ⟨?_⟩
    have hcompact : IsCompact (⋃ j : Fin A.size, tsupport (A.cutoff j)) :=
      isCompact_iUnion A.compact_support
    apply hcompact.of_isClosed_subset isClosed_univ
    intro x _
    by_contra hx
    have hzero (j : Fin A.size) : A.cutoff j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Set.mem_iUnion.mpr ⟨j, h⟩))
    have hsum := A.sum_cutoff x
    simp [hzero] at hsum
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let : IsSmoothPositiveMeasure (n := n) μ := hμ
  -- Transport only the order equality; both maps retain the exact smooth integral.
  have hnative (t q : ℝ) (ht : -t = q) :
      ∃ T : A.SobolevSpace q ≃L⋆[ℂ] StrongDual ℂ (A.SobolevSpace t),
        ∀ u v : smoothSections (n := n) (r := r) E,
          T (A.smoothToSobolev q v) (A.smoothToSobolev t u) =
            smoothSectionPairing μ E v u := by
    subst q
    exact ⟨A.sobolevDuality μ t, (A.existsUnique_sobolevDuality μ t).exists.choose_spec⟩
  have hevaluation (t q : ℝ) (ht : -t = q) :
      ∃ U : A.DualSobolevSpace q ≃L[ℂ] StrongDual ℂ (A.SobolevSpace t),
        ∀ (α : smoothDualSections (n := n) (r := r) E)
          (u : smoothSections (n := n) (r := r) E),
          U (A.dualSmoothToSobolev q α) (A.smoothToSobolev t u) =
            smoothDualSectionPairing E μ α u := by
    subst q
    exact ⟨A.sobolevEvaluationDuality μ t,
      (A.existsUnique_sobolevEvaluationDuality μ t).exists.choose_spec⟩
  obtain ⟨T, hT⟩ := hnative (-s) s (neg_neg s)
  obtain ⟨U, hU⟩ := hevaluation (-s) s (neg_neg s)
  let Q : A.SobolevSpace s ≃L⋆[ℂ] A.DualSobolevSpace s := T.trans U.symm
  have hQ (v : smoothSections (n := n) (r := r) E) :
      Q (A.smoothToSobolev s v) =
        A.dualSmoothToSobolev s (smoothHermitianDualEquiv E v) := by
    apply U.injective
    change U (U.symm (T (A.smoothToSobolev s v))) = _
    rw [U.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro u
    refine (A.denseRange_smoothToSobolev (-s)).induction_on u
      (isClosed_eq (T _).continuous (U _).continuous) ?_
    intro w
    rw [hT, hU, smoothDualSectionPairing_hermitian]
  refine ⟨Q, hQ, ?_⟩
  intro S hS
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer S.continuous Q.continuous
  funext u
  exact (hS u).trans (hQ u).symm

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The conjugate-linear metric identification of the two concrete Sobolev completions. -/
def sobolevHermitianDual (s : ℝ) : A.SobolevSpace s ≃L⋆[ℂ] A.DualSobolevSpace s :=
  Classical.choose (A.existsUnique_sobolevHermitianDual s).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The completed metric identification preserves the actual fiberwise smooth-section map. -/
theorem sobolevHermitianDual_smooth (s : ℝ) (u : smoothSections (n := n) (r := r) E) :
    A.sobolevHermitianDual s (A.smoothToSobolev s u) =
      A.dualSmoothToSobolev s (smoothHermitianDualEquiv E u) := by
  /- The unique extension retains the original fiberwise native metric map. -/
  exact (A.existsUnique_sobolevHermitianDual s).exists.choose_spec u

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The metric-free bilinear duality recovers the previously defined Hermitian duality. -/
theorem sobolevEvaluationPairing_hermitian [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (s : ℝ) (v : A.SobolevSpace (-s)) (u : A.SobolevSpace s) :
    A.sobolevEvaluationPairing μ s (A.sobolevHermitianDual (-s) v) u =
      A.sobolevPairing μ s v u := by
  /- On smooth inputs native dualization turns evaluation into the original
  Hermitian integral. Continuity in both completed variables extends that identity. -/
  change A.sobolevEvaluationDuality μ s (A.sobolevHermitianDual (-s) v) u =
    A.sobolevDuality μ s v u
  refine (A.denseRange_smoothToSobolev (-s)).induction_on v
    (isClosed_eq (((A.sobolevEvaluationDuality μ s).continuous.comp
      (A.sobolevHermitianDual (-s)).continuous).clm_apply continuous_const)
      ((A.sobolevDuality μ s).continuous.clm_apply continuous_const)) ?_
  intro w
  refine (A.denseRange_smoothToSobolev s).induction_on u
    (isClosed_eq (A.sobolevEvaluationDuality μ s _).continuous
      (A.sobolevDuality μ s _).continuous) ?_
  intro z
  rw [A.sobolevHermitianDual_smooth]
  exact (A.sobolevEvaluationPairing_smooth μ s (smoothHermitianDualEquiv E w) z).trans
    ((smoothDualSectionPairing_hermitian E μ w z).trans
      (A.sobolevPairing_smoothToSobolev μ s z w).symm)

end AtiyahSinger.SmoothBundlePresentation
