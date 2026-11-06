/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndexDiffeomorph
public import AtiyahSinger.Topology.CotangentModelKZero

/-!
# The analytic index in an arbitrary specified finite-dimensional full model

Public module ID: M0781.

An explicit linear equivalence to a Euclidean model supplies a recharted atlas
on the original manifold. Choose a positive smooth density for that atlas and
compose the existing component analytic index with the exact cotangent K
transport. The comparison with any supplied density and independence of the
linear equivalence ensure that this is the same intrinsic analytic index.

Sources: SG III.3 Theorem 3.17(v) and III.13 (13.7)--(13.8). The model adapter
is a project supplement for the current Euclidean analytic interfaces. It
does not establish the twisted product index formula of Theorem 13.6.
The model independence follows by the actual identity diffeomorphism between
the two specified atlases and its inverse-dual cotangent formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The existing analytic index, pulled back to the original full-model cotangent K group. -/
def analyticIndexLinearModel :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    let c := cotangentLinearModelHomeomorph e M
    letI := c.symm.t2Space
    letI := c.isOpenEmbedding.locallyCompactSpace
    CompactSupportKZero
        (TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)) →+ ℤ := by
  letI := linearModelChartedSpace e M
  letI := isManifold_linearModelChartedSpace e M
  let c := cotangentLinearModelHomeomorph e M
  letI := c.symm.t2Space
  letI := c.isOpenEmbedding.locallyCompactSpace
  letI := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  -- Select a density for this exact Euclidean atlas on the same Borel space.
  let μ : Measure M := (exists_smoothPositiveMeasure (n := n) (M := M)).choose
  letI : IsSmoothPositiveMeasure (n := n) μ :=
    (exists_smoothPositiveMeasure (n := n) (M := M)).choose_spec
  -- The component construction includes disconnected and empty compact manifolds.
  exact (analyticIndexOfComponents μ).comp (cotangentKZeroLinearModel e M).toAddMonoidHom

/-- Any positive smooth density for the specified recharted atlas gives the same index. -/
theorem analyticIndexLinearModel_eq_comp (μ : Measure M)
    (hμ : letI := linearModelChartedSpace e M
      IsSmoothPositiveMeasure (n := n) μ) :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    letI := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
    letI := hμ
    analyticIndexLinearModel e M =
      (analyticIndexOfComponents μ).comp (cotangentKZeroLinearModel e M).toAddMonoidHom := by
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let := hμ
  let ν : Measure M := (exists_smoothPositiveMeasure (n := n) (M := M)).choose
  let : IsSmoothPositiveMeasure (n := n) ν :=
    (exists_smoothPositiveMeasure (n := n) (M := M)).choose_spec
  -- Both densities belong to this exact recharted atlas; the cotangent transport stays fixed.
  change (analyticIndexOfComponents ν).comp (cotangentKZeroLinearModel e M).toAddMonoidHom =
    (analyticIndexOfComponents μ).comp (cotangentKZeroLinearModel e M).toAddMonoidHom
  rw [analyticIndexOfComponents_independent_measure ν μ]

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the original cotangent classes and analytic linear-model
-- transport.
/-- The analytic index on the original cotangent K group is independent of the linear model. -/
theorem analyticIndexLinearModel_independent_equiv {m : ℕ}
    (f : E ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    analyticIndexLinearModel e M = analyticIndexLinearModel f M := by
  classical
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let := linearModelChartedSpace f M
  let := isManifold_linearModelChartedSpace f M
  let de := linearModelDiffeomorph e M
  let df := linearModelDiffeomorph f M
  let d := de.symm.trans df
  let ce := cotangentLinearModelHomeomorph e M
  let cf := cotangentLinearModelHomeomorph f M
  let := ce.symm.t2Space
  let := ce.isOpenEmbedding.locallyCompactSpace
  -- The identity between these two original atlases has the prescribed coordinate derivative.
  have hderiv (x : M) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        d.symm x = e.toContinuousLinearMap.comp f.symm.toContinuousLinearMap := by
    change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((de : M → M) ∘ df.symm) x = _
    rw [mfderiv_comp x (de.mdifferentiable (by simp) (df.symm x))
      (df.symm.mdifferentiable (by simp) x)]
    exact congrArg₂ ContinuousLinearMap.comp
      ((contMDiff_mfderiv_linearModelId e M).2.1 (df.symm x))
      ((contMDiff_mfderiv_linearModelId f M).2.2 x)
  have hcotangent : ce.trans (cotangentDiffeomorph d) = cf := by
    apply Homeomorph.ext
    rintro ⟨x, ξ⟩
    change (⟨x, (ξ.comp e.symm.toContinuousLinearMap).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) d.symm x)⟩ :
        CotangentTotalSpace (n := m) (M := M)) = ⟨x, ξ.comp f.symm.toContinuousLinearMap⟩
    rw [hderiv]
    congr 1
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg ξ (e.symm_apply_apply (f.symm v))
  -- Pullback functoriality uses the same inverse homeomorphisms in this square.
  have hK : (cotangentKZeroDiffeomorph d).toAddMonoidHom.comp
      (cotangentKZeroLinearModel e M).toAddMonoidHom =
        (cotangentKZeroLinearModel f M).toAddMonoidHom := by
    change (compactSupportKZeroPullback
      ⟨(cotangentDiffeomorph d).symm, (cotangentDiffeomorph d).symm.continuous⟩
        (cotangentDiffeomorph d).symm.isProperMap).comp
      (compactSupportKZeroPullback ⟨ce.symm, ce.symm.continuous⟩ ce.symm.isProperMap) =
        compactSupportKZeroPullback ⟨cf.symm, cf.symm.continuous⟩ cf.symm.isProperMap
    rw [← compactSupportKZeroPullback_comp]
    have hinverse : (⟨ce.symm, ce.symm.continuous⟩ : C(_, _)).comp
        ⟨(cotangentDiffeomorph d).symm, (cotangentDiffeomorph d).symm.continuous⟩ =
          ⟨cf.symm, cf.symm.continuous⟩ := by
      exact congrArg (fun h ↦ (⟨h.symm, h.symm.continuous⟩ : C(_, _))) hcotangent
    congr 1
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨ν, hν⟩ := exists_smoothPositiveMeasure (n := m) (M := M)
  let := hν
  -- Component naturality allows these independently selected positive densities.
  rw [analyticIndexLinearModel_eq_comp e M μ hμ, analyticIndexLinearModel_eq_comp f M ν hν]
  rw [← hK, ← AddMonoidHom.comp_assoc, analyticIndexOfComponents_diffeomorph μ ν d]

end AtiyahSinger
