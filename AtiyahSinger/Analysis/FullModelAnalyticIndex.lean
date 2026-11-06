/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LinearModelAnalyticIndex

/-!
# Analytic-index naturality in the original full models

Public module ID: M0649.

A supplied native cotangent homeomorphism with the actual inverse-differential
formula transports the intrinsic analytic index along the same diffeomorphism.
The Euclidean changes of model cancel in that formula. This comparison is used
for the original associated sphere quotient and its product realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n m : ℕ}
  (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (f : F ≃L[ℝ] EuclideanSpace ℝ (Fin m))
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Compare the same inverse differential through both specified Euclidean coordinate changes.
/-- The native inverse-differential cotangent map preserves the full-model analytic index. -/
theorem analyticIndexLinearModel_diffeomorph
    (d : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N)
    (c : TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) ≃ₜ
      TotalSpace (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ))
    (hc : ∀ z, c z = ⟨d z.proj,
      z.snd.comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) d.symm (d z.proj))⟩) :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    letI := linearModelChartedSpace f N
    letI := isManifold_linearModelChartedSpace f N
    let ce := cotangentLinearModelHomeomorph e M
    let cf := cotangentLinearModelHomeomorph f N
    letI := ce.symm.t2Space
    letI := ce.isOpenEmbedding.locallyCompactSpace
    letI := cf.symm.t2Space
    letI := cf.isOpenEmbedding.locallyCompactSpace
    (analyticIndexLinearModel f N).comp (compactSupportKZeroHomeomorph c) =
      analyticIndexLinearModel e M := by
  classical
  dsimp only
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let := linearModelChartedSpace f N
  let := isManifold_linearModelChartedSpace f N
  let := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin m)) N
  let ce := cotangentLinearModelHomeomorph e M
  let cf := cotangentLinearModelHomeomorph f N
  let := ce.symm.t2Space
  let := ce.isOpenEmbedding.locallyCompactSpace
  let := cf.symm.t2Space
  let := cf.isOpenEmbedding.locallyCompactSpace
  let de := linearModelDiffeomorph e M
  let df := linearModelDiffeomorph f N
  let D := (de.symm.trans d).trans df
  -- The derivative is computed for this same three-map composition.
  have hderiv (y : N) :
      mfderiv (𝓡 m) (𝓡 n) D.symm y = e.toContinuousLinearMap.comp
        ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) d.symm y).comp f.symm.toContinuousLinearMap) := by
    change mfderiv (𝓡 m) (𝓡 n) ((d.symm.trans de : N → M) ∘ df.symm) y = _
    rw [mfderiv_comp y ((d.symm.trans de).mdifferentiable (by simp) (df.symm y))
      (df.symm.mdifferentiable (by simp) y)]
    have hinner : mfderiv 𝓘(ℝ, F) (𝓡 n) (d.symm.trans de) (df.symm y) =
        e.toContinuousLinearMap.comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) d.symm y) := by
      change mfderiv 𝓘(ℝ, F) (𝓡 n) ((de : M → M) ∘ d.symm) y = _
      exact (mfderiv_comp y (de.mdifferentiable (by simp) (d.symm y))
        (d.symm.mdifferentiable (by simp) y)).trans
          (congrArg (fun a ↦ a.comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) d.symm y))
            ((contMDiff_mfderiv_linearModelId e M).2.1 (d.symm y)))
    exact congrArg₂ ContinuousLinearMap.comp hinner
      ((contMDiff_mfderiv_linearModelId f N).2.2 y)
  have hsquare : c.trans cf = ce.trans (cotangentDiffeomorph D) := by
    apply Homeomorph.ext
    intro z
    change cf (c z) = cotangentDiffeomorph D (ce z)
    rw [hc]
    change (⟨d z.proj, (z.snd.comp
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) d.symm (d z.proj))).comp
        f.symm.toContinuousLinearMap⟩ : CotangentTotalSpace (n := m) (M := N)) =
      ⟨d z.proj, (z.snd.comp e.symm.toContinuousLinearMap).comp
        (mfderiv (𝓡 m) (𝓡 n) D.symm (d z.proj))⟩
    rw [hderiv]
    apply congrArg (TotalSpace.mk (d z.proj))
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg z.snd (e.symm_apply_apply
      ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) d.symm (d z.proj)) (f.symm v))).symm
  have hK : (cotangentKZeroLinearModel f N).toAddMonoidHom.comp
      (compactSupportKZeroHomeomorph c) =
        (cotangentKZeroDiffeomorph D).toAddMonoidHom.comp
          (cotangentKZeroLinearModel e M).toAddMonoidHom := by
    change (compactSupportKZeroHomeomorph cf).comp (compactSupportKZeroHomeomorph c) =
      (compactSupportKZeroHomeomorph (cotangentDiffeomorph D)).comp
        (compactSupportKZeroHomeomorph ce)
    unfold compactSupportKZeroHomeomorph
    rw [← compactSupportKZeroPullback_comp, ← compactSupportKZeroPullback_comp]
    have hinverse : (⟨c.symm, c.symm.continuous⟩ : C(_, _)).comp
        ⟨cf.symm, cf.symm.continuous⟩ =
          (⟨ce.symm, ce.symm.continuous⟩ : C(_, _)).comp
            ⟨(cotangentDiffeomorph D).symm, (cotangentDiffeomorph D).symm.continuous⟩ :=
      congrArg (fun h ↦ (⟨h.symm, h.symm.continuous⟩ : C(_, _))) hsquare
    congr 1
  -- The existing component theorem permits independent positive densities on the two models.
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨ν, hν⟩ := exists_smoothPositiveMeasure (n := m) (M := N)
  let := hν
  rw [analyticIndexLinearModel_eq_comp f N ν hν,
    analyticIndexLinearModel_eq_comp e M μ hμ, AddMonoidHom.comp_assoc, hK,
    ← AddMonoidHom.comp_assoc, analyticIndexOfComponents_diffeomorph μ ν D]

end AtiyahSinger
