/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentMetric
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth coordinate coefficients of the original cotangent metric

Public module ID: M1152.

The coordinate covectors are the pullbacks of constant linear functionals by
the actual derivative of the selected chart. Evaluating the supplied smooth
metric on them gives its smooth Gram coefficients, without changing the
cotangent bundle, the chart, or the metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothCotangentMetric

open Bundle Filter IsManifold
open scoped ContDiff Manifold Topology

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The supplied cotangent metric has smooth coefficients in every original valid chart. -/
theorem contMDiffOn_inner_covectorFromChart
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (η ζ : EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ g.inner x (covectorFromChart c x η) (covectorFromChart c x ζ))
      c.source := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
  intro x hx
  -- Pull a constant coordinate covector back by the derivative of this same chart.
  have hcovector (v : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt I (I.prod 𝓘(ℝ, CotangentModel n)) ∞
        (fun y ↦ (⟨y, covectorFromChart c y v⟩ : CotangentTotalSpace)) x := by
    have hd := (contMDiffAt_of_mem_maximalAtlas hcm hx).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)
    have hinner : ContMDiffAt I 𝓘(ℝ, CotangentModel n) ∞
        (fun _ : M ↦ innerSL ℝ v) x := contMDiffAt_const
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply (hinner.clm_comp hd).congr_of_eventuallyEq
    filter_upwards with y
    ext w
    simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply, I]
    rfl
  -- Two bundle evaluations retain the original metric and both original covectors.
  have h := (g.contMDiff.contMDiffAt.clm_bundle_apply (hcovector η)).clm_bundle_apply
    (hcovector ζ)
  have hs := (contMDiffAt_totalSpace.mp h).2
  simpa using hs.contMDiffWithinAt

end AtiyahSinger.SmoothCotangentMetric
