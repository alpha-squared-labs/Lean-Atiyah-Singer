/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

import AtiyahSinger.Analysis.CompactJetIntegral
import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Smooth integration over a compact manifold parameter

Public module ID: M1131.

`contDiffOn_integral_of_compact_manifold` proves local smoothness of a finite-measure integral
of a jointly smooth function on a compact manifold times an open finite-dimensional real domain.
The parameter keeps its original manifold model, including possible corners; no finite-dimensional
or Hausdorff parameter hypothesis is needed. The output is a complete real normed space.

The proof combines the existing smooth partial-jet theorem with compact continuous-jet
integration. Those interfaces retain the standard dominated differentiation argument and the
original manifold parameter. It supplies the analytic step for smooth Haar averages and for smooth
kernel output dependence. It makes no claim about noncompact parameters without additional
domination or support hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Set Filter MeasureTheory Topology
open scoped ContDiff

universe u

variable {V HG Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (I : ModelWithCorners ℝ V HG)
  [TopologicalSpace Y] [ChartedSpace HG Y] [IsManifold I ∞ Y]
  [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]

set_option maxHeartbeats 1000000 in
-- This budget covers slice smoothness and all orders of compact-parameter differentiation.
/-- Integrating a jointly smooth function over a compact manifold parameter preserves smoothness.
The measure is any finite Borel measure. The finite-dimensional hypothesis concerns only the
variable being differentiated; the parameter model may have corners. The domain and codomain
normed spaces are stated in the same universe so the derivative induction has one codomain class. -/
theorem contDiffOn_integral_of_compact_manifold {H F : Type u}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : Y × H → F} {s : Set H} (hs : IsOpen s)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, F) ∞ f (univ ×ˢ s)) :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ y, f (y, x) ∂μ) s := by
  -- Restrict joint manifold smoothness to each slice in the differentiated variable.
  have hslice (y : Y) : ContDiffOn ℝ ∞ (fun x ↦ f (y, x)) s := by
    apply ContMDiffOn.contDiffOn
    exact hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x hx ↦ ⟨mem_univ y, hx⟩)
  -- The existing partial-jet theorem retains the same manifold parameter and its corners.
  have hjets (k : ℕ) : ContinuousOn
      (fun p : Y × H ↦ iteratedFDeriv ℝ k (fun x ↦ f (p.1, x)) p.2) (univ ×ˢ s) :=
    (contMDiffOn_iteratedFDeriv_parameter I (isOpen_univ.prod hs) hf k).continuousOn
  -- Integrate these same jets with the original finite measure and compact parameter.
  exact contDiffOn_integral_of_continuous_jets μ hs hslice hjets


end AtiyahSinger
