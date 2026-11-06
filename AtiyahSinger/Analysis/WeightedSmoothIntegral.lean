/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactJetIntegral
public import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Continuous weights in compact smooth parameter integrals

Public module ID: M1051.

A continuous scalar weight in the compact parameter does not affect smoothness
in the spatial variable. Only the spatial derivatives are integrated; no
regularity of the weight beyond continuity is required. This permits continuous
partitions in compact-group averages under the original weak group assumptions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff Manifold

universe u

/-- A continuous complex parameter weight preserves smoothness of the actual compact integral. -/
theorem contDiffOn_integral_smul_of_compact_manifold
    {V HG Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace HG] (I : ModelWithCorners ℝ V HG)
    [TopologicalSpace Y] [ChartedSpace HG Y] [IsManifold I ∞ Y]
    [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    {H F : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {f : Y × H → F} {s : Set H} (hs : IsOpen s)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, F) ∞ f (univ ×ˢ s))
    (w : Y → ℂ) (hw : Continuous w) :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ y, w y • f (y, x) ∂μ) s := by
  -- In each slice the parameter weight is a constant continuous linear multiplier.
  have hslice (y : Y) : ContDiffOn ℝ ∞ (fun x ↦ f (y, x)) s :=
    (hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x hx ↦ ⟨mem_univ y, hx⟩)).contDiffOn
  have hweighted (y : Y) : ContDiffOn ℝ ∞ (fun x ↦ w y • f (y, x)) s :=
    (hslice y).const_smul (w y)
  apply contDiffOn_integral_of_continuous_jets μ hs hweighted
  intro k
  -- Differentiate in space first; the unchanged continuous weight multiplies every jet.
  have hj := (contMDiffOn_iteratedFDeriv_parameter I (isOpen_univ.prod hs) hf k).continuousOn
  have h := (hw.comp continuous_fst).continuousOn.smul hj
  apply h.congr
  intro p hp
  exact iteratedFDeriv_const_smul_apply'
    (((hslice p.1 p.2 hp.2).contDiffAt (hs.mem_nhds hp.2)).of_le (by simp))

end AtiyahSinger
