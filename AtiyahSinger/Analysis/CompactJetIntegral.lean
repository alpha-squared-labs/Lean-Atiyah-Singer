/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Smooth integration of continuous jet families

Public module ID: M0351.

Integration over a compact topological parameter commutes with every derivative
in an open finite-dimensional real domain, provided that the original slices
are smooth and all their spatial jets depend jointly continuously on parameter
and point. The parameter needs no differentiable structure. This distinction is
needed when the geometric parameter is composed with a merely continuous map,
such as inverse in a topological group with separately specified smooth actions.

The proof is the standard differentiation-under-the-integral argument. Compact
parameter times a small closed ball gives a uniform bound for the next spatial
derivative. Mathlib's dominated Fréchet differentiation theorem then constructs
the Taylor series of the integral. No norm on the space of smooth functions and
no integral in that space is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff

variable {Y H F : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure Y) [IsFiniteMeasure μ]
  {f : Y → H → F} {s : Set H} (hs : IsOpen s)
  (hf : ∀ y, ContDiffOn ℝ ∞ (f y) s)
  (hjets : ∀ k : ℕ,
    ContinuousOn (fun p : Y × H ↦ iteratedFDeriv ℝ k (f p.1) p.2) (univ ×ˢ s))

include hs hf hjets

private theorem hasFTaylorSeriesUpToOn_integral_of_continuous_jets :
    HasFTaylorSeriesUpToOn ∞ (fun x ↦ ∫ y, f y x ∂μ)
      (fun x k ↦ ∫ y, iteratedFDeriv ℝ k (f y) x ∂μ) s := by
  -- Every fixed spatial jet is a continuous function of the compact parameter.
  have hcont (k : ℕ) (x : H) (hx : x ∈ s) :
      Continuous (fun y ↦ iteratedFDeriv ℝ k (f y) x) := by
    apply continuousOn_univ.mp
    exact (hjets k).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y _ ↦ ⟨mem_univ y, hx⟩)
  have hint (k : ℕ) (x : H) (hx : x ∈ s) :
      Integrable (fun y ↦ iteratedFDeriv ℝ k (f y) x) μ :=
    (hcont k x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hderiv (k : ℕ) (x : H) (hx : x ∈ s) :
      HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (f y) z ∂μ)
        ((∫ y, iteratedFDeriv ℝ (k + 1) (f y) x ∂μ).curryLeft) x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ H) F
    let d (y : Y) (z : H) : H →L[ℝ] H [×k]→L[ℝ] F :=
      C (iteratedFDeriv ℝ (k + 1) (f y) z)
    have hd : ContinuousOn (fun p : Y × H ↦ d p.1 p.2) (univ ×ˢ s) :=
      C.continuous.comp_continuousOn (hjets (k + 1))
    -- A small closed ball stays inside the open domain; compactness bounds the next jet.
    obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
    have hcpt : IsCompact ((univ : Set Y) ×ˢ Metric.closedBall x r) :=
      isCompact_univ.prod (isCompact_closedBall x r)
    obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn
      (hd.mono (prod_mono Subset.rfl hrs))
    have hD : HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (f y) z ∂μ)
        (∫ y, d y x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun z y ↦ d y z) (bound := fun _ ↦ B)
        (Metric.closedBall_mem_nhds x hr)
      · filter_upwards [hs.mem_nhds hx] with z hz
        exact (hint k z hz).1
      · exact hint k x hx
      · exact ((C.continuous.comp (hcont (k + 1) x hx)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).1
      · exact Eventually.of_forall (fun y z hz ↦ hB (y, z) ⟨mem_univ y, hz⟩)
      · exact integrable_const B
      · apply Eventually.of_forall
        intro y z hz
        have hsmooth : ContDiffAt ℝ ∞ (f y) z :=
          (hf y z (hrs hz)).contDiffAt (hs.mem_nhds (hrs hz))
        have hdiff := hsmooth.differentiableAt_iteratedFDeriv (m := k)
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
        exact hdiff.hasFDerivAt
    -- Currying is continuous linear and commutes with this finite-dimensional-jet integral.
    have hcomm := C.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (hint (k + 1) x hx)
    change (∫ y, d y x ∂μ) =
      (∫ y, iteratedFDeriv ℝ (k + 1) (f y) x ∂μ).curryLeft at hcomm
    rwa [hcomm] at hD
  -- The integrated jets satisfy the three Taylor-series fields for the original integral.
  constructor
  · intro x hx
    let C := continuousMultilinearCurryFin0 ℝ H F
    have hcomm := C.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (hint 0 x hx)
    change (∫ y, (iteratedFDeriv ℝ 0 (f y) x).curry0 ∂μ) =
      (∫ y, iteratedFDeriv ℝ 0 (f y) x ∂μ).curry0 at hcomm
    simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply] using
      hcomm.symm
  · intro k _ x hx
    exact (hderiv k x hx).hasFDerivWithinAt
  · intro k _
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    · exact (hjets k).comp continuous_swap.continuousOn
        (fun p hp ↦ ⟨mem_univ p.2, hp.1⟩)
    · intro x y hx hy
      exact (hy (mem_univ y)).elim

/-- A compact finite-measure integral of a jointly continuous spatial jet family is smooth. -/
theorem contDiffOn_integral_of_continuous_jets :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ y, f y x ∂μ) s := by
  -- The actual integrated jets form a Taylor series of every finite order.
  exact (hasFTaylorSeriesUpToOn_integral_of_continuous_jets μ hs hf hjets).contDiffOn

/-- Each spatial derivative is the integral of the same derivative of the original family. -/
theorem iteratedFDeriv_integral_of_continuous_jets (k : ℕ) {x : H} (hx : x ∈ s) :
    iteratedFDeriv ℝ k (fun z ↦ ∫ y, f y z ∂μ) x =
      ∫ y, iteratedFDeriv ℝ k (f y) x ∂μ := by
  -- Uniqueness of derivatives identifies the integrated Taylor series on the open domain.
  have hseries := hasFTaylorSeriesUpToOn_integral_of_continuous_jets μ hs hf hjets
  have hsmooth := contDiffOn_integral_of_continuous_jets μ hs hf hjets
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := k)
    (by simp) hs.uniqueDiffOn hx
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
    (((hsmooth x hx).contDiffAt (hs.mem_nhds hx)).of_le (by simp)) hx] at heq
  exact heq.symm

end AtiyahSinger
