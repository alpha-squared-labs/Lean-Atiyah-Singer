/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSymbolIntegral
public import AtiyahSinger.Analysis.GlobalSymbolTopology

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Compact integration of genuine global symbols

Public module ID: M0681.

The integral takes values in each original Hom fiber. On a valid chart, the
same two frame equivalences commute with that finite-dimensional integral.
Continuous chart jets and uniform global symbol seminorms therefore give a
symbol of the same order by the existing compact local integration theorem.

The uniform hypotheses remain explicit. In particular this result does not
infer lower-order bounds from pointwise lower-order membership. It is the
integration step following the separate compact-group cocycle estimate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set Topology
open scoped ContDiff Manifold SchwartzMap


variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]

set_option maxSynthPendingDepth 25 in
/-- Compact integration preserves the order of genuine global symbols with continuous
coordinate jets and uniform bounds in every original global symbol seminorm. -/
theorem isGlobalSymbol_integral_of_continuous_jets {m : ℝ}
    (a : Y → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hmixed : ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F)),
        [MemTrivializationAtlas e] → [MemTrivializationAtlas f] → ∀ i j : ℕ,
        ContinuousOn (fun p : Y ×
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
            symbolDerivative (globalSymbolInChart E F (a p.1).val c e f) i j p.2.1 p.2.2)
          (univ ×ˢ (symbolChartDomain E F c e f ×ˢ univ)))
    (hjoint : ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F)),
        [MemTrivializationAtlas e] → [MemTrivializationAtlas f] → ∀ k : ℕ,
        ContinuousOn (fun p : Y ×
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
            iteratedFDeriv ℝ k
              (Function.uncurry (globalSymbolInChart E F (a p.1).val c e f)) p.2)
          (univ ×ˢ (symbolChartDomain E F c e f ×ˢ univ)))
    (hbound : ∀ J : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F,
      BddAbove (range (fun t ↦ globalSymbolSeminorm E F m J (a t)))) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m
      (fun x ξ ↦ ∫ t, (a t).val x ξ ∂μ) := by
  classical
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  intro c hc e f _ _
  let X := EuclideanSpace ℝ (Fin n)
  let U := symbolChartDomain E F c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  let b (t : Y) := globalSymbolInChart E F (a t).val c e f
  have hb (t : Y) : IsSymbol U m (b t) := (a t).property c hc e f
  -- Each local compact derivative test is precisely one of the original global seminorms.
  have hlocal : IsSymbol U m (fun x ξ ↦ ∫ t, b t x ξ ∂μ) := by
    apply isSymbol_integral_of_continuous_jets μ hU b hb
      (hmixed c hc e f) (hjoint c hc e f)
    intro K hKU hK i j
    let J : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F := {
      chart := c
      mem_atlas := hc
      inputFrame := e
      outputFrame := f
      input_mem_atlas := inferInstance
      output_mem_atlas := inferInstance
      localIndex := ⟨K, hKU, hK, i, j⟩ }
    obtain ⟨C, hC⟩ := hbound J
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro t x hx ξ
    have hnorm := symbolDerivative_norm_le_seminorm hU m J.localIndex
      (globalSymbolInChartLinearMap E F m J (a t)) x hx ξ
    have hle : globalSymbolSeminorm E F m J (a t) ≤ max C 0 :=
      (hC (mem_range_self t)).trans (le_max_left _ _)
    exact hnorm.trans (mul_le_mul_of_nonneg_right hle
      (Real.rpow_nonneg (by positivity) _))
  let p := globalSymbolInChart E F (fun x ξ ↦ ∫ t, (a t).val x ξ ∂μ) c e f
  -- An equivalence of Hom fibers commutes with the integral in these same valid frames.
  have heq (z : X) (hz : z ∈ U) (η : X) :
      p z η = ∫ t, b t z η ∂μ := by
    let A := (e.linearEquivAt ℂ (c.symm z) hz.1.2).toContinuousLinearEquiv
    let B := (f.linearEquivAt ℂ (c.symm z) hz.2).toContinuousLinearEquiv
    let C := A.arrowCongr B
    have hC (v : E (c.symm z) →L[ℂ] F (c.symm z)) : C v =
        (f.continuousLinearMapAt ℂ (c.symm z)).comp (v.comp (e.symmL ℂ (c.symm z))) := by
      apply ContinuousLinearMap.ext
      intro w
      simp only [C, ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearMap.comp_apply]
      change f.linearEquivAt ℂ (c.symm z) hz.2
        (v ((e.linearEquivAt ℂ (c.symm z) hz.1.2).symm w)) = _
      rw [Trivialization.linearEquivAt_symm_apply, e.symmL_apply hz.1.2]
      exact f.continuousLinearMapAt_apply_of_mem ℂ hz.2 _ |>.symm
    have h := C.integral_comp_comm (μ := μ)
      (fun t ↦ (a t).val (c.symm z) (covectorFromChart c (c.symm z) η))
    simpa only [hC, p, b, globalSymbolInChart] using h.symm
  -- Equal functions on the open chart domain have the same actual mixed derivatives.
  refine ⟨hlocal.1.congr (fun z hz ↦ heq z.1 hz.1 z.2), ?_⟩
  intro K hKU hK i j
  obtain ⟨C, hC, hestimate⟩ := hlocal.2 K hKU hK i j
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  have hnear : (fun z ↦ iteratedFDeriv ℝ j (p z) ξ) =ᶠ[𝓝 x]
      (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ ∫ t, b t z η ∂μ) ξ) := by
    filter_upwards [hU.mem_nhds (hKU hx)] with z hz
    rw [funext (heq z hz)]
  change ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (p z) ξ) x‖ ≤ _
  rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hestimate x hx ξ

end AtiyahSinger
