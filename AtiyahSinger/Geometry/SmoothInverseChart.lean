/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Smooth inverse charts with a common open domain

Public module ID: M1405.

A smooth map with invertible derivative has an actual inverse chart on which
both directions are smooth. The source is restricted to the open locus of
invertible derivatives, so inverse smoothness holds at every target point.
This form of the inverse function theorem supplies the local flag slices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

/-- The inverse function theorem gives one chart with both directions smooth on its open sets. -/
theorem exists_smoothInverseChart {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (x : E)
    (L : E ≃L[ℝ] F) (hL : HasFDerivAt f (L : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F,
      x ∈ e.source ∧ (e : E → F) = f ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hL (by simp)
  let U : Set E := {y | (fderiv ℝ f y).IsInvertible}
  have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (hf.continuous_fderiv (by simp))
  have hx : x ∈ U := by
    change (fderiv ℝ f x).IsInvertible
    rw [hL.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  let e := e₀.restrOpen U hU
  refine ⟨e, ?_, rfl, hf.contDiffOn, ?_⟩
  · exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hL (by simp), hx⟩
  -- The derivative is invertible throughout this source, not only at its center.
  intro y hy
  have hinv : (fderiv ℝ f (e.symm y)).IsInvertible := (e.map_target hy).2
  obtain ⟨A, hA⟩ := hinv
  have hd : HasFDerivAt e (A : E →L[ℝ] F) (e.symm y) := by
    change HasFDerivAt f (A : E →L[ℝ] F) (e.symm y)
    rw [hA]
    exact (hf.differentiable (by simp) _).hasFDerivAt
  exact (e.contDiffAt_symm hy hd hf.contDiffAt).contDiffWithinAt

end AtiyahSinger
