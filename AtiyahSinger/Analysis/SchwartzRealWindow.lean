/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# A real compact Schwartz window with nonzero square integral

Public module ID: M0950.

A real smooth plateau bump supplies a compact Schwartz window. Positivity on
a neighborhood of the origin makes its square integral nonzero, including in
dimension zero. This fixes the normalization in windowed Fourier reconstruction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ComplexConjugate ContDiff SchwartzMap

/-- A real compact Schwartz window can be chosen with nonzero square integral. -/
theorem exists_real_schwartzWindow (n : ℕ) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), HasCompactSupport g ∧
      (∀ x, conj (g x) = g x) ∧ (∫ x, g x ^ 2) ≠ 0 := by
  let V := EuclideanSpace ℝ (Fin n)
  let b : ContDiffBump (0 : V) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let g : 𝓢(V, ℂ) :=
    (b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hg (x : V) : g x = (b x : ℂ) := rfl
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have hpos : 0 < ∫ x : V, b x ^ 2 :=
    (b.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (b.hasCompactSupport.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp))
      (fun x ↦ sq_nonneg (b x)) (by rw [hb0]; norm_num)
  refine ⟨g, b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl, ?_, ?_⟩
  · intro x
    simp only [hg, Complex.conj_ofReal]
  · have heq : (∫ x : V, g x ^ 2) = ((∫ x : V, b x ^ 2 : ℝ) : ℂ) := by
      simp only [hg, ← Complex.ofReal_pow]
      exact integral_complex_ofReal
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'

end AtiyahSinger
