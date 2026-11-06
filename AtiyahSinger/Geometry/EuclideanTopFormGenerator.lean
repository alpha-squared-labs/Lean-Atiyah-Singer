/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanFormIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A normalized compactly supported Euclidean top form

Public module ID: M1223.

A normalized real bump in the standard coordinates multiplies the determinant
of the same ordered Euclidean basis. The resulting original complex-valued
alternating form is smooth, compactly supported and has integral one.

Source: the standard compact-support orientation generator, Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- There is an actual smooth compactly supported Euclidean top form of integral one. -/
theorem exists_smooth_compactlySupported_topForm_integral_one (n : ℕ) :
    ∃ α : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℂ,
      ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ euclideanTopFormIntegral n α = 1 := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let P := Fin n → ℝ
  let E : V ≃L[ℝ] P := EuclideanSpace.equiv (Fin n) ℝ
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let δR : V [⋀^Fin n]→L[ℝ] ℝ :=
    { b.toBasis.det with cont := b.toBasis.continuous_toMatrix.matrix_det }
  let δ : V [⋀^Fin n]→L[ℝ] ℂ := Complex.ofRealCLM.compContinuousAlternatingMap δR
  have hδ : δ b = 1 := by
    change (b.toBasis.det b.toBasis : ℂ) = 1
    rw [b.toBasis.det_self, Complex.ofReal_one]
  let bump : ContDiffBump (0 : P) := default
  let φ : P → ℝ := bump.normed volume
  have hφ : ContDiff ℝ ∞ φ := bump.contDiff_normed
  have hφc : HasCompactSupport φ := bump.hasCompactSupport_normed
  have hφi : (∫ x : P, φ x) = 1 := bump.integral_normed
  let α (x : V) : V [⋀^Fin n]→L[ℝ] ℂ := φ (E x) • δ
  have hα : ContDiff ℝ ∞ α := (hφ.comp E.contDiff).smul contDiff_const
  have hαc : HasCompactSupport α :=
    (hφc.comp_homeomorph E.toHomeomorph).comp_left (g := fun t : ℝ ↦ t • δ) (zero_smul ℝ δ)
  refine ⟨α, hα, hαc, ?_⟩
  change (∫ x : P, (φ (E (E.symm x)) • δ) b) = 1
  simp only [E.apply_symm_apply, ContinuousAlternatingMap.smul_apply, hδ]
  change (∫ x : P, (φ x : ℂ) * 1) = 1
  simp only [mul_one, integral_complex_ofReal, hφi, Complex.ofReal_one]

end AtiyahSinger
