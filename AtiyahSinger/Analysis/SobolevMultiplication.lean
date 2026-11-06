/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.Pseudolocal

import AtiyahSinger.Analysis.BesselSymbol

/-!
# Compact smooth matrix multiplication at every Sobolev order

Public module ID: M1002.

The specified Schwartz matrix multiplier is a zero-order pseudodifferential operator.
Its bounded realization therefore preserves every real Bessel order, including negative
orders. Rectangular matrices and zero ranks are allowed. This is the local frame-change
estimate used when comparing finite presentations of bundle Sobolev spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 20 in
/-- A compact smooth matrix multiplier preserves every real Sobolev order. -/
theorem exists_norm_matrixMultiplier_sobolev_le {n r q : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate s (matrixMultiplierCLM A hA hcA u)‖ ≤
          C * ‖schwartzSobolevCoordinate s u‖ := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let p : SymbolFunction n r q := fun x _ ↦ A x
  -- The constant-frequency symbol has order zero by the smooth matrix symbol law.
  have hp : IsSymbol univ 0 p := by
    have h := isSymbol_matrixSymbol univ isOpen_univ 0 (besselSymbol n r 0)
      (isSymbol_besselSymbol n r 0) A (fun _ ↦ ContinuousLinearMap.id ℂ V)
      hA.contDiffOn contDiffOn_const
    have heq : matrixSymbol A (fun _ ↦ ContinuousLinearMap.id ℂ V)
        (besselSymbol n r 0) = p := by
      funext x ξ
      simp only [matrixSymbol, besselSymbol, zero_div, Real.rpow_zero, one_smul]
      rfl
    rw [heq] at h
    exact h
  have hcp : HasCompactSupport p := by
    apply hcA.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    change (fun _ : X ↦ A x) ≠ 0 at hx
    exact fun hzero ↦ hx (funext (fun _ ↦ hzero))
  have hquant (u : 𝓢(X, V)) (x : X) : quantize p u x = A x (u x) := by
    let f : X → V := fun ξ ↦
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℂ)) • (𝓕 u) ξ
    have hphase (ξ : X) :
        ‖Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hf : Integrable f := by
      have hfu : Integrable (fun ξ : X ↦ (𝓕 u) ξ) (volume : Measure X) := (𝓕 u).integrable
      apply hfu.norm.mono'
      · have hinner : Continuous (fun ξ : X ↦ (inner ℝ x ξ : ℂ)) := by fun_prop
        exact ((continuous_const.mul hinner).cexp.smul (𝓕 u).continuous).aestronglyMeasurable
      · filter_upwards [] with ξ
        simp only [f, norm_smul, hphase, one_mul]
        exact le_rfl
    calc
      quantize p u x = ∫ ξ, A x (f ξ) := by
        rw [quantize_rescaled]
        simp only [p, f, map_smul]
        rfl
      _ = A x (∫ ξ, f ξ) := (A x).integral_comp_comm hf
      _ = A x (quantize (besselSymbol n r 0) u x) := by
        rw [quantize_rescaled]
        simp only [besselSymbol, zero_div, Real.rpow_zero, one_smul,
          ContinuousLinearMap.id_apply, f]
        rfl
      _ = A x (u x) := by
        rw [quantize_besselSymbol]
        simp only [zero_div, Real.rpow_zero, SchwartzMap.fourierMultiplierCLM_const, one_smul,
          ContinuousLinearMap.id_apply]
  -- Identify the bounded zero-order realization with the same actual matrix action.
  let T := quantizeSobolev 0 s p hp hcp
  refine ⟨‖T‖, norm_nonneg _, ?_⟩
  intro u
  have hT : T (schwartzSobolevCoordinate s u) =
      schwartzSobolevCoordinate s (matrixMultiplierCLM A hA hcA u) := by
    apply besselRealization_injective n q s
    ext1 φ
    have h := besselRealization_quantizeSobolev 0 s p hp hcp u φ
    rw [sub_zero] at h
    rw [h, besselRealization_schwartzSobolevCoordinate, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hquant, matrixMultiplierCLM_apply]
  rw [← hT]
  exact T.le_opNorm _

end AtiyahSinger
