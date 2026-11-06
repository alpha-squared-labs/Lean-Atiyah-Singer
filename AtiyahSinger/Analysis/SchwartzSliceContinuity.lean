/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzKernelExistence
public import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Continuous Schwartz slices on a common compact support

Public module ID: M0951.

Restriction to a fixed affine slice is a continuous map on the original
Schwartz spaces. With a common compact support in the remaining variable,
the slice also varies continuously with its fixed coordinate and with the
original Schwartz function. This is the continuity input for applying two
localized PDO functionals in independent variables.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff SchwartzMap

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Restriction to the original affine slice, with its exact Schwartz function. -/
def schwartzSliceCLM (x : X) : 𝓢(X × Y, ℂ) →L[ℂ] 𝓢(Y, ℂ) := by
  have hg : (fun y : Y ↦ (x, y)).HasTemperateGrowth := by
    convert (ContinuousLinearMap.inr ℝ X Y).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const (x, (0 : Y))) using 1
    funext y
    simp
  exact SchwartzMap.compCLM ℂ hg ⟨1, 1, fun y ↦ by
    simpa only [one_mul, pow_one] using
      (norm_snd_le (x, y)).trans (le_add_of_nonneg_left zero_le_one)⟩

/-- A continuous Schwartz family with common remaining-variable support has continuous slices. -/
theorem continuous_schwartzSlice_of_common_compact_support
    {P : Type*} [TopologicalSpace P] (F : P → 𝓢(X × Y, ℂ)) (hF : Continuous F)
    (K : Set Y) (hK : IsCompact K)
    (hsupport : ∀ p, tsupport (F p) ⊆ Prod.snd ⁻¹' K) :
    Continuous (fun p : P × X ↦ schwartzSliceCLM p.2 (F p.1)) := by
  -- Slice supports stay in the specified compact set, independently of both parameters.
  apply continuous_schwartzMap_of_common_compact_support _ K hK ?_ ?_
  · intro p
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    exact hsupport p.1 (subset_tsupport (F p.1) hy)
  · intro j
    let R : ((X × Y) [×j]→L[ℝ] ℂ) →L[ℝ] Y [×j]→L[ℝ] ℂ :=
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin j ↦ ContinuousLinearMap.inr ℝ X Y)
    have hc : Continuous (fun p : (P × X) × Y ↦
        R (iteratedFDeriv ℝ j (F p.1.1) (p.1.2, p.2))) :=
      R.continuous.comp ((continuous_iteratedFDeriv_schwartz j).comp
        ((hF.comp continuous_fst.fst).prodMk (continuous_fst.snd.prodMk continuous_snd)))
    -- Affine translation leaves derivatives unchanged; the linear slice restricts each argument.
    convert hc using 1
    funext p
    have hfun : (schwartzSliceCLM p.1.2 (F p.1.1) : Y → ℂ) =
        (fun z : X × Y ↦ F p.1.1 ((p.1.2, 0) + z)) ∘
          ContinuousLinearMap.inr ℝ X Y := by
      funext y
      simp only [schwartzSliceCLM, SchwartzMap.compCLM_apply, Function.comp_apply,
        ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
    have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ F p.1.1 ((p.1.2, 0) + z)) :=
      ((F p.1.1).smooth ⊤).comp (contDiff_const.add contDiff_id)
    rw [hfun, (ContinuousLinearMap.inr ℝ X Y).iteratedFDeriv_comp_right hs p.2 (by simp),
      iteratedFDeriv_comp_add_left]
    simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
    rfl

end AtiyahSinger
