/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The original scalar Schwartz tensor test

Public module ID: M0952.

The literal product of two scalar Schwartz functions on the same Euclidean
space is a Schwartz function on the product. This fixed external product
provides the tensor tests used in the construction and comparison of
tempered kernels.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ComplexConjugate ContDiff SchwartzMap

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The pointwise external product of two scalar Schwartz tests is again a Schwartz test. -/
theorem exists_schwartzTensor (φ ψ : 𝓢(V, ℂ)) :
    ∃ f : 𝓢(V × V, ℂ), ∀ z : V × V, f z = φ z.1 * ψ z.2 := by
  /- Stage 1: the function (x,y) ↦ φ(x)ψ(y) is smooth by the product rule.
  Each mixed derivative is a finite sum of products of derivatives of the
  two factors. Stage 2: the product norm is the maximum of the two norms.
  Bound each polynomial weight by the sum of the corresponding factor
  weights and use the two Schwartz decay bounds. These estimates provide
  the actual SchwartzMap smoothness and decay fields, with this function. -/
  -- Projection pullback does not increase any derivative norm.
  have hproj (f : 𝓢(V, ℂ)) (p : V × V →L[ℝ] V) (hp : ‖p‖ ≤ 1)
      (i : ℕ) (z : V × V) :
      ‖iteratedFDeriv ℝ i (f ∘ p) z‖ ≤ ‖iteratedFDeriv ℝ i f (p z)‖ := by
    rw [p.iteratedFDeriv_comp_right (f.smooth ⊤) z (by simp)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i f (p z)‖ * ∏ _ : Fin i, ‖p‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ i f (p z)‖ * ∏ _ : Fin i, (1 : ℝ) := by
        gcongr
      _ = ‖iteratedFDeriv ℝ i f (p z)‖ := by simp
  have hφ : ContDiff ℝ ∞ (fun z : V × V ↦ φ z.1) :=
    (φ.smooth ⊤).comp contDiff_fst
  have hψ : ContDiff ℝ ∞ (fun z : V × V ↦ ψ z.2) :=
    (ψ.smooth ⊤).comp contDiff_snd
  refine ⟨⟨fun z ↦ φ z.1 * ψ z.2, hφ.mul hψ, ?_⟩, fun _ ↦ rfl⟩
  intro k j
  -- Leibniz bounds each derivative by finitely many products of factor derivatives.
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (j - i) ψ +
      SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (j - i) ψ), ?_⟩
  intro z
  have hweight : ‖z‖ ^ k ≤ ‖z.1‖ ^ k + ‖z.2‖ ^ k := by
    rw [Prod.norm_def]
    rcases le_total ‖z.1‖ ‖z.2‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
  calc
    ‖z‖ ^ k * ‖iteratedFDeriv ℝ j (fun z : V × V ↦ φ z.1 * ψ z.2) z‖ ≤
        ‖z‖ ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun z : V × V ↦ φ z.1) z‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun z : V × V ↦ ψ z.2) z‖ := by
      gcongr
      exact norm_iteratedFDeriv_mul_le hφ hψ z (by simp)
    _ ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i φ z.1‖ * ‖iteratedFDeriv ℝ (j - i) ψ z.2‖ := by
      gcongr with i hi
      · exact hproj φ (ContinuousLinearMap.fst ℝ V V)
          (ContinuousLinearMap.norm_fst_le ..) i z
      · exact hproj ψ (ContinuousLinearMap.snd ℝ V V)
          (ContinuousLinearMap.norm_snd_le ..) (j - i) z
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (‖z‖ ^ k * (‖iteratedFDeriv ℝ i φ z.1‖ *
            ‖iteratedFDeriv ℝ (j - i) ψ z.2‖)) := by
      rw [Finset.mul_sum]
      congr 1
      funext i
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ (‖z.1‖ ^ k + ‖z.2‖ ^ k) *
            (‖iteratedFDeriv ℝ i φ z.1‖ * ‖iteratedFDeriv ℝ (j - i) ψ z.2‖) := by
          gcongr
        _ = (‖z.1‖ ^ k * ‖iteratedFDeriv ℝ i φ z.1‖) *
              ‖iteratedFDeriv ℝ (j - i) ψ z.2‖ +
            ‖iteratedFDeriv ℝ i φ z.1‖ *
              (‖z.2‖ ^ k * ‖iteratedFDeriv ℝ (j - i) ψ z.2‖) := by ring
        _ ≤ _ := by
          gcongr
          · exact SchwartzMap.le_seminorm ℂ k i φ z.1
          · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ (j - i) z.2
          · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ i z.1
          · exact SchwartzMap.le_seminorm ℂ k (j - i) ψ z.2

/-- The actual scalar tensor test, with value φ(x)ψ(y). -/
def schwartzTensor (φ ψ : 𝓢(V, ℂ)) : 𝓢(V × V, ℂ) :=
  (exists_schwartzTensor φ ψ).choose

/-- The external tensor test retains its literal two-variable function. -/
theorem schwartzTensor_apply (φ ψ : 𝓢(V, ℂ)) (z : V × V) :
    schwartzTensor φ ψ z = φ z.1 * ψ z.2 := by
  /- Read the pointwise formula from the same existence witness selected
  by schwartzTensor. Its underlying function is the original external
  product; only the Schwartz smoothness and decay certificates are packaged. -/
  exact (exists_schwartzTensor φ ψ).choose_spec z

end AtiyahSinger
