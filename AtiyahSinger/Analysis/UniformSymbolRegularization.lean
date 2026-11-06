/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol

/-!
# Uniform metric recovery of a fixed global regularization

Public module ID: M1045.

The finite atlas regularization equals its original Hom function whenever
the specified metric covector length is at least one common radius. The radius
works for every Hom function. Signed partition weights are allowed; the
argument uses their sum and saturation of each active frequency cutoff.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- A fixed finite regularization recovers every original symbol beyond one metric radius. -/
theorem QuantizationPresentation.exists_regularizedSymbolFunction_eq_of_length_ge
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ a : GlobalSymbolFunction (n := n) E F, ∀ x ξ,
      R ≤ g.length x ξ → A.regularizedSymbolFunction a x ξ = a x ξ := by
  classical
  obtain ⟨R, hR, hbound⟩ := A.exists_covectorInChart_norm_bounds g
  refine ⟨R, hR, ?_⟩
  intro a x ξ hξ
  have hterm (j : Fin A.size) :
      (A.patch j).weight x * highFrequencyCutoff n
        (covectorInChart (A.patch j).chart x ξ) = (A.patch j).weight x := by
    by_cases hw : (A.patch j).weight x = 0
    · simp only [hw, zero_mul]
    · have hnorm : 1 ≤ ‖covectorInChart (A.patch j).chart x ξ‖ := by
        have h := (hbound j x hw ξ).1
        have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
        nlinarith
      rw [highFrequencyCutoff_eq_one _ hnorm, mul_one]
  -- All active cutoffs saturate together; the original signed partition reconstructs a.
  simp only [QuantizationPresentation.regularizedSymbolFunction, hterm]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_weight, Complex.ofReal_one, one_smul]

end AtiyahSinger
