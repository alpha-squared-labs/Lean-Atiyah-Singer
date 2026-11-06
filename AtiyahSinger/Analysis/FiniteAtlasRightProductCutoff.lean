/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteAtlasProductCutoff
public import AtiyahSinger.Analysis.RightTensorCutoffGlobalSymbol

/-!
# Dominant frequencies in the actual finite tensor atlas

Public module ID: M0621.

One positive cutoff parameter works simultaneously in all the fixed charts.
When the second metric frequency dominates, every active second-factor cutoff
equals one. The total scalar weight of the actual PDO symbol is therefore one,
using only the original partition identity, including signed partitions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {F₀ F₁ : N → Type*} {E : M → Type*}
  [∀ y, NormedAddCommGroup (F₀ y)] [∀ y, NormedAddCommGroup (F₁ y)]
  [∀ y, NormedAddCommGroup (E y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]

/-- A sufficiently small common parameter preserves the full second-factor atlas weight
whenever its metric frequency dominates. No positivity of partition weights is assumed. -/
theorem QuantizationPresentation.exists_rightProductCutoffWeight_sum_eq_one
    (A : QuantizationPresentation (n := m) (r := s₀) (q := s₁) F₀ F₁)
    (B : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (g : SmoothCotangentMetric (n := m) (M := N))
    (k : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ (y : N) (x : M) (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ),
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
        let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
        let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
        k.length x ξ₂ ≤ g.length y ξ₁ →
          ∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε y x ξ = 1 := by
  classical
  obtain ⟨C, hC, hA⟩ := A.exists_covectorInChart_norm_bounds g
  obtain ⟨D, hD, hB⟩ := B.exists_covectorInChart_norm_bounds k
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hCDpos : 0 < C * D := mul_pos hCpos hDpos
  have hCD : 1 ≤ C * D := by nlinarith
  refine ⟨(C * D)⁻¹, inv_pos.mpr hCDpos, (inv_le_one₀ hCDpos).mpr hCD, ?_⟩
  intro ε hε hεδ y x ξ
  dsimp only
  intro hdom
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  have hεCD : ε * (C * D) ≤ 1 := by
    calc
      ε * (C * D) ≤ (C * D)⁻¹ * (C * D) :=
        mul_le_mul_of_nonneg_right hεδ hCDpos.le
      _ = 1 := inv_mul_cancel₀ hCDpos.ne'
  -- The same metric comparison constant controls every active patch pair.
  have hlocal (i : Fin A.size) (j : Fin B.size) :
      (A.patch i).rightProductCutoffWeight (B.patch j) ε y x ξ =
        (A.patch i).weight y * (B.patch j).weight x := by
    by_cases ha : (A.patch i).weight y = 0
    · simp [QuantizationPatch.rightProductCutoffWeight, ha]
    by_cases hb : (B.patch j).weight x = 0
    · simp [QuantizationPatch.rightProductCutoffWeight, hb]
    let ρ := ‖covectorInChart (A.patch i).chart y ξ₁‖
    let σ := ‖covectorInChart (B.patch j).chart x ξ₂‖
    have hAr := (hA i y ha ξ₁).1
    have hBs := (hB j x hb ξ₂).2
    have hratio : ε * σ ≤ ρ := by
      calc
        ε * σ ≤ ε * (D * k.length x ξ₂) := mul_le_mul_of_nonneg_left hBs hε.le
        _ ≤ ε * (D * g.length y ξ₁) := by gcongr
        _ ≤ ε * (D * (C * ρ)) := by gcongr
        _ = (ε * (C * D)) * ρ := by ring
        _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hεCD (norm_nonneg _)
        _ = ρ := one_mul ρ
    have hcut := productFrequencyCutoff_eq_one_of_mul_le ε ρ σ hε
      (norm_nonneg _) (norm_nonneg _) hratio
    change (A.patch i).weight y * (B.patch j).weight x * productFrequencyCutoff ε ρ σ = _
    rw [hcut, mul_one]
  -- Saturation makes the original partition identities exact even for signed weights.
  simp only [hlocal, ← Finset.mul_sum, B.sum_weight, mul_one, A.sum_weight]

end AtiyahSinger
