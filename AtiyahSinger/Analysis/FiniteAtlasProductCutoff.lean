/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.TensorCutoffGlobalSymbol

/-!
# Dominant frequencies in the actual finite tensor atlas

Public module ID: M0619.

One positive cutoff parameter works simultaneously in all the fixed charts.
When the first metric frequency dominates, every active first-factor cutoff
equals one. The total scalar weight of the actual PDO symbol is therefore one,
using only the original partition identity, including signed partitions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The SG cutoff retains a first frequency that dominates the scaled second frequency. -/
theorem productFrequencyCutoff_eq_one_of_mul_le
    (ε r s : ℝ) (hε : 0 < ε) (hr : 0 ≤ r) (hs : 0 ≤ s) (h : ε * s ≤ r) :
    productFrequencyCutoff ε r s = 1 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hpzero (t : ℝ) (ht : |t| ≤ 1) : productCutoffProfile t = 0 := by
    change 1 - bump t = 0
    rw [bump.one_of_mem_closedBall]
    · simp
    · simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using ht
  by_cases hz : r = 0
  · have hsz : s = 0 := by nlinarith
    subst r
    subst s
    simp [productFrequencyCutoff, hpzero 0 (by norm_num)]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hn : 0 ≤ ε * s / r := div_nonneg (mul_nonneg hε.le hs) hr
    have hl : ε * s / r ≤ 1 := (div_le_one hrpos).mpr h
    rw [productFrequencyCutoff, ite_eq_right hz,
      hpzero (ε * s / r) (by rwa [abs_of_nonneg hn])]
    simp

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedAddCommGroup (E₁ x)]
  [∀ x, NormedAddCommGroup (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]

/-- A sufficiently small common parameter preserves the full first-factor atlas weight
whenever its metric frequency dominates. No positivity of partition weights is assumed. -/
theorem QuantizationPresentation.exists_productCutoffWeight_sum_eq_one
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ (x : M) (y : N) (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ),
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
        let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
        let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
        k.length y ξ₂ ≤ g.length x ξ₁ →
          ∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ = 1 := by
  classical
  obtain ⟨C, hC, hA⟩ := A.exists_covectorInChart_norm_bounds g
  obtain ⟨D, hD, hB⟩ := B.exists_covectorInChart_norm_bounds k
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hCDpos : 0 < C * D := mul_pos hCpos hDpos
  have hCD : 1 ≤ C * D := by nlinarith
  refine ⟨(C * D)⁻¹, inv_pos.mpr hCDpos, (inv_le_one₀ hCDpos).mpr hCD, ?_⟩
  intro ε hε hεδ x y ξ
  dsimp only
  intro hdom
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  have hεCD : ε * (C * D) ≤ 1 := by
    calc
      ε * (C * D) ≤ (C * D)⁻¹ * (C * D) :=
        mul_le_mul_of_nonneg_right hεδ hCDpos.le
      _ = 1 := inv_mul_cancel₀ hCDpos.ne'
  -- The same metric comparison constant controls every active patch pair.
  have hlocal (i : Fin A.size) (j : Fin B.size) :
      (A.patch i).productCutoffWeight (B.patch j) ε x y ξ =
        (A.patch i).weight x * (B.patch j).weight y := by
    by_cases ha : (A.patch i).weight x = 0
    · simp [QuantizationPatch.productCutoffWeight, ha]
    by_cases hb : (B.patch j).weight y = 0
    · simp [QuantizationPatch.productCutoffWeight, hb]
    let r := ‖covectorInChart (A.patch i).chart x ξ₁‖
    let s := ‖covectorInChart (B.patch j).chart y ξ₂‖
    have hAr := (hA i x ha ξ₁).1
    have hBs := (hB j y hb ξ₂).2
    have hratio : ε * s ≤ r := by
      calc
        ε * s ≤ ε * (D * k.length y ξ₂) := mul_le_mul_of_nonneg_left hBs hε.le
        _ ≤ ε * (D * g.length x ξ₁) := by gcongr
        _ ≤ ε * (D * (C * r)) := by gcongr
        _ = (ε * (C * D)) * r := by ring
        _ ≤ 1 * r := mul_le_mul_of_nonneg_right hεCD (norm_nonneg _)
        _ = r := one_mul r
    have hcut := productFrequencyCutoff_eq_one_of_mul_le ε r s hε
      (norm_nonneg _) (norm_nonneg _) hratio
    change (A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s = _
    rw [hcut, mul_one]
  -- Saturation makes the original partition identities exact even for signed weights.
  simp only [hlocal, ← Finset.mul_sum, B.sum_weight, mul_one, A.sum_weight]

end AtiyahSinger
