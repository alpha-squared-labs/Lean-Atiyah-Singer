/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolQuotient

import all AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Uniform estimates for positive frequency scaling

Public module ID: M2281.

For an order-zero symbol, replacing the frequency by `t` times that frequency preserves
the symbol estimates uniformly for `0 < t ≤ 1`. One extra frequency derivative supplies
a factor of `t` in the weaker weighted estimate. These are the symbol estimates used in
small-parameter composition bounds, derived from the standard type-(1,0) estimates and
the linear chain rule. Taylor, *Pseudodifferential Operators*, II.7, p. 53, discusses the
bounded scaled family. The explicit extra-derivative estimate here is a project supplement.
No convergence at `t = 0` in the full symbol or operator norm topology is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

variable {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The original symbol with its frequency argument multiplied by a real parameter. -/
def frequencyScaleSymbol (t : ℝ) (a : SymbolFunction n r q) : SymbolFunction n r q :=
  fun x ξ ↦ a x (t • ξ)

/-- Positive frequency contractions preserve order-zero symbol bounds with the same constants. -/
theorem IsSymbol.frequencyScale {a : SymbolFunction n r q} (ha : IsSymbol U 0 a)
    (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) : IsSymbol U 0 (frequencyScaleSymbol t a) := by
  /- The linear frequency substitution preserves smoothness on the same base domain.
  Its j-th derivative contributes t^j; compare t(1+norm ξ) with 1+t norm ξ
  before dividing by the positive frequency weights. The estimate is uniform in t. -/
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry (frequencyScaleSymbol t a))
      (U ×ˢ Set.univ) :=
    ha.1.comp (contDiff_fst.prodMk (contDiff_snd.const_smul t)).contDiffOn
      (fun z hz ↦ ⟨hz.1, Set.mem_univ _⟩)
  refine ⟨hsmooth, ?_⟩
  intro K hKU hK i j
  obtain ⟨C, hC, hbound⟩ := ha.2 K hKU hK i j
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  -- Use the existing exact mixed chain rule on the same totalized symbol function.
  have hderiv : symbolDerivative (frequencyScaleSymbol t a) i j x ξ =
      t ^ j • symbolDerivative a i j x (t • ξ) :=
    mixed_iteratedFDeriv_frequency_smul a t ht.ne' i j x ξ
  have hratio : t ^ j / (1 + t * ‖ξ‖) ^ j ≤ 1 / (1 + ‖ξ‖) ^ j := by
    apply (div_le_div_iff₀ (pow_pos (by positivity) j) (pow_pos (by positivity) j)).mpr
    have hcomparison := pow_le_pow_left₀
      (show 0 ≤ t * (1 + ‖ξ‖) by positivity)
      (show t * (1 + ‖ξ‖) ≤ 1 + t * ‖ξ‖ by nlinarith) j
    simpa only [mul_pow, one_mul] using hcomparison
  have hscaled : ‖symbolDerivative a i j x (t • ξ)‖ ≤
      C * (1 + ‖t • ξ‖) ^ (-(j : ℝ)) := by
    simpa only [zero_sub] using hbound x hx (t • ξ)
  calc
    ‖symbolDerivative (frequencyScaleSymbol t a) i j x ξ‖ =
        t ^ j * ‖symbolDerivative a i j x (t • ξ)‖ := by
      rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le j)]
    _ ≤ t ^ j * (C * (1 + ‖t • ξ‖) ^ (-(j : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (pow_nonneg ht.le j)
    _ = C * (t ^ j / (1 + t * ‖ξ‖) ^ j) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    _ ≤ C * (1 / (1 + ‖ξ‖) ^ j) := mul_le_mul_of_nonneg_left hratio hC
    _ = C * (1 + ‖ξ‖) ^ (0 - (j : ℝ)) := by
      rw [zero_sub, Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring

/-- An extra frequency derivative gives a uniform small-parameter factor in order-zero weights. -/
theorem IsSymbol.exists_frequencyScale_derivative_bound {a : SymbolFunction n r q}
    (ha : IsSymbol U 0 a) (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U)
    (hK : IsCompact K) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (frequencyScaleSymbol t a) i (j + 1) x ξ‖ ≤
        C * t * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
  /- Retain one additional frequency derivative in the original symbol estimate.
  The chain rule then leaves one factor of t after comparison of the other j weights.
  Choose the constant before the parameter, base point and frequency. -/
  obtain ⟨C, hC, hbound⟩ := ha.2 K hKU hK i (j + 1)
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x hx ξ
  have hderiv : symbolDerivative (frequencyScaleSymbol t a) i (j + 1) x ξ =
      t ^ (j + 1) • symbolDerivative a i (j + 1) x (t • ξ) :=
    mixed_iteratedFDeriv_frequency_smul a t ht.ne' i (j + 1) x ξ
  have hratio : t ^ (j + 1) / (1 + t * ‖ξ‖) ^ (j + 1) ≤
      t / (1 + ‖ξ‖) ^ j := by
    apply (div_le_div_iff₀ (pow_pos (by positivity) (j + 1))
      (pow_pos (by positivity) j)).mpr
    have hcomparison : t ^ j * (1 + ‖ξ‖) ^ j ≤ (1 + t * ‖ξ‖) ^ j := by
      simpa only [mul_pow] using pow_le_pow_left₀
        (show 0 ≤ t * (1 + ‖ξ‖) by positivity)
        (show t * (1 + ‖ξ‖) ≤ 1 + t * ‖ξ‖ by nlinarith) j
    calc
      t ^ (j + 1) * (1 + ‖ξ‖) ^ j = t * (t ^ j * (1 + ‖ξ‖) ^ j) := by
        rw [pow_succ]
        ring
      _ ≤ t * (1 + t * ‖ξ‖) ^ j := mul_le_mul_of_nonneg_left hcomparison ht.le
      _ ≤ t * (1 + t * ‖ξ‖) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) (Nat.le_succ j)) ht.le
  have hscaled : ‖symbolDerivative a i (j + 1) x (t • ξ)‖ ≤
      C * (1 + ‖t • ξ‖) ^ (-((j + 1 : ℕ) : ℝ)) := by
    simpa only [zero_sub] using hbound x hx (t • ξ)
  -- Convert the positive real weights to natural powers and divide after comparison.
  calc
    ‖symbolDerivative (frequencyScaleSymbol t a) i (j + 1) x ξ‖ =
        t ^ (j + 1) * ‖symbolDerivative a i (j + 1) x (t • ξ)‖ := by
      rw [hderiv, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg ht.le (j + 1))]
    _ ≤ t ^ (j + 1) * (C * (1 + ‖t • ξ‖) ^ (-((j + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (pow_nonneg ht.le (j + 1))
    _ = C * (t ^ (j + 1) / (1 + t * ‖ξ‖) ^ (j + 1)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    _ ≤ C * (t / (1 + ‖ξ‖) ^ j) := mul_le_mul_of_nonneg_left hratio hC
    _ = C * t * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring

end AtiyahSinger
