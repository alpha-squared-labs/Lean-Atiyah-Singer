/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.JointFrequencyQuantizationBound

/-!
# Resolvent decay for the original compactly localized quantizer

Public module ID: M0769.

A joint symbol of order minus two gives decay by `1 / (1 + t)` for the original
order-zero Sobolev quantizer. The scalar parameter factor is retained while
estimating every finite seminorm used by the quantization theorem. This proves
operator norm decay, rather than only integrability at individual spatial points.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

/-- The same localized order-zero Sobolev quantizer has resolvent decay in the parameter. -/
theorem exists_decay_quantizeSobolev_jointFrequencySymbolSlice
    {n r q : ℕ} (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (a : SymbolFunction (n + 1) r q) (ha : IsSymbol W (-2) a)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, EuclideanSpace.finAddEquivProd.symm
      (x, (0 : EuclideanSpace ℝ (Fin 1))) ∈ W)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ U) (s : ℝ) :
    ∃ hslice : ∀ t : ℝ, 0 < t → IsSymbol U 0 (jointFrequencySymbolSlice a t),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ht : 0 < t),
        ‖quantizeSobolev 0 s (zeroExtendedSymbol U χ (jointFrequencySymbolSlice a t))
          (isSymbol_zeroExtendedSymbol U hU 0 χ hχ hcχ hsχ
            (jointFrequencySymbolSlice a t) (hslice t ht))
          (hasCompactSupport_zeroExtendedSymbol U χ (jointFrequencySymbolSlice a t) hcχ)‖ ≤
          C / (1 + t) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let split : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
      X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  obtain ⟨hnegative, _⟩ := exists_uniform_quantizeSobolev_jointFrequencySymbolSlice
    W hW (-2) s (by norm_num) a ha U hU hUW χ hχ hcχ hsχ
  have hslice (t : ℝ) (ht : 0 < t) : IsSymbol U 0 (jointFrequencySymbolSlice a t) :=
    (hnegative t ht).mono (by norm_num)
  -- Keep one complete joint denominator for parameter decay, before the frequency comparison.
  have hweight (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (t : ℝ) (ht : 0 < t) :
      (1 + R ^ 2 + t) ^ ((-2 - (k : ℝ)) / 2) ≤
        (2 ^ (k : ℝ) / (1 + t)) * (1 + R) ^ (-(k : ℝ)) := by
    let b : ℝ := Real.sqrt (1 + R ^ 2 + t)
    have hb₀ : 0 ≤ b := Real.sqrt_nonneg _
    have hb₂ : b ^ 2 = 1 + R ^ 2 + t := Real.sq_sqrt (by positivity)
    have hb₁ : 1 ≤ b := by nlinarith
    have hbR : R ≤ b := by nlinarith
    have hb : 0 < b := zero_lt_one.trans_le hb₁
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcomp : (2 * b) ^ (-(k : ℝ)) ≤ (1 + R) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hfreq : (1 + R ^ 2 + t) ^ (-(k : ℝ) / 2) ≤
        2 ^ (k : ℝ) * (1 + R) ^ (-(k : ℝ)) := by
      rw [Real.rpow_div_two_eq_sqrt (-(k : ℝ)) (by positivity)]
      change b ^ (-(k : ℝ)) ≤ _
      calc
        _ = 2 ^ (k : ℝ) * (2 * b) ^ (-(k : ℝ)) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb.le,
            ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            add_neg_cancel, Real.rpow_zero, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (by positivity)
    have hdecay : (1 + R ^ 2 + t)⁻¹ ≤ (1 + t)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by linarith : 0 < 1 + t)
          (by nlinarith [sq_nonneg R] : 1 + t ≤ 1 + R ^ 2 + t))
    rw [show (-2 - (k : ℝ)) / 2 = -1 + -(k : ℝ) / 2 by ring,
      Real.rpow_add (by positivity), Real.rpow_neg_one]
    calc
      _ ≤ (1 + t)⁻¹ * (2 ^ (k : ℝ) * (1 + R) ^ (-(k : ℝ))) :=
        mul_le_mul hdecay hfreq (by positivity) (by positivity)
      _ = _ := by ring
  have hbound (K : Set X) (hKU : K ⊆ U) (hK : IsCompact K) (i k : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (jointFrequencySymbolSlice a t) i k x ξ‖ ≤
          (C / (1 + t)) * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    have hKW : (fun x : X ↦ split.symm (x, 0)) '' K ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      exact hUW x (hKU hx)
    obtain ⟨C, hC, hest⟩ :=
      exists_bound_jointFrequencySymbolSlice W hW (-2) a ha K hK hKW i k
    refine ⟨C * 2 ^ (k : ℝ), mul_nonneg hC (by positivity), ?_⟩
    intro t ht x hx ξ
    calc
      _ ≤ C * (1 + ‖ξ‖ ^ 2 + t) ^ ((-2 - (k : ℝ)) / 2) := hest t ht x hx ξ
      _ ≤ C * ((2 ^ (k : ℝ) / (1 + t)) * (1 + ‖ξ‖) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left (hweight ‖ξ‖ (norm_nonneg _) k t ht) hC
      _ = _ := by ring
  -- Every original seminorm has one numerator independent of the positive parameter.
  have hsemi (J : SymbolSeminormIndex U) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ) (ht : 0 < t),
        symbolSeminorm hU 0 J ⟨jointFrequencySymbolSlice a t, hslice t ht⟩ ≤
          B / (1 + t) := by
    obtain ⟨B, hB, hest⟩ := hbound J.compactSet J.subset_domain J.isCompact
      J.spatialOrder J.frequencyOrder
    refine ⟨B, hB, ?_⟩
    intro t ht
    change symbolSeminormValue hU 0 J ⟨jointFrequencySymbolSlice a t, hslice t ht⟩ ≤ _
    by_cases hK : J.compactSet.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hK
      apply csSup_le
      · exact ⟨_, x₀, hx₀, (0 : X), rfl⟩
      · rintro v ⟨x, hx, ξ, rfl⟩
        apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
        simpa only [zero_sub] using hest t ht x hx ξ
    · have hnonneg : 0 ≤ B / (1 + t) := div_nonneg hB (by linarith)
      simpa [symbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK] using hnonneg
  obtain ⟨J, c, hquant⟩ := exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
    (r := r) (q := q) U hU 0 s χ hχ hcχ hsχ
  choose b hb hbsemi using hsemi
  let B : ℝ := ∑ j ∈ J, b j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ ↦ hb j)
  have hsup (t : ℝ) (ht : 0 < t) :
      (J.sup (symbolSeminorm hU 0)) ⟨jointFrequencySymbolSlice a t, hslice t ht⟩ ≤
        B / (1 + t) := by
    apply Seminorm.finset_sup_apply_le (div_nonneg hB (by linarith))
    intro j hj
    exact (hbsemi j t ht).trans (div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun k _ ↦ hb k) hj) (by linarith))
  refine ⟨hslice, (c : ℝ) * B, mul_nonneg c.coe_nonneg hB, ?_⟩
  intro t ht
  let b := zeroExtendedSymbol U χ (jointFrequencySymbolSlice a t)
  have hb : IsSymbol Set.univ 0 b :=
    isSymbol_zeroExtendedSymbol U hU 0 χ hχ hcχ hsχ _ (hslice t ht)
  have hcb : HasCompactSupport b := hasCompactSupport_zeroExtendedSymbol U χ _ hcχ
  let T := quantizeSobolev 0 s b hb hcb
  -- Identify the same operator on original Schwartz coordinates, then use density.
  have hT (u : 𝓢(X, V)) : T (schwartzSobolevCoordinate s u) =
      schwartzSobolevCoordinate (s - 0) (quantizeSchwartz 0 b hb hcb u) := by
    apply besselRealization_injective n q (s - 0)
    ext1 φ
    rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
      SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [quantizeSchwartz_apply]
  have hnorm (u : 𝓢(X, V)) :
      ‖T (schwartzSobolevCoordinate s u)‖ ≤
        (((c : ℝ) * B) / (1 + t)) * ‖schwartzSobolevCoordinate s u‖ := by
    rw [hT]
    have h := (hquant ⟨jointFrequencySymbolSlice a t, hslice t ht⟩ u).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsup t ht) c.coe_nonneg) (norm_nonneg _))
    simpa only [mul_div_assoc] using h
  change ‖T‖ ≤ ((c : ℝ) * B) / (1 + t)
  apply T.opNorm_le_bound (div_nonneg (mul_nonneg c.coe_nonneg hB) (by linarith))
  intro z
  exact (denseRange_schwartzSobolevCoordinate n r s).induction_on z
    (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) hnorm

end AtiyahSinger
