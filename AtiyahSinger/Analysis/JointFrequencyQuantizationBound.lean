/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.JointFrequencySymbolRestriction
public import AtiyahSinger.Analysis.QuantizationBounds

/-!
# Uniform Sobolev bounds for the actual joint-frequency quantizer

Public module ID: M0767.

A fixed compact spatial cutoff and a nonpositive-order symbol in one additional
frequency give one Sobolev norm bound for every positive parameter. All constants
are selected before the parameter; the bounded operator is the original named
quantizer, with its original Bessel coordinates and Fourier normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff NNReal SchwartzMap Topology

/-- Joint-frequency estimates give a parameter-independent norm bound for the same
compactly localized Sobolev quantizer. The returned symbol proofs retain its actual family. -/
theorem exists_uniform_quantizeSobolev_jointFrequencySymbolSlice
    {n r q : ℕ} (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (m s : ℝ) (hm : m ≤ 0) (a : SymbolFunction (n + 1) r q) (ha : IsSymbol W m a)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, EuclideanSpace.finAddEquivProd.symm
      (x, (0 : EuclideanSpace ℝ (Fin 1))) ∈ W)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ U) :
    ∃ hslice : ∀ τ : ℝ, 0 < τ → IsSymbol U m (jointFrequencySymbolSlice a τ),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (hτ : 0 < τ),
        ‖quantizeSobolev m s (zeroExtendedSymbol U χ (jointFrequencySymbolSlice a τ))
          (isSymbol_zeroExtendedSymbol U hU m χ hχ hcχ hsχ
            (jointFrequencySymbolSlice a τ) (hslice τ hτ))
          (hasCompactSupport_zeroExtendedSymbol U χ (jointFrequencySymbolSlice a τ) hcχ)‖ ≤
          C := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let split : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
      X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  -- Negative powers permit a uniform comparison with the ordinary symbol weight.
  have hweight (R e τ : ℝ) (hR : 0 ≤ R) (he : e ≤ 0) (hτ : 0 < τ) :
      (1 + R ^ 2 + τ) ^ (e / 2) ≤ 2 ^ (-e) * (1 + R) ^ e := by
    let b : ℝ := Real.sqrt (1 + R ^ 2 + τ)
    have hb₀ : 0 ≤ b := Real.sqrt_nonneg _
    have hb₂ : b ^ 2 = 1 + R ^ 2 + τ := Real.sq_sqrt (by positivity)
    have hb₁ : 1 ≤ b := by nlinarith
    have hbR : R ≤ b := by nlinarith
    have hb : 0 < b := zero_lt_one.trans_le hb₁
    have hcomp : (2 * b) ^ e ≤ (1 + R) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he
    rw [Real.rpow_div_two_eq_sqrt e (by positivity)]
    change b ^ e ≤ _
    calc
      b ^ e = 2 ^ (-e) * (2 * b) ^ e := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb.le,
          ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (by positivity)
  have hbound (K : Set X) (hKU : K ⊆ U) (hK : IsCompact K) (i j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (jointFrequencySymbolSlice a τ) i j x ξ‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
    have hKW : (fun x : X ↦ split.symm (x, 0)) '' K ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      exact hUW x (hKU hx)
    obtain ⟨C, hC, hest⟩ := exists_bound_jointFrequencySymbolSlice W hW m a ha K hK hKW i j
    refine ⟨C * 2 ^ (-(m - (j : ℝ))), mul_nonneg hC (by positivity), ?_⟩
    intro τ hτ x hx ξ
    calc
      _ ≤ C * (1 + ‖ξ‖ ^ 2 + τ) ^ ((m - (j : ℝ)) / 2) := hest τ hτ x hx ξ
      _ ≤ C * (2 ^ (-(m - (j : ℝ))) * (1 + ‖ξ‖) ^ (m - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (hweight ‖ξ‖ (m - (j : ℝ)) τ (norm_nonneg _)
            (sub_nonpos.mpr (hm.trans (Nat.cast_nonneg _))) hτ) hC
      _ = _ := by ring
  have hslice (τ : ℝ) (hτ : 0 < τ) : IsSymbol U m (jointFrequencySymbolSlice a τ) := by
    refine ⟨?_, ?_⟩
    · have hb : ContDiff ℝ ∞ (fun z : X × X ↦ split.symm (z.1, 0)) :=
        split.symm.contDiff.comp (contDiff_fst.prodMk contDiff_const)
      have hf : ContDiff ℝ ∞ (fun z : X × X ↦ split.symm
          (z.2, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ))) :=
        split.symm.contDiff.comp (contDiff_snd.prodMk contDiff_const)
      exact ha.1.comp (hb.contDiffOn.prodMk hf.contDiffOn)
        (fun z hz ↦ ⟨hUW z.1 hz.1, Set.mem_univ _⟩)
    · intro K hKU hK i j
      obtain ⟨C, hC, hest⟩ := hbound K hKU hK i j
      exact ⟨C, hC, hest τ hτ⟩
  -- Each original symbol seminorm is bounded before selecting the positive parameter.
  have hsemi (J : SymbolSeminormIndex U) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (hτ : 0 < τ),
        symbolSeminorm hU m J ⟨jointFrequencySymbolSlice a τ, hslice τ hτ⟩ ≤ B := by
    obtain ⟨B, hB, hest⟩ := hbound J.compactSet J.subset_domain J.isCompact
      J.spatialOrder J.frequencyOrder
    refine ⟨B, hB, ?_⟩
    intro τ hτ
    change symbolSeminormValue hU m J ⟨jointFrequencySymbolSlice a τ, hslice τ hτ⟩ ≤ B
    by_cases hK : J.compactSet.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hK
      apply csSup_le
      · refine ⟨_, x₀, hx₀, (0 : X), rfl⟩
      · rintro t ⟨x, hx, ξ, rfl⟩
        exact (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
          (hest τ hτ x hx ξ)
    · simpa [symbolSeminormValue, Set.not_nonempty_iff_eq_empty.mp hK] using hB
  obtain ⟨J, c, hquant⟩ := exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
    (r := r) (q := q) U hU m s χ hχ hcχ hsχ
  choose b hb hbsemi using hsemi
  let B : ℝ := ∑ j ∈ J, b j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ ↦ hb j)
  have hsup (τ : ℝ) (hτ : 0 < τ) :
      (J.sup (symbolSeminorm hU m)) ⟨jointFrequencySymbolSlice a τ, hslice τ hτ⟩ ≤ B := by
    apply Seminorm.finset_sup_apply_le hB
    intro j hj
    exact (hbsemi j τ hτ).trans (Finset.single_le_sum (fun k _ ↦ hb k) hj)
  refine ⟨hslice, (c : ℝ) * B, mul_nonneg c.coe_nonneg hB, ?_⟩
  intro τ hτ
  let p := zeroExtendedSymbol U χ (jointFrequencySymbolSlice a τ)
  have hp : IsSymbol Set.univ m p :=
    isSymbol_zeroExtendedSymbol U hU m χ hχ hcχ hsχ _ (hslice τ hτ)
  have hcp : HasCompactSupport p :=
    hasCompactSupport_zeroExtendedSymbol U χ _ hcχ
  let T := quantizeSobolev m s p hp hcp
  -- The original quantizer has the same Schwartz output in its Bessel coordinates.
  have hT (u : 𝓢(X, V)) : T (schwartzSobolevCoordinate s u) =
      schwartzSobolevCoordinate (s - m) (quantizeSchwartz m p hp hcp u) := by
    apply besselRealization_injective n q (s - m)
    ext1 φ
    rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
      SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [quantizeSchwartz_apply]
  have hnorm (u : 𝓢(X, V)) :
      ‖T (schwartzSobolevCoordinate s u)‖ ≤
        ((c : ℝ) * B) * ‖schwartzSobolevCoordinate s u‖ := by
    rw [hT]
    exact (hquant ⟨jointFrequencySymbolSlice a τ, hslice τ hτ⟩ u).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsup τ hτ) c.coe_nonneg) (norm_nonneg _))
  -- Density transfers the one common bound to the named bounded operator itself.
  change ‖T‖ ≤ (c : ℝ) * B
  apply T.opNorm_le_bound (mul_nonneg c.coe_nonneg hB)
  intro z
  exact (denseRange_schwartzSobolevCoordinate n r s).induction_on z
    (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) hnorm

end AtiyahSinger
