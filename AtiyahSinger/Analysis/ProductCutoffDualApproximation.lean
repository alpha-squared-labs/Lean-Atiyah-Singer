/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductSymbolCutoff

import all AtiyahSinger.Analysis.ProductSymbolCutoff
import all AtiyahSinger.Analysis.SymbolFourier

/-!
# The product cutoff error from H⁰ to H⁻¹

Public module ID: M0875.

The original full cutoff error has a small norm also when the single Sobolev
weight is placed on its output. Peetre's inequality moves that weight through
the spatial Fourier kernel, costing one additional power of spatial decay.
Every cutoff, frequency normalization and Bessel realization is unchanged.

This supplies the local estimate required for norm approximation of the actual
formal adjoint. The global metric duality and coordinate assembly are separate
obligations; the H¹-to-H⁰ estimate alone would not imply this direction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter FourierTransform MeasureTheory
open scoped ContDiff SchwartzMap Topology

variable {n m r q : ℕ}

set_option maxHeartbeats 800000 in
-- Retain uniform Fourier decay before choosing the cutoff parameter and its majorant.
/-- The same cutoff error admits a uniform H⁰-to-H⁻¹ Fourier realization. -/
theorem exists_productCutoffErrorOperator_zero_neg_one_bound (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε δ : ℝ, 0 ≤ δ →
      (∀ ξ : EuclideanSpace ℝ (Fin (n + m)),
        (1 - productFrequencyCutoff ε ‖(EuclideanSpace.finAddEquivProd ξ).1‖
          ‖(EuclideanSpace.finAddEquivProd ξ).2‖) *
            (1 + ‖(EuclideanSpace.finAddEquivProd ξ).1‖) ≤ δ * (1 + ‖ξ‖)) →
      ∃ T : Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin q)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
        ‖T‖ ≤ C * δ ∧
        ∀ u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)),
          ∀ φ : 𝓢(EuclideanSpace ℝ (Fin (n + m)), ℂ),
            besselRealization (n + m) q (-1) (T (schwartzSobolevCoordinate 0 u)) φ =
              ∫ x, φ x • quantize (productCutoffErrorSymbol a χ ε) u x := by
  let X := EuclideanSpace ℝ (Fin (n + m))
  let split : X ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let b (ε : ℝ) (ξ : X) :=
    1 - productFrequencyCutoff ε ‖(split ξ).1‖ ‖(split ξ).2‖
  let A : X → ℝ × X → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
    fun x p ↦ productCutoffErrorSymbol a χ p.1 x p.2
  let w : ℝ × X → ℝ := fun p ↦ b p.1 p.2 * (1 + ‖(split p.2).1‖)
  have hw0 (p : ℝ × X) : 0 ≤ w p :=
    mul_nonneg (productCutoffError_scalar_bound _ _ _ (norm_nonneg _) (norm_nonneg _)).1
      (by positivity)
  obtain ⟨K, hK, hsupp, hmeas, hsmooth, hder⟩ :=
    productCutoffError_spatial_data a ha haK χ hχ hχK
  have hderA (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun y ↦ A y p) x‖ ≤ C * w p := by
    obtain ⟨C, hC, hb⟩ := hder i
    exact ⟨C, hC, fun p x hx ↦ hb p.1 p.2 x hx⟩
  have hFourier (N : ℕ) := spatial_fourier_decay_of_spatial_bounds A
    (fun p ↦ hsmooth p.1 p.2) K hK (fun x hx p ↦ hsupp p.1 x hx p.2) w hw0 hderA N
  obtain ⟨C₀, hC₀, hF₀⟩ := hFourier 0
  obtain ⟨C₁, hC₁, hF₁⟩ := hFourier (n + m + 2)
  obtain ⟨C₂, hC₂, hV⟩ := hder 0
  let D₀ : ℝ := max ((2 * (2 * Real.pi) ^ 2) ^ ((1 : ℝ) / 2)) 1
  let D : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 2) * D₀
  have hD₀ : 0 ≤ D₀ := zero_le_one.trans (le_max_right _ _)
  have hD : 0 ≤ D := mul_nonneg (by positivity) hD₀
  let d : X → ℝ := fun ζ ↦ (1 + ‖ζ‖) ^ (-((n + m : ℕ) : ℝ) - 1)
  have hd : Continuous d := by
    apply Continuous.rpow_const (continuous_const.add continuous_norm)
    intro ζ
    left
    exact ne_of_gt (show 0 < 1 + ‖ζ‖ from by positivity)
  have hd0 (ζ : X) : 0 ≤ d ζ := by dsimp [d]; positivity
  have hdi : Integrable d := by
    have hdim : (Module.finrank ℝ X : ℝ) < ((n + m : ℕ) : ℝ) + 1 := by simp [X]
    simpa only [d, neg_add, sub_eq_add_neg] using
      (integrable_one_add_norm (E := X) (μ := volume) hdim)
  refine ⟨C₁ * D * (∫ ζ, d ζ), by positivity, ?_⟩
  intro ε δ hδ hfreq
  have hval : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖productCutoffErrorSymbol a χ ε x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (1 : ℝ) := by
    refine ⟨C₂ * δ, mul_nonneg hC₂ hδ, ?_⟩
    intro x ξ
    rw [Real.rpow_one]
    by_cases hx : x ∈ K
    · have h := hV ε ξ x hx
      simp only [norm_iteratedFDeriv_zero] at h
      exact h.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hfreq ξ) hC₂)
    · rw [hsupp ε x hx ξ, norm_zero]
      positivity
  have hfourier : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ ζ,
      ‖𝓕 (fun x ↦ productCutoffErrorSymbol a χ ε x ξ) ζ‖ ≤
        C * (1 + ‖ξ‖) ^ (1 : ℝ) := by
    refine ⟨C₀ * δ, mul_nonneg hC₀ hδ, ?_⟩
    intro ξ ζ
    have h := hF₀ (ε, ξ) ζ
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h
    rw [Real.rpow_one]
    exact h.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hfreq ξ) hC₀)
  -- Moving the single Bessel weight to the output costs one spatial Fourier decay power.
  have hweight (ξ η : X) :
      (1 + ‖ξ‖ ^ 2) ^ (-((1 : ℝ) / 2)) * (1 + ‖(2 * Real.pi) • η‖) ≤
        D * (1 + ‖ξ - η‖) := by
    have hshift := bessel_weight_shift (-((1 : ℝ) / 2)) η (ξ - η)
    have hadd : η + (ξ - η) = ξ := by abel
    rw [hadd] at hshift
    norm_num at hshift
    have hspatial := spatial_weight_le_bessel (1 : ℝ) η
    rw [Real.rpow_one] at hspatial
    have hcancel : (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
        (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num
    have hdiff : (1 + ‖ξ - η‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ 1 + ‖ξ - η‖ := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [norm_nonneg (ξ - η)]
    calc
      _ ≤ ((2 : ℝ) ^ ((1 : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
          (1 + ‖ξ - η‖ ^ 2) ^ ((1 : ℝ) / 2)) *
          (D₀ * (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2)) := by
        gcongr
      _ = D * (1 + ‖ξ - η‖ ^ 2) ^ ((1 : ℝ) / 2) := by
        dsimp only [D]
        calc
          _ = ((2 : ℝ) ^ ((1 : ℝ) / 2) * D₀ *
              (1 + ‖ξ - η‖ ^ 2) ^ ((1 : ℝ) / 2)) *
              ((1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
              (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2)) := by ring
          _ = _ := by rw [hcancel, mul_one]
      _ ≤ D * (1 + ‖ξ - η‖) := mul_le_mul_of_nonneg_left hdiff hD
  let dδ : X → ℝ := fun ζ ↦ (C₁ * D * δ) * d ζ
  have hdδ : Continuous dδ := hd.const_mul _
  have hdδ0 (ζ : X) : 0 ≤ dδ ζ := mul_nonneg (by positivity) (hd0 ζ)
  have hdiδ : Integrable dδ := hdi.const_mul _
  have hdeδ (ζ : X) : dδ (-ζ) = dδ ζ := by simp only [dδ, d, norm_neg]
  let d₁ : X → ℝ := fun ζ ↦ (1 + ‖ζ‖) ^ (-((n + m : ℕ) : ℝ) - 2)
  have hdecay (ζ : X) : (1 + ‖ζ‖) * d₁ ζ = d ζ := by
    dsimp only [d₁, d]
    calc
      _ = (1 + ‖ζ‖) ^ (1 : ℝ) * (1 + ‖ζ‖) ^ (-((n + m : ℕ) : ℝ) - 2) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
  have hbound (ξ η : X) :
      ‖((1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - 1) / 2) * (1 + ‖η‖ ^ 2) ^ (-((0 : ℝ) / 2))) •
        𝓕 (fun x ↦ productCutoffErrorSymbol a χ ε x ((2 * Real.pi) • η)) (ξ - η)‖ ≤
          dδ (ξ - η) := by
    have hF := hF₁ (ε, (2 * Real.pi) • η) (ξ - η)
    have hexp : -((n + m + 2 : ℕ) : ℝ) = -((n + m : ℕ) : ℝ) - 2 := by
      push_cast
      ring
    rw [hexp] at hF
    norm_num only [zero_sub, zero_div, neg_zero, Real.rpow_zero, mul_one]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
          (C₁ * w (ε, (2 * Real.pi) • η) * d₁ (ξ - η)) := by gcongr
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
          (C₁ * (δ * (1 + ‖(2 * Real.pi) • η‖)) * d₁ (ξ - η)) := by
        gcongr
        exact hfreq _
      _ = (C₁ * δ * d₁ (ξ - η)) *
          ((1 + ‖ξ‖ ^ 2) ^ (-((1 : ℝ) / 2)) * (1 + ‖(2 * Real.pi) • η‖)) := by ring
      _ ≤ (C₁ * δ * d₁ (ξ - η)) * (D * (1 + ‖ξ - η‖)) :=
        mul_le_mul_of_nonneg_left (hweight ξ η) (by dsimp only [d₁]; positivity)
      _ = (C₁ * D * δ) * ((1 + ‖ξ - η‖) * d₁ (ξ - η)) := by ring
      _ = dδ (ξ - η) := by rw [hdecay]
  obtain ⟨T, hTnorm, hT⟩ := exists_quantize_sobolev_extension_of_spatial_bounds
    1 0 (productCutoffErrorSymbol a χ ε) (hmeas ε) (hsmooth ε) hval hfourier
    K hK (hsupp ε) dδ hdδ hdδ0 hdiδ hdeδ (by simpa only [neg_div] using hbound)
  refine ⟨T, ?_, ?_⟩
  · apply hTnorm.trans_eq
    rw [integral_const_mul]
    ring
  · simpa only [zero_sub] using hT

end AtiyahSinger
