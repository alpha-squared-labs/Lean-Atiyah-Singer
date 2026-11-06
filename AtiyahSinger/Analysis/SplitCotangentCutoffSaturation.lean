/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Analysis.FiniteAtlasProductCutoff

/-!
# Complementary cutoff saturation for actual mixed cotangent blocks

Public module ID: M1014.

Given uniform upper and inverse bounds for the specified cotangent blocks,
refine any prescribed horizontal cone. One sufficiently small positive cutoff
parameter makes every horizontal SG cutoff equal one inside that cone and
every vertical SG cutoff equal one outside it, throughout the interpolation
of the original mixed block. This is pointwise saturation, so subsequent
finite partition sums may have signed weights.

The index set may include the active chart and spatial point. The theorem
does not supply the actual compact-chart bounds, nor identify bundle maps or
their K classes. It retains the given base, mixed and vertical blocks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

variable {Z X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- One parameter saturates complementary cutoffs for the same mixed cotangent homotopy. -/
theorem exists_productCutoffHomotopyWeight_eq_one_in_split_cones
    (A : Z → X →L[ℝ] X) (B : Z → Y →L[ℝ] X) (V : Z → Y →L[ℝ] Y)
    (D δ₀ : ℝ) (hD : 1 ≤ D) (hδ₀ : 0 < δ₀)
    (hA : ∀ z, ‖A z‖ ≤ D) (hAi : ∀ z ξ, ‖ξ‖ ≤ D * ‖A z ξ‖)
    (hB : ∀ z, ‖B z‖ ≤ D) (hV : ∀ z, ‖V z‖ ≤ D)
    (hVi : ∀ z η, ‖η‖ ≤ D * ‖V z η‖) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (t : unitInterval) z ξ η,
        (‖η‖ ≤ δ * ‖ξ‖ → productCutoffHomotopyWeight ε t
          ‖A z ξ + (t : ℝ) • B z η‖ ‖V z η‖ = 1) ∧
        (δ * ‖ξ‖ ≤ ‖η‖ → productCutoffHomotopyWeight ε t
          ‖V z η‖ ‖A z ξ + (t : ℝ) • B z η‖ = 1) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  let δ := min δ₀ (2 * D ^ 2)⁻¹
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδsmall : 2 * D ^ 2 * δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (min_le_right δ₀ (2 * D ^ 2)⁻¹)
      (show 0 ≤ 2 * D ^ 2 by positivity)
    simpa only [δ, mul_inv_cancel₀ (show 2 * D ^ 2 ≠ 0 by positivity)] using h
  let ε₀ := min 1 (δ / (D ^ 2 * (δ + 1)))
  have hden : 0 < D ^ 2 * (δ + 1) := by positivity
  have hε₀ : 0 < ε₀ := lt_min zero_lt_one (div_pos hδ hden)
  refine ⟨δ, ε₀, hδ, min_le_left _ _, hε₀, min_le_left _ _, ?_⟩
  intro ε hε hεbound t z ξ η
  have hεone : ε ≤ 1 := hεbound.trans (min_le_left _ _)
  have hεsmall : ε * (D ^ 2 * (δ + 1)) ≤ δ :=
    (le_div_iff₀ hden).mp (hεbound.trans (min_le_right _ _))
  have hbase : ‖A z ξ‖ ≤ D * ‖ξ‖ :=
    ((A z).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right (hA z) (norm_nonneg ξ))
  have hvertical : ‖V z η‖ ≤ D * ‖η‖ :=
    ((V z).le_opNorm η).trans (mul_le_mul_of_nonneg_right (hV z) (norm_nonneg η))
  have hshift : ‖(t : ℝ) • B z η‖ ≤ D * ‖η‖ := by
    calc
      ‖(t : ℝ) • B z η‖ = (t : ℝ) * ‖B z η‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      _ ≤ 1 * (‖B z‖ * ‖η‖) :=
        mul_le_mul t.property.2 ((B z).le_opNorm η) (norm_nonneg _) zero_le_one
      _ ≤ D * ‖η‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg η)
  have hupper : ‖A z ξ + (t : ℝ) • B z η‖ ≤ D * ‖ξ‖ + D * ‖η‖ :=
    (norm_add_le _ _).trans (add_le_add hbase hshift)
  have hlower : ‖ξ‖ ≤ D * (‖A z ξ + (t : ℝ) • B z η‖ + D * ‖η‖) := by
    have htri : ‖A z ξ‖ ≤ ‖A z ξ + (t : ℝ) • B z η‖ + ‖(t : ℝ) • B z η‖ := by
      simpa only [add_sub_cancel_right] using
        norm_sub_le (A z ξ + (t : ℝ) • B z η) ((t : ℝ) • B z η)
    exact (hAi z ξ).trans (mul_le_mul_of_nonneg_left
      (htri.trans (add_le_add le_rfl hshift)) hDpos.le)
  constructor
  · intro hcone
    -- The mixed term consumes at most half the base lower bound in the refined cone.
    have hsmall : 2 * D ^ 2 * ‖η‖ ≤ ‖ξ‖ := by
      calc
        2 * D ^ 2 * ‖η‖ ≤ 2 * D ^ 2 * (δ * ‖ξ‖) := by gcongr
        _ = (2 * D ^ 2 * δ) * ‖ξ‖ := by ring
        _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right hδsmall (norm_nonneg ξ)
        _ = ‖ξ‖ := one_mul _
    have hdom : ε * ‖V z η‖ ≤ ‖A z ξ + (t : ℝ) • B z η‖ := by
      have he := mul_le_mul_of_nonneg_right hεone (norm_nonneg (V z η))
      nlinarith
    have hc := productFrequencyCutoff_eq_one_of_mul_le ε
      ‖A z ξ + (t : ℝ) • B z η‖ ‖V z η‖ hε (norm_nonneg _) (norm_nonneg _) hdom
    simp only [productCutoffHomotopyWeight, hc]
    ring
  · intro hcone
    -- Outside the same cone the small common parameter saturates the swapped cutoff.
    have hscaled : δ * (ε * ‖A z ξ + (t : ℝ) • B z η‖) ≤ δ * ‖V z η‖ := by
      calc
        δ * (ε * ‖A z ξ + (t : ℝ) • B z η‖) ≤
            δ * (ε * (D * ‖ξ‖ + D * ‖η‖)) := by gcongr
        _ = (ε * D) * (δ * ‖ξ‖ + δ * ‖η‖) := by ring
        _ ≤ (ε * D) * (‖η‖ + δ * ‖η‖) := by gcongr
        _ = (ε * D * (δ + 1)) * ‖η‖ := by ring
        _ ≤ (ε * D * (δ + 1)) * (D * ‖V z η‖) := by
          apply mul_le_mul_of_nonneg_left (hVi z η)
          positivity
        _ = (ε * (D ^ 2 * (δ + 1))) * ‖V z η‖ := by ring
        _ ≤ δ * ‖V z η‖ := mul_le_mul_of_nonneg_right hεsmall (norm_nonneg _)
    have hdom : ε * ‖A z ξ + (t : ℝ) • B z η‖ ≤ ‖V z η‖ := by
      nlinarith
    have hc := productFrequencyCutoff_eq_one_of_mul_le ε
      ‖V z η‖ ‖A z ξ + (t : ℝ) • B z η‖ hε (norm_nonneg _) (norm_nonneg _) hdom
    simp only [productCutoffHomotopyWeight, hc]
    ring

end AtiyahSinger
