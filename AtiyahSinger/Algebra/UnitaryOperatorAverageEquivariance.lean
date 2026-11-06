/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.UnitaryOperatorAverage
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Haar averaging as a projection onto intertwiners

Public module ID: M0074.

Vectorwise Haar averaging gives an intertwiner for the specified isometric
actions and fixes every original intertwiner. Together with the operator-norm
contraction, this preserves small perturbations of an equivariant operator.
No continuity in operator norm is assumed for either group action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory

variable {G E F : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ν : Measure G) [IsProbabilityMeasure ν]
  (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (τ : G →* (F ≃ₗᵢ[ℂ] F))
  (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
  (hτ : Continuous (fun p : G × F ↦ τ p.1 p.2))

/-- Strong Haar averaging intertwines the same two original actions. -/
theorem unitaryOperatorAverage_intertwines [Measure.IsMulLeftInvariant ν]
    (T : E →L[ℂ] F) (a : G) (u : E) :
    unitaryOperatorAverage ν ρ τ hρ hτ T (ρ a u) =
      τ a (unitaryOperatorAverage ν ρ τ hρ hτ T u) := by
  -- Translate the original integral by a; the inverse action cancels that translation.
  rw [unitaryOperatorAverage_apply, unitaryOperatorAverage_apply]
  calc
    (∫ g, τ g (T (ρ g⁻¹ (ρ a u))) ∂ν) =
        ∫ g, τ (a * g) (T (ρ (a * g)⁻¹ (ρ a u))) ∂ν :=
      (integral_mul_left_eq_self (fun g ↦ τ g (T (ρ g⁻¹ (ρ a u)))) a).symm
    _ = ∫ g, τ a (τ g (T (ρ g⁻¹ u))) ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with g
      have hcancel : ρ (a * g)⁻¹ (ρ a u) = ρ g⁻¹ u := by
        change ((ρ (a * g)⁻¹) * (ρ a)) u = _
        rw [← map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      rw [hcancel, map_mul]
      rfl
    _ = τ a (∫ g, τ g (T (ρ g⁻¹ u)) ∂ν) :=
      (τ a).toLinearIsometry.integral_comp_comm _

/-- Averaging fixes an operator already intertwining the specified actions. -/
theorem unitaryOperatorAverage_eq_self
    (T : E →L[ℂ] F) (hT : ∀ (g : G) (u : E), T (ρ g u) = τ g (T u)) :
    unitaryOperatorAverage ν ρ τ hρ hτ T = T := by
  -- Every conjugated value equals the original value, before integration.
  apply ContinuousLinearMap.ext
  intro u
  rw [unitaryOperatorAverage_apply]
  have hconst (g : G) : τ g (T (ρ g⁻¹ u)) = T u := by
    rw [hT]
    change ((τ g) * (τ g⁻¹)) (T u) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  simp only [hconst]
  simp

end AtiyahSinger
