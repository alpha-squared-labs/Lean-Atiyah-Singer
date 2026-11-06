/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Strong averaging of operators between isometric representations

Public module ID: M0073.

For jointly continuous isometric representations, integrate each conjugated
operator on each vector in the original Banach output space. The common
isometry bound gives a bounded operator and a linear contraction in the
operator norm. The group representation itself need not be continuous in
operator norm; no integral in the operator space is taken.
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

/-- Vectorwise averaging of conjugates is a continuous linear transformation of operators. -/
def unitaryOperatorAverage : (E →L[ℂ] F) →L[ℂ] (E →L[ℂ] F) := by
  have hint (T : E →L[ℂ] F) (u : E) :
      Integrable (fun g ↦ τ g (T (ρ g⁻¹ u))) ν := by
    have hi := hρ.comp (continuous_inv.prodMk (continuous_const (y := u)))
    exact (hτ.comp (continuous_id.prodMk (T.continuous.comp hi)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (T : E →L[ℂ] F) (u : E) :
      ‖∫ g, τ g (T (ρ g⁻¹ u)) ∂ν‖ ≤ ‖T‖ * ‖u‖ := by
    have h (g : G) : ‖τ g (T (ρ g⁻¹ u))‖ ≤ ‖T‖ * ‖u‖ := by
      rw [(τ g).norm_map]
      simpa only [(ρ g⁻¹).norm_map] using T.le_opNorm (ρ g⁻¹ u)
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall h)
  let A (T : E →L[ℂ] F) : E →L[ℂ] F :=
    LinearMap.mkContinuous
      { toFun := fun u ↦ ∫ g, τ g (T (ρ g⁻¹ u)) ∂ν
        map_add' := by
          intro u v
          simp only [map_add]
          exact integral_add (hint T u) (hint T v)
        map_smul' := by
          intro z u
          simp only [map_smul]
          exact integral_smul z _ }
      ‖T‖ (hbound T)
  have hA (T : E →L[ℂ] F) : ‖A T‖ ≤ ‖T‖ :=
    (A T).opNorm_le_bound (norm_nonneg T) (hbound T)
  let L : (E →L[ℂ] F) →ₗ[ℂ] (E →L[ℂ] F) := {
    toFun := A
    map_add' := by
      intro T S
      ext u
      change (∫ g, τ g ((T + S) (ρ g⁻¹ u)) ∂ν) = _
      simp only [add_apply, map_add]
      exact integral_add (hint T u) (hint S u)
    map_smul' := by
      intro z T
      ext u
      change (∫ g, τ g ((z • T) (ρ g⁻¹ u)) ∂ν) = _
      simp only [smul_apply, map_smul]
      exact integral_smul z _ }
  exact L.mkContinuous 1 (fun T ↦ by
    change ‖A T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using hA T)

omit [CompleteSpace F] in
/-- The average evaluates by integrating in the original output Banach space. -/
theorem unitaryOperatorAverage_apply (T : E →L[ℂ] F) (u : E) :
    unitaryOperatorAverage ν ρ τ hρ hτ T u = ∫ g, τ g (T (ρ g⁻¹ u)) ∂ν := rfl

omit [CompleteSpace F] in
/-- Averaging conjugates by isometries cannot increase an operator norm. -/
theorem norm_unitaryOperatorAverage_le (T : E →L[ℂ] F) :
    ‖unitaryOperatorAverage ν ρ τ hρ hτ T‖ ≤ ‖T‖ := by
  apply (unitaryOperatorAverage ν ρ τ hρ hτ T).opNorm_le_bound (norm_nonneg T)
  intro u
  rw [unitaryOperatorAverage_apply]
  have h (g : G) : ‖τ g (T (ρ g⁻¹ u))‖ ≤ ‖T‖ * ‖u‖ := by
    rw [(τ g).norm_map]
    simpa only [(ρ g⁻¹).norm_map] using T.le_opNorm (ρ g⁻¹ u)
  simpa using norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall h)

end AtiyahSinger
