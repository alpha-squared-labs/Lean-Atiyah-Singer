/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# A normalized Lebesgue integral for positive contraction powers

Public module ID: M0818.

The scalar normalization and the operator integral use ordinary Lebesgue measure.
This retains the density hidden by the existing existential-measure CFC theorem,
so subsequent parameter substitutions can use the usual Jacobians.

The proof lifts mathlib's scalar `Real.rpow_eq_const_mul_integral` through the
continuous functional calculus. The scalar kernel at one dominates the whole
nonnegative spectrum of the contraction. The final kernel is the original
bounded resolvent, and its Lebesgue integrability is proved separately from the
normalized-measure identity. No spectral gap or inverse of B is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set

/-- Fractional powers of a positive contraction are normalized Lebesgue resolvent integrals. -/
theorem cfc_rpow_eq_normalized_resolvent_integral
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hB : 0 ≤ B) (hBnorm : ‖B‖ ≤ 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    0 < C ∧
      IntegrableOn (fun t : ℝ ↦ t ^ (p - 1) •
        (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))) (Ioi 0) ∧
      CFC.rpow B p = C⁻¹ • (∫ t in Ioi (0 : ℝ), t ^ (p - 1) •
        (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))) := by
  let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨hp, hp1⟩
  have hC : 0 < C := Real.integral_rpowIntegrand₀₁_one_pos hpI
  refine ⟨hC, ?_⟩
  rcases subsingleton_or_nontrivial H with hH | hH
  · let _ : Subsingleton H := hH
    constructor
    · have hzero : (fun t : ℝ ↦ t ^ (p - 1) •
          (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))) = fun _ ↦ 0 :=
        Subsingleton.elim _ _
      rw [hzero]
      simp [IntegrableOn]
    · exact Subsingleton.elim _ _
  let _ : Nontrivial H := hH
  let c : NNReal := ⟨C⁻¹, inv_nonneg.mpr hC.le⟩
  let ν : Measure ℝ := c • volume
  let f : ℝ → ℝ → ℝ := fun t x ↦ Real.rpowIntegrand₀₁ p t x
  let bound : ℝ → ℝ := fun t ↦ ‖f t 1‖
  have hself : IsSelfAdjoint B := .of_nonneg hB
  -- The normalized measure has an explicit constant density, independent of the operator.
  have hscalar (x : ℝ) (hx : 0 ≤ x) :
      x ^ p = ∫ t in Ioi (0 : ℝ), f t x ∂ν := by
    dsimp only [ν]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    change x ^ p = C⁻¹ * ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t x
    exact Real.rpow_eq_const_mul_integral hpI hx
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : ℝ) ×ˢ spectrum ℝ B) :=
    Real.continuousOn_rpowIntegrand₀₁_uncurry hpI (spectrum ℝ B)
      (fun x hx ↦ spectrum_nonneg_of_nonneg hB hx)
  have hbound (μ : Measure ℝ) :
      ∀ᵐ t ∂μ.restrict (Ioi 0), ∀ x ∈ spectrum ℝ B, ‖f t x‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hB hx
    have hx1 : x ≤ 1 := (le_abs_self x).trans
      ((spectrum.norm_le_norm_of_mem hx).trans hBnorm)
    dsimp only [f, bound]
    rw [Real.norm_of_nonneg (Real.rpowIntegrand₀₁_nonneg hp ht.le hx0),
      Real.norm_of_nonneg (Real.rpowIntegrand₀₁_nonneg hp ht.le zero_le_one)]
    exact Real.rpowIntegrand₀₁_monotoneOn hpI ht.le hx0 zero_le_one hx1
  have hboundVolume : Integrable bound (volume.restrict (Ioi 0)) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi hpI zero_le_one).norm
  have hboundNormalized : HasFiniteIntegral bound (ν.restrict (Ioi 0)) := by
    dsimp only [ν]
    rw [Measure.restrict_smul]
    apply Integrable.hasFiniteIntegral
    exact Integrable.smul_measure_nnreal hboundVolume
  -- Prove unnormalized integrability, then lift the scalar equality using the normalized measure.
  have hintegrable : IntegrableOn (fun t ↦ cfc (f t) B) (Ioi (0 : ℝ)) :=
    integrableOn_cfc measurableSet_Ioi f bound B hf (hbound volume)
      hboundVolume.hasFiniteIntegral hself
  have hnormalized : CFC.rpow B p = ∫ t in Ioi (0 : ℝ), cfc (f t) B ∂ν := by
    calc
      CFC.rpow B p = cfc (fun x : ℝ ↦ x ^ p) B := CFC.rpow_eq_cfc_real hB
      _ = cfc (fun x : ℝ ↦ ∫ t in Ioi (0 : ℝ), f t x ∂ν) B := by
        apply cfc_congr
        intro x hx
        exact hscalar x (spectrum_nonneg_of_nonneg hB hx)
      _ = ∫ t in Ioi (0 : ℝ), cfc (f t) B ∂ν :=
        cfc_setIntegral measurableSet_Ioi f bound B hf (hbound ν) hboundNormalized hself
  have hvolume : CFC.rpow B p = C⁻¹ • (∫ t in Ioi (0 : ℝ), cfc (f t) B) := by
    have hmeasure : (∫ t in Ioi (0 : ℝ), cfc (f t) B ∂ν) =
        c • (∫ t in Ioi (0 : ℝ), cfc (f t) B) := by
      dsimp only [ν]
      rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    have hcoefficient (T : H →L[ℂ] H) : c • T = C⁻¹ • T := by
      ext v
      change (c : ℝ) • T v = C⁻¹ • T v
      rfl
    exact hnormalized.trans (hmeasure.trans (hcoefficient _))
  -- The scalar quotient is exactly the original bounded resolvent on this nonnegative spectrum.
  have hkernel (t : ℝ) (ht : 0 < t) :
      cfc (f t) B = t ^ (p - 1) •
        (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B)) := by
    have hnonzero (x : ℝ) (hx : x ∈ spectrum ℝ B) : t + x ≠ 0 :=
      (add_pos_of_pos_of_nonneg ht (spectrum_nonneg_of_nonneg hB hx)).ne'
    calc
      cfc (f t) B = cfc (fun x : ℝ ↦ t ^ (p - 1) * (x / (t + x))) B := by
        apply cfc_congr
        intro x hx
        dsimp only [f]
        rw [Real.rpowIntegrand₀₁_eq_pow_div hpI ht.le
          (spectrum_nonneg_of_nonneg hB hx)]
        exact mul_div_assoc _ _ _
      _ = t ^ (p - 1) • (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B)) := by
        rw [cfc_const_mul (t ^ (p - 1)) (fun x : ℝ ↦ x / (t + x)) B
          (continuousOn_id.div (continuousOn_const.add continuousOn_id) hnonzero),
          cfc_map_div (fun x : ℝ ↦ x) (fun x : ℝ ↦ t + x) B hnonzero
            continuousOn_id (continuousOn_const.add continuousOn_id) hself,
          cfc_id' ℝ B hself,
          cfc_const_add t (fun x : ℝ ↦ x) B continuousOn_id hself,
          cfc_id' ℝ B hself, Algebra.algebraMap_eq_smul_one]
  have hsame : (fun t : ℝ ↦ cfc (f t) B) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ ↦ t ^ (p - 1) • (B * Ring.inverse (t • (1 : H →L[ℂ] H) + B))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hkernel t ht
  exact ⟨Integrable.congr hintegrable hsame,
    hvolume.trans (congrArg (fun T : H →L[ℂ] H ↦ C⁻¹ • T) (integral_congr_ae hsame))⟩

end AtiyahSinger
