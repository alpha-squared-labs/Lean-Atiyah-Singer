/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DifferentialForms
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration of actual Euclidean top forms

Public module ID: M1219.

Top forms are evaluated on the standard ordered Euclidean basis and integrated
in those same coordinates. Integration of a compactly supported derivative
vanishes by Haar integration by parts with constant scalar factor one. This
supplies the scalar obstruction in the compact-support de Rham calculation.

Source: the Euclidean Stokes formula for compact support, Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped BigOperators ContDiff

/-- Integration of an actual complex-valued top form in the standard ordered coordinates. -/
def euclideanTopFormIntegral (n : ℕ)
    (α : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℂ) : ℂ :=
  ∫ x : Fin n → ℝ, α ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    (EuclideanSpace.basisFun (Fin n) ℝ)

set_option maxHeartbeats 1500000 in
-- Haar integration by parts retains the original coordinate direction and volume.
set_option backward.isDefEq.respectTransparency false in
/-- The integral of a coordinate derivative of a smooth compactly supported function is zero. -/
theorem integral_fderiv_coordinate_eq_zero (n : ℕ) (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, fderiv ℝ f x (Pi.single i 1)) = 0 := by
  -- Compact support supplies the product-integrability hypotheses of Haar integration by parts.
  have hcont : Continuous (fun x ↦ fderiv ℝ f x (Pi.single i 1)) :=
    (hf.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
  have hderiv : Integrable (fun x ↦ fderiv ℝ f x (Pi.single i 1)) :=
    hcont.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (Pi.single i 1))
  have hint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  -- Use the constant real scalar one with the original direction and original product volume.
  have hparts := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := fun _ : Fin (n + 1) → ℝ ↦ (1 : ℝ))
    (g := f) (v := Pi.single i 1)
    (by simp)
    (by simpa only [one_smul] using hderiv)
    (by simpa only [one_smul] using hint)
    (fun x _ ↦ differentiableAt_const (1 : ℝ))
    (fun x _ ↦ hf.differentiable (by simp) x)
  simpa only [one_smul, fderiv_const_apply, zero_apply,
    zero_smul, integral_zero, neg_zero] using hparts

set_option maxHeartbeats 2000000 in
-- Continuous evaluations identify the derivative summands with the same scalar functions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exact top form with a smooth compactly supported primitive has integral zero. -/
theorem euclideanTopFormIntegral_extDeriv (n : ℕ)
    (η : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℂ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    euclideanTopFormIntegral (n + 1) (extDeriv η) = 0 := by
  classical
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let P := Fin (n + 1) → ℝ
  let E : P ≃L[ℝ] V := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let ev (i : Fin (n + 1)) : (V [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousAlternatingMap.apply ℝ V ℂ (i.removeNth b)
  let f (i : Fin (n + 1)) (x : P) : ℂ := ev i (η (E x))
  have hf (i : Fin (n + 1)) : ContDiff ℝ ∞ (f i) :=
    (ev i).contDiff.comp (hη.comp E.contDiff)
  have hfc (i : Fin (n + 1)) : HasCompactSupport (f i) :=
    (hc.comp_homeomorph E.toHomeomorph).comp_left (ev i).map_zero
  have hd (i : Fin (n + 1)) (x : P) :
      fderiv ℝ (f i) x (Pi.single i 1) = (fderiv ℝ η (E x) (b i)) (i.removeNth b) := by
    have h := (ev i).hasFDerivAt.comp x
      ((hη.differentiable (by simp) (E x)).hasFDerivAt.comp x E.hasFDerivAt)
    have hb : E (Pi.single i 1) = b i := by
      change WithLp.toLp 2 (Pi.single i (1 : ℝ)) =
        EuclideanSpace.basisFun (Fin (n + 1)) ℝ i
      rw [EuclideanSpace.basisFun_apply, PiLp.toLp_single]
    change fderiv ℝ (fun x ↦ ev i (η (E x))) x (Pi.single i 1) = _
    have hh : fderiv ℝ (fun x ↦ ev i (η (E x))) x =
        (ev i).comp ((fderiv ℝ η (E x)).comp E.toContinuousLinearMap) := h.fderiv
    rw [hh]
    change ev i (fderiv ℝ η (E x) (E (Pi.single i 1))) = _
    rw [hb]
    rfl
  have hint (i : Fin (n + 1)) :
      Integrable (fun x ↦ (-1 : ℤ) ^ i.val • fderiv ℝ (f i) x (Pi.single i 1)) := by
    have hcont : Continuous (fun x ↦ fderiv ℝ (f i) x (Pi.single i 1)) :=
      ((hf i).fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
    have hi : Integrable (fun x ↦ fderiv ℝ (f i) x (Pi.single i 1)) :=
      hcont.integrable_of_hasCompactSupport ((hfc i).fderiv_apply ℝ (Pi.single i 1))
    exact hi.smul _
  -- The original unnormalized exterior derivative is precisely the sum of these derivatives.
  have hpoint (x : P) : (extDeriv η (E x)) b =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • fderiv ℝ (f i) x (Pi.single i 1) := by
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd]
  change (∫ x : P, (extDeriv η (E x)) b) = 0
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ ↦ hint i)]
  apply Finset.sum_eq_zero
  intro i _
  simp_rw [← Int.cast_smul_eq_zsmul ℝ]
  rw [integral_smul, integral_fderiv_coordinate_eq_zero n i (f i) (hf i) (hfc i), smul_zero]

end AtiyahSinger
