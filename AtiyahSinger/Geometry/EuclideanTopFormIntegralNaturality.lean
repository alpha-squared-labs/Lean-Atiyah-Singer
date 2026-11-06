/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanFormIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Linear change of variables for top-form integration

Public module ID: M1224.

The actual complex-valued real alternating tensor contributes the signed determinant.
Lebesgue change of variables contributes its absolute value. For a linear equivalence
of determinant of absolute value one, the original coordinate integral therefore
transforms by the determinant itself.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory

/-- The original top-form integral transforms by the determinant under a volume-preserving
linear change of coordinates. -/
theorem euclideanTopFormIntegral_pullback (n : ℕ)
    (B : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB : |LinearMap.det B.toLinearMap| = 1)
    (α : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℂ) :
    euclideanTopFormIntegral n (fun x ↦
      (α (B x)).compContinuousLinearMap B.toContinuousLinearMap) =
      ((LinearMap.det B.toLinearMap : ℝ) : ℂ) * euclideanTopFormIntegral n α := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let P := Fin n → ℝ
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E : V ≃L[ℝ] P := EuclideanSpace.equiv (Fin n) ℝ
  -- Both real coordinates of the complex tensor satisfy the same determinant identity.
  have hreal (f : V [⋀^Fin n]→ₗ[ℝ] ℝ) :
      f (fun i ↦ B (b i)) = LinearMap.det B.toLinearMap * f b := by
    rw [f.eq_smul_basis_det b]
    change f b * b.det (B.toLinearMap ∘ b) = _
    rw [b.det_comp, b.det_self, mul_one]
    simp only [smul_apply, Module.Basis.det_self, smul_eq_mul, mul_one]
    exact mul_comm _ _
  have htensor (a : V [⋀^Fin n]→L[ℝ] ℂ) :
      a (fun i ↦ B (b i)) = ((LinearMap.det B.toLinearMap : ℝ) : ℂ) * a b := by
    apply Complex.ext
    · have h := hreal ((Complex.reCLM.compContinuousAlternatingMap a).toAlternatingMap)
      change (a (fun i ↦ B (b i))).re = LinearMap.det B.toLinearMap * (a b).re at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using h
    · have h := hreal ((Complex.imCLM.compContinuousAlternatingMap a).toAlternatingMap)
      change (a (fun i ↦ B (b i))).im = LinearMap.det B.toLinearMap * (a b).im at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero] using h
  -- The actual coordinate conjugate preserves the product Lebesgue measure.
  let T : P ≃L[ℝ] P := E.symm.trans (B.trans E)
  have hdet : LinearMap.det T.toLinearMap = LinearMap.det B.toLinearMap :=
    LinearMap.det_conj B.toLinearMap E.toLinearEquiv
  have hdet0 : LinearMap.det T.toLinearMap ≠ 0 := by
    rw [hdet]
    intro h
    simp [h] at hB
  have hmeasure : MeasurePreserving T := by
    refine ⟨T.continuous.measurable, ?_⟩
    change Measure.map T.toLinearMap (volume : Measure P) = volume
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure P) hdet0
    simpa only [hdet, abs_inv, hB, inv_one, ENNReal.ofReal_one, one_smul] using h
  change (∫ x : P, α (B (E.symm x)) (fun i ↦ B (b i))) =
    ((LinearMap.det B.toLinearMap : ℝ) : ℂ) * ∫ x : P, α (E.symm x) b
  simp_rw [htensor]
  rw [integral_const_mul]
  congr 1
  exact hmeasure.integral_comp T.toHomeomorph.measurableEmbedding
    (fun x : P ↦ α (E.symm x) b)

end AtiyahSinger
