/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianCoreTensorSymbol
public import Mathlib.Analysis.Convex.Integral

/-!
# Averaging a graded symbol with a fixed dominant factor

Public module ID: M0318.

A probability average of the actual native matrix preserves the coefficient
one of the dominant invertible factor. The other coefficient stays real, even
when no separate continuity or integrability of the auxiliary weights is given:
the integrable full matrix lies in a closed real affine line. Thus the averaged
matrix retains the original Hermitian invertibility argument, including signed
atlas weights and zero tensor summands.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped TensorProduct

private theorem exists_integral_eq_add_smul
    {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : Ω → V) (hf : Integrable f μ) (v w : V)
    (h : ∀ z, ∃ t : ℝ, f z = v + t • w) :
    ∃ t : ℝ, (∫ z, f z ∂μ) = v + t • w := by
  let S := Submodule.span ℝ ({w} : Set V)
  have hs : IsClosed (S : Set V) := S.closed_of_finiteDimensional
  have hmem : ∀ z, f z - v ∈ S := by
    intro z
    obtain ⟨t, ht⟩ := h z
    rw [ht, add_sub_cancel_left]
    exact Submodule.smul_mem S t (Submodule.subset_span (Set.mem_singleton w))
  have hint := S.convex.integral_mem hs (Filter.Eventually.of_forall hmem)
    (hf.sub (integrable_const v))
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hint
  rw [integral_sub hf (integrable_const v)] at ht
  simp only [integral_const, probReal_univ, one_smul] at ht
  refine ⟨t, ?_⟩
  rw [ht]
  abel

variable {Ω S T E₀ E₁ F₀ F₁ : Type*}
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup T] [NormedSpace ℂ T] [FiniteDimensional ℂ T]
  [AddCommGroup E₀] [Module ℂ E₀] [FiniteDimensional ℂ E₀]
  [AddCommGroup E₁] [Module ℂ E₁] [FiniteDimensional ℂ E₁]
  [AddCommGroup F₀] [Module ℂ F₀] [FiniteDimensional ℂ F₀]
  [AddCommGroup F₁] [Module ℂ F₁] [FiniteDimensional ℂ F₁]

omit [FiniteDimensional ℂ E₀] [FiniteDimensional ℂ E₁]
  [FiniteDimensional ℂ F₀] [FiniteDimensional ℂ F₁] in

/-- The actual averaged matrix retains a saturated dominant coefficient. -/
theorem exists_integral_reciprocalTensorSymbol_weights
    (p : E₀ →ₗ[ℂ] E₁) (pi : E₁ →ₗ[ℂ] E₀)
    (q : F₀ →ₗ[ℂ] F₁) (qi : F₁ →ₗ[ℂ] F₀)
    (e : ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) ≃ₗ[ℂ] S)
    (f : ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) ≃ₗ[ℂ] T)
    (A : Ω → S →L[ℂ] T) (hA : Integrable A μ) (α β : Ω → ℝ)
    (hformula : ∀ z v, A z (e v) = f (reciprocalTensorSymbol
      ((α z : ℂ) • p) ((α z : ℂ) • pi) ((β z : ℂ) • q) ((β z : ℂ) • qi) v))
    (hdominant : (Function.Bijective p ∧ ∀ z, α z = 1) ∨
      (Function.Bijective q ∧ ∀ z, β z = 1)) :
    ∃ a b : ℝ,
      (∀ v, (∫ z, A z ∂μ) (e v) = f (reciprocalTensorSymbol
        ((a : ℂ) • p) ((a : ℂ) • pi) ((b : ℂ) • q) ((b : ℂ) • qi) v)) ∧
      ((a = 1 ∧ Function.Bijective p) ∨ (b = 1 ∧ Function.Bijective q)) := by
  let : CompleteSpace T := FiniteDimensional.complete ℂ T
  let L (a b : ℝ) : S →L[ℂ] T :=
    (f.toLinearMap.comp ((reciprocalTensorSymbol ((a : ℂ) • p) ((a : ℂ) • pi)
      ((b : ℂ) • q) ((b : ℂ) • qi)).comp e.symm.toLinearMap)).toContinuousLinearMap
  have hLeval (a b : ℝ) (v : (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) :
      L a b (e v) = f (reciprocalTensorSymbol ((a : ℂ) • p) ((a : ℂ) • pi)
        ((b : ℂ) • q) ((b : ℂ) • qi) v) := by
    change f (reciprocalTensorSymbol ((a : ℂ) • p) ((a : ℂ) • pi)
      ((b : ℂ) • q) ((b : ℂ) • qi) (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  have hlinear (a b : ℝ) : L a b = a • L 1 0 + b • L 0 1 := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    change L a b (e v) = a • L 1 0 (e v) + b • L 0 1 (e v)
    rw [hLeval, hLeval, hLeval]
    rw [← LinearMapClass.map_smul_of_tower f, ← LinearMapClass.map_smul_of_tower f,
      ← f.map_add]
    apply congrArg f
    simp only [reciprocalTensorSymbol, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right]
    apply Prod.ext
    · simp [Function.prod]
      rfl
    · simp only [Complex.coe_smul, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.coprod_apply, LinearMap.neg_apply, Complex.ofReal_one, one_smul,
        Complex.ofReal_zero, zero_smul, neg_zero, LinearMap.zero_apply, add_zero,
        zero_add, Prod.smul_mk, smul_neg, Prod.mk_add_mk]
      exact add_comm _ _
  have hAL (z : Ω) : A z = L (α z) (β z) := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    exact (hformula z v).trans (hLeval _ _ v).symm
  rcases hdominant with ⟨hpinv, hα⟩ | ⟨hqinv, hβ⟩
  · obtain ⟨b, hb⟩ := exists_integral_eq_add_smul A hA (L 1 0) (L 0 1) (by
      intro z
      refine ⟨β z, ?_⟩
      rw [hAL, hα, hlinear, one_smul])
    have hsame : (∫ z, A z ∂μ) = L 1 b := by
      rw [hb, hlinear 1 b, one_smul]
    refine ⟨1, b, ?_, Or.inl ⟨rfl, hpinv⟩⟩
    intro v
    rw [hsame]
    exact hLeval 1 b v
  · obtain ⟨a, ha⟩ := exists_integral_eq_add_smul A hA (L 0 1) (L 1 0) (by
      intro z
      refine ⟨α z, ?_⟩
      rw [hAL, hβ, hlinear, one_smul, add_comm])
    have hsame : (∫ z, A z ∂μ) = L a 1 := by
      rw [ha, hlinear a 1, one_smul, add_comm]
    refine ⟨a, 1, ?_, Or.inr ⟨rfl, hqinv⟩⟩
    intro v
    rw [hsame]
    exact hLeval a 1 v

set_option maxHeartbeats 800000 in

/-- A full-symbol probability average preserves a fixed dominant Hermitian factor. -/
theorem integral_reciprocalTensorSymbol_bijective_of_dominant
    (h₀ : InnerProductSpace.Core ℂ E₀) (h₁ : InnerProductSpace.Core ℂ E₁)
    (k₀ : InnerProductSpace.Core ℂ F₀) (k₁ : InnerProductSpace.Core ℂ F₁)
    (p : E₀ →ₗ[ℂ] E₁) (pi : E₁ →ₗ[ℂ] E₀)
    (q : F₀ →ₗ[ℂ] F₁) (qi : F₁ →ₗ[ℂ] F₀)
    (hp : ∀ u v, h₁.inner (p u) v = h₀.inner u (pi v))
    (hq : ∀ u v, k₁.inner (q u) v = k₀.inner u (qi v))
    (e : ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) ≃ₗ[ℂ] S)
    (f : ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) ≃ₗ[ℂ] T)
    (A : Ω → S →L[ℂ] T) (hA : Integrable A μ) (α β : Ω → ℝ)
    (hformula : ∀ z v, A z (e v) = f (reciprocalTensorSymbol
      ((α z : ℂ) • p) ((α z : ℂ) • pi) ((β z : ℂ) • q) ((β z : ℂ) • qi) v))
    (hdominant : (Function.Bijective p ∧ ∀ z, α z = 1) ∨
      (Function.Bijective q ∧ ∀ z, β z = 1)) :
    Function.Bijective ((∫ z, A z ∂μ) : S →L[ℂ] T) := by
  let : CompleteSpace T := FiniteDimensional.complete ℂ T
  let L (a b : ℝ) : S →L[ℂ] T :=
    (f.toLinearMap.comp ((reciprocalTensorSymbol ((a : ℂ) • p) ((a : ℂ) • pi)
      ((b : ℂ) • q) ((b : ℂ) • qi)).comp e.symm.toLinearMap)).toContinuousLinearMap
  have hLeval (a b : ℝ) (v : (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) :
      L a b (e v) = f (reciprocalTensorSymbol ((a : ℂ) • p) ((a : ℂ) • pi)
        ((b : ℂ) • q) ((b : ℂ) • qi) v) := by
    change f (reciprocalTensorSymbol ((a : ℂ) • p) ((a : ℂ) • pi)
      ((b : ℂ) • q) ((b : ℂ) • qi) (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  have hlinear (a b : ℝ) : L a b = a • L 1 0 + b • L 0 1 := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    change L a b (e v) = a • L 1 0 (e v) + b • L 0 1 (e v)
    rw [hLeval, hLeval, hLeval]
    rw [← LinearMapClass.map_smul_of_tower f, ← LinearMapClass.map_smul_of_tower f,
      ← f.map_add]
    apply congrArg f
    simp only [reciprocalTensorSymbol, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right]
    apply Prod.ext
    · simp [Function.prod]
      rfl
    · simp only [Complex.coe_smul, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.coprod_apply, LinearMap.neg_apply, Complex.ofReal_one, one_smul,
        Complex.ofReal_zero, zero_smul, neg_zero, LinearMap.zero_apply, add_zero,
        zero_add, Prod.smul_mk, smul_neg, Prod.mk_add_mk]
      exact add_comm _ _
  have hAL (z : Ω) : A z = L (α z) (β z) := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    exact (hformula z v).trans (hLeval _ _ v).symm
  have hbij (a b : ℝ)
      (h : (a ≠ 0 ∧ Function.Bijective p) ∨ (b ≠ 0 ∧ Function.Bijective q)) :
      Function.Bijective (L a b) := by
    exact f.bijective.comp ((reciprocalTensorSymbol_bijective_of_hermitian_adjoint
      h₀ h₁ k₀ k₁ p pi q qi hp hq a b h).comp e.symm.bijective)
  -- The matrix-valued integral stays in a closed real affine line through the dominant block.
  rcases hdominant with ⟨hpinv, hα⟩ | ⟨hqinv, hβ⟩
  · obtain ⟨b, hb⟩ := exists_integral_eq_add_smul A hA (L 1 0) (L 0 1) (by
      intro z
      refine ⟨β z, ?_⟩
      rw [hAL, hα, hlinear, one_smul])
    have hsame : (∫ z, A z ∂μ) = L 1 b := by
      rw [hb, hlinear 1 b, one_smul]
    rw [hsame]
    exact hbij 1 b (Or.inl ⟨one_ne_zero, hpinv⟩)
  · obtain ⟨a, ha⟩ := exists_integral_eq_add_smul A hA (L 0 1) (L 1 0) (by
      intro z
      refine ⟨α z, ?_⟩
      rw [hAL, hβ, hlinear, one_smul, add_comm])
    have hsame : (∫ z, A z ∂μ) = L a 1 := by
      rw [ha, hlinear a 1, one_smul, add_comm]
    rw [hsame]
    exact hbij a 1 (Or.inr ⟨one_ne_zero, hqinv⟩)

end AtiyahSinger
