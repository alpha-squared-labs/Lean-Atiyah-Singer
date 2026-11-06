/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Inverse bounds in specified tensor and orthogonal sum metrics

Public module ID: M0035.

An inverse bound on the original Hilbert tensor factors transfers to the
specified native sum through its actual linear equivalences and pairings.
The maximum product norm and orthogonal sum energy are compared explicitly;
the resulting factor two is independent of the point and of the parameters.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

-- Implementation lemma: pure tensors determine the full specified Hermitian pairing.
private theorem tensor_equiv_core_inner {E F N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [AddCommGroup N] [Module ℂ N]
    (h : InnerProductSpace.Core ℂ N) (e : E ⊗[ℂ] F ≃ₗ[ℂ] N)
    (he : ∀ u v a b, h.inner (e (u ⊗ₜ[ℂ] a)) (e (v ⊗ₜ[ℂ] b)) =
      inner ℂ u v * inner ℂ a b) (u v : E ⊗[ℂ] F) :
    h.inner (e u) (e v) = inner ℂ u v := by
  induction u using TensorProduct.inductionOn with
  | tmul u a =>
    induction v using TensorProduct.inductionOn with
    | tmul v b => exact he u v a b
    | add v w hv hw =>
      simpa only [map_add, InnerProductSpace.Core.inner_add_right, inner_add_right]
        using congrArg₂ (· + ·) hv hw
  | add u w hu hw =>
    simpa only [map_add, InnerProductSpace.Core.inner_add_left, inner_add_left]
      using congrArg₂ (· + ·) hu hw

variable {E₀ E₁ F₀ F₁ N₀₀ N₁₀ N₀₁ N₁₁ Nplus Nminus : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁]
  [AddCommGroup N₀₀] [Module ℂ N₀₀] [AddCommGroup N₁₀] [Module ℂ N₁₀]
  [AddCommGroup N₀₁] [Module ℂ N₀₁] [AddCommGroup N₁₁] [Module ℂ N₁₁]
  [AddCommGroup Nplus] [Module ℂ Nplus] [AddCommGroup Nminus] [Module ℂ Nminus]

/-- A tensor inverse bound controls the same map in its specified orthogonal sum metrics. -/
theorem bijective_and_energy_bound_of_tensor_orthogonal_sum
    (e₀₀ : E₀ ⊗[ℂ] F₀ ≃ₗ[ℂ] N₀₀) (e₁₀ : E₁ ⊗[ℂ] F₀ ≃ₗ[ℂ] N₁₀)
    (e₀₁ : E₀ ⊗[ℂ] F₁ ≃ₗ[ℂ] N₀₁) (e₁₁ : E₁ ⊗[ℂ] F₁ ≃ₗ[ℂ] N₁₁)
    (ePlus : (N₀₀ × N₁₁) ≃ₗ[ℂ] Nplus) (eMinus : (N₁₀ × N₀₁) ≃ₗ[ℂ] Nminus)
    (h₀₀ : InnerProductSpace.Core ℂ N₀₀) (h₁₀ : InnerProductSpace.Core ℂ N₁₀)
    (h₀₁ : InnerProductSpace.Core ℂ N₀₁) (h₁₁ : InnerProductSpace.Core ℂ N₁₁)
    (hPlus : InnerProductSpace.Core ℂ Nplus) (hMinus : InnerProductSpace.Core ℂ Nminus)
    (he₀₀ : ∀ u v a b, h₀₀.inner (e₀₀ (u ⊗ₜ[ℂ] a)) (e₀₀ (v ⊗ₜ[ℂ] b)) =
      inner ℂ u v * inner ℂ a b)
    (he₁₀ : ∀ u v a b, h₁₀.inner (e₁₀ (u ⊗ₜ[ℂ] a)) (e₁₀ (v ⊗ₜ[ℂ] b)) =
      inner ℂ u v * inner ℂ a b)
    (he₀₁ : ∀ u v a b, h₀₁.inner (e₀₁ (u ⊗ₜ[ℂ] a)) (e₀₁ (v ⊗ₜ[ℂ] b)) =
      inner ℂ u v * inner ℂ a b)
    (he₁₁ : ∀ u v a b, h₁₁.inner (e₁₁ (u ⊗ₜ[ℂ] a)) (e₁₁ (v ⊗ₜ[ℂ] b)) =
      inner ℂ u v * inner ℂ a b)
    (hePlus : ∀ u v, hPlus.inner (ePlus u) (ePlus v) =
      h₀₀.inner u.1 v.1 + h₁₁.inner u.2 v.2)
    (heMinus : ∀ u v, hMinus.inner (eMinus u) (eMinus v) =
      h₁₀.inner u.1 v.1 + h₀₁.inner u.2 v.2)
    (T : (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁) →ₗ[ℂ]
      (E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁))
    (A : Nplus →ₗ[ℂ] Nminus)
    (hA : ∀ u v, A (ePlus (e₀₀ u, e₁₁ v)) = eMinus (e₁₀ (T (u, v)).1,
      e₀₁ (T (u, v)).2))
    (w M : ℝ) (hw : 0 < w)
    (hbij : Function.Bijective T) (hbound : ∀ u, ‖u‖ ≤ (M / w) * ‖T u‖) :
    Function.Bijective A ∧ ∀ u, w ^ 2 * (hPlus.inner u u).re ≤
      (2 * M ^ 2) * (hMinus.inner (A u) (A u)).re := by
  -- The exact tensor and sum equivalences transport both injectivity and surjectivity.
  let s := (e₀₀.prodCongr e₁₁).trans ePlus
  let t := (e₁₀.prodCongr e₀₁).trans eMinus
  have hconj : A = t.toLinearMap.comp (T.comp s.symm.toLinearMap) := by
    ext u
    obtain ⟨v, rfl⟩ := s.surjective u
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, s.symm_apply_apply] using
      (show A (s v) = t (T v) by
        change A (ePlus (e₀₀ v.1, e₁₁ v.2)) =
          eMinus (e₁₀ (T v).1, e₀₁ (T v).2)
        exact hA v.1 v.2)
  constructor
  · rw [hconj]
    exact t.bijective.comp (hbij.comp s.symm.bijective)
  intro u
  obtain ⟨v, rfl⟩ := s.surjective u
  have hs : (hPlus.inner (s v) (s v)).re = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    rw [show s v = ePlus (e₀₀ v.1, e₁₁ v.2) from rfl, hePlus]
    rw [tensor_equiv_core_inner h₀₀ e₀₀ he₀₀,
      tensor_equiv_core_inner h₁₁ e₁₁ he₁₁, Complex.add_re]
    exact congrArg₂ (· + ·) (inner_self_eq_norm_sq (𝕜 := ℂ) _)
      (inner_self_eq_norm_sq (𝕜 := ℂ) _)
  have ht : (hMinus.inner (A (s v)) (A (s v))).re =
      ‖(T v).1‖ ^ 2 + ‖(T v).2‖ ^ 2 := by
    rw [show s v = ePlus (e₀₀ v.1, e₁₁ v.2) from rfl, hA, heMinus]
    rw [tensor_equiv_core_inner h₁₀ e₁₀ he₁₀,
      tensor_equiv_core_inner h₀₁ e₀₁ he₀₁, Complex.add_re]
    exact congrArg₂ (· + ·) (inner_self_eq_norm_sq (𝕜 := ℂ) _)
      (inner_self_eq_norm_sq (𝕜 := ℂ) _)
  -- The original product norm is the maximum, while the specified sum has squared-sum energy.
  have hsource : ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    have h₀ := pow_le_pow_left₀ (norm_nonneg v.1) (norm_fst_le v) 2
    have h₁ := pow_le_pow_left₀ (norm_nonneg v.2) (norm_snd_le v) 2
    linarith
  have htarget : ‖T v‖ ^ 2 ≤ ‖(T v).1‖ ^ 2 + ‖(T v).2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖(T v).1‖ ‖(T v).2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖(T v).1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖(T v).2‖]
  have hweighted : w * ‖v‖ ≤ M * ‖T v‖ := by
    have hb := (mul_le_mul_of_nonneg_left (hbound v) hw.le)
    rwa [← mul_assoc, mul_div_cancel₀ M hw.ne'] at hb
  have hsquared := pow_le_pow_left₀ (by positivity : 0 ≤ w * ‖v‖) hweighted 2
  simp only [mul_pow] at hsquared
  rw [hs, ht]
  calc
    w ^ 2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) ≤ w ^ 2 * (2 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsource (sq_nonneg w)
    _ ≤ 2 * (M ^ 2 * ‖T v‖ ^ 2) := by nlinarith [hsquared]
    _ ≤ (2 * M ^ 2) * (‖(T v).1‖ ^ 2 + ‖(T v).2‖ ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left htarget (show 0 ≤ 2 * M ^ 2 by positivity)

end AtiyahSinger
