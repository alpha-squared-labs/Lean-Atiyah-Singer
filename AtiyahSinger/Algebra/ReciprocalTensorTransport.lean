/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol

/-!
# Coordinate transport of the reciprocal tensor symbol

Public module ID: M0050.

The four original fiber equivalences transport the exact forward
map. This is used for the specified small bundle models and for comparing
the same boundary matrices with exterior parity coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {E₀ E₁ F₀ F₁ G₀ G₁ H₀ H₁ : Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [AddCommGroup E₁] [Module ℂ E₁]
  [AddCommGroup F₀] [Module ℂ F₀] [AddCommGroup F₁] [Module ℂ F₁]
  [AddCommGroup G₀] [Module ℂ G₀] [AddCommGroup G₁] [Module ℂ G₁]
  [AddCommGroup H₀] [Module ℂ H₀] [AddCommGroup H₁] [Module ℂ H₁]

/-- Four specified fiber equivalences intertwine the exact positive-convention tensor blocks. -/
theorem reciprocalTensorSymbol_congr
    (i₀ : E₀ ≃ₗ[ℂ] G₀) (i₁ : E₁ ≃ₗ[ℂ] G₁)
    (j₀ : F₀ ≃ₗ[ℂ] H₀) (j₁ : F₁ ≃ₗ[ℂ] H₁)
    (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) :
    ((TensorProduct.congr i₁ j₀).prodCongr (TensorProduct.congr i₀ j₁)).toLinearMap.comp
        (reciprocalTensorSymbol d d' e e') =
      (reciprocalTensorSymbol
        (i₁.toLinearMap.comp (d.comp i₀.symm.toLinearMap))
        (i₀.toLinearMap.comp (d'.comp i₁.symm.toLinearMap))
        (j₁.toLinearMap.comp (e.comp j₀.symm.toLinearMap))
        (j₀.toLinearMap.comp (e'.comp j₁.symm.toLinearMap))).comp
          ((TensorProduct.congr i₀ j₀).prodCongr (TensorProduct.congr i₁ j₁)).toLinearMap := by
  -- Check the two source summands on pure tensors; their original order is unchanged.
  ext x <;>
    simp only [LinearEquiv.coe_prodCongr, TensorProduct.toLinearMap_congr, LinearMap.coe_comp,
      LinearMap.coe_inl, LinearMap.coe_inr, Function.comp_apply, Function.prod,
      LinearMap.prodMap_apply,
      reciprocalTensorSymbol, LinearMap.prod_apply, LinearMap.coprod_apply, LinearMap.neg_apply,
      map_zero, add_zero, zero_add, map_neg, neg_inj]
  all_goals
    induction x using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

end AtiyahSinger
