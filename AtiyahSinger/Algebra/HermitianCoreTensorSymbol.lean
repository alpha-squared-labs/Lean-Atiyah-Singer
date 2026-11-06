/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff

/-!
# The graded tensor symbol for prescribed Hermitian pairings

Public module ID: M0032.

Positive-definite Hermitian forms and their actual algebraic adjoints suffice
for the graded tensor invertibility argument. The temporary norms are used
only within this algebraic proof; no topology or bundle norm is changed in the
statement. This permits application to arbitrary supplied smooth metrics on
native bundle fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {E₀ E₁ F₀ F₁ : Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [FiniteDimensional ℂ E₀]
  [AddCommGroup E₁] [Module ℂ E₁] [FiniteDimensional ℂ E₁]
  [AddCommGroup F₀] [Module ℂ F₀] [FiniteDimensional ℂ F₀]
  [AddCommGroup F₁] [Module ℂ F₁] [FiniteDimensional ℂ F₁]

/-- One invertible weighted factor gives invertibility for the specified Hermitian adjoint pairs. -/
theorem reciprocalTensorSymbol_bijective_of_hermitian_adjoint
    (h₀ : InnerProductSpace.Core ℂ E₀) (h₁ : InnerProductSpace.Core ℂ E₁)
    (k₀ : InnerProductSpace.Core ℂ F₀) (k₁ : InnerProductSpace.Core ℂ F₁)
    (p : E₀ →ₗ[ℂ] E₁) (pi : E₁ →ₗ[ℂ] E₀)
    (q : F₀ →ₗ[ℂ] F₁) (qi : F₁ →ₗ[ℂ] F₀)
    (hp : ∀ u v, h₁.inner (p u) v = h₀.inner u (pi v))
    (hq : ∀ u v, k₁.inner (q u) v = k₀.inner u (qi v)) (α β : ℝ)
    (h : (α ≠ 0 ∧ Function.Bijective p) ∨ (β ≠ 0 ∧ Function.Bijective q)) :
    Function.Bijective (reciprocalTensorSymbol ((α : ℂ) • p) ((α : ℂ) • pi)
      ((β : ℂ) • q) ((β : ℂ) • qi)) := by
  -- Only algebraic maps occur in the conclusion; realize the specified forms locally.
  let := h₀
  let := h₁
  let := k₀
  let := k₁
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := E₀)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := E₁)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := F₀)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := F₁)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ E₀)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ E₁)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ F₀)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ F₁)
  have hpi : pi = p.adjoint := by
    have heq : p = pi.adjoint := (LinearMap.eq_adjoint_iff p pi).mpr hp
    rw [heq, LinearMap.adjoint_adjoint]
  have hqi : qi = q.adjoint := by
    have heq : q = qi.adjoint := (LinearMap.eq_adjoint_iff q qi).mpr hq
    rw [heq, LinearMap.adjoint_adjoint]
  -- The original reverse maps are now identified, rather than replaced by new choices.
  rw [hpi, hqi]
  exact weightedGradedTensorSymbol_bijective p q α β h

end AtiyahSinger
