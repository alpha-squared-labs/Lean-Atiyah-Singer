/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockOperator
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The kernel of a graded block with cancelling cross terms

Public module ID: M0688.

The actual bounded graded matrix has the product of the two joint kernels
when its cross pairings agree. The norm identity is proved on the supplied
spaces and maps; no tensor-product realization or equality of ranks is used.
This is the kernel splitting needed after the horizontal and vertical actions
in SG III.13.6 have been realized on their actual common domains. Establishing
the domains and pairings is handled by the joint-domain realization modules.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁]

/-- Cancellation of the two cross pairings identifies the actual graded block kernel. -/
theorem ker_gradedBlockOperator_of_inner_eq
    (U : E₀ →L[ℂ] F₀) (V : E₀ →L[ℂ] F₁)
    (W : E₁ →L[ℂ] F₀) (Z : E₁ →L[ℂ] F₁)
    (hcross : ∀ (u : E₀) (v : E₁), inner ℂ (U u) (W v) = inner ℂ (V u) (Z v)) :
    (gradedBlockOperator U V W Z).ker =
      ((U.ker ⊓ V.ker).prod (W.ker ⊓ Z.ker)).comap
        (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toLinearMap := by
  -- The specified minus sign cancels the real cross terms and leaves four nonnegative terms.
  have henergy (u : E₀) (v : E₁) :
      ‖U u - W v‖ ^ 2 + ‖V u + Z v‖ ^ 2 =
        ‖U u‖ ^ 2 + ‖V u‖ ^ 2 + ‖W v‖ ^ 2 + ‖Z v‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hcross]
    ring
  apply Submodule.ext
  intro x
  let u := x.ofLp.1
  let v := x.ofLp.2
  change gradedBlockOperator U V W Z x = 0 ↔
    (U u = 0 ∧ V u = 0) ∧ W v = 0 ∧ Z v = 0
  have hzero : gradedBlockOperator U V W Z x = 0 ↔
      U u - W v = 0 ∧ V u + Z v = 0 := by
    constructor
    · intro h
      have h' := congrArg WithLp.ofLp h
      have h₀ : U u + -(W v) = 0 := congrArg Prod.fst h'
      have h₁ : V u + Z v = 0 := congrArg Prod.snd h'
      exact ⟨by simpa only [sub_eq_add_neg] using h₀, h₁⟩
    · rintro ⟨h₀, h₁⟩
      apply (WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁).injective
      change (U u + -(W v), V u + Z v) = (0, 0)
      exact Prod.ext (by simpa only [sub_eq_add_neg] using h₀) h₁
  rw [hzero]
  constructor
  · rintro ⟨h₀, h₁⟩
    have h := henergy u v
    simp only [h₀, h₁, norm_zero] at h
    have hU : ‖U u‖ = 0 := by
      nlinarith [norm_nonneg (U u), sq_nonneg ‖V u‖, sq_nonneg ‖W v‖, sq_nonneg ‖Z v‖]
    have hV : ‖V u‖ = 0 := by
      nlinarith [norm_nonneg (V u), sq_nonneg ‖U u‖, sq_nonneg ‖W v‖, sq_nonneg ‖Z v‖]
    have hW : ‖W v‖ = 0 := by
      nlinarith [norm_nonneg (W v), sq_nonneg ‖U u‖, sq_nonneg ‖V u‖, sq_nonneg ‖Z v‖]
    have hZ : ‖Z v‖ = 0 := by
      nlinarith [norm_nonneg (Z v), sq_nonneg ‖U u‖, sq_nonneg ‖V u‖, sq_nonneg ‖W v‖]
    exact ⟨⟨norm_eq_zero.mp hU, norm_eq_zero.mp hV⟩, norm_eq_zero.mp hW, norm_eq_zero.mp hZ⟩
  · rintro ⟨⟨hU, hV⟩, hW, hZ⟩
    simp only [hU, hV, hW, hZ, sub_self, add_zero, and_self]

end AtiyahSinger
