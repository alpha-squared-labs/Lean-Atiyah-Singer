/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockOperator
public import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Operator-norm limits of graded block matrices

Public module ID: M0689.

The four original entries converge in norm, hence so does their signed graded
matrix in the fixed ℓ²-sums. This applies to both parity directions of
the associated product, including their actual compact residual corrections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped Topology

/-- Convergence of the four entries gives convergence of the same graded matrix. -/
theorem tendsto_gradedBlockOperator {E₀ E₁ F₀ F₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    (U : ℕ → E₀ →L[ℂ] F₀) (V : ℕ → E₀ →L[ℂ] F₁)
    (W : ℕ → E₁ →L[ℂ] F₀) (Z : ℕ → E₁ →L[ℂ] F₁)
    (u : E₀ →L[ℂ] F₀) (v : E₀ →L[ℂ] F₁)
    (w : E₁ →L[ℂ] F₀) (z : E₁ →L[ℂ] F₁)
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v))
    (hW : Tendsto W atTop (𝓝 w)) (hZ : Tendsto Z atTop (𝓝 z)) :
    Tendsto (fun m ↦ gradedBlockOperator (U m) (V m) (W m) (Z m)) atTop
      (𝓝 (gradedBlockOperator u v w z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- The difference is the same signed matrix of the four entrywise differences.
  have heq (m : ℕ) : gradedBlockOperator (U m) (V m) (W m) (Z m) -
      gradedBlockOperator u v w z =
        gradedBlockOperator (U m - u) (V m - v) (W m - w) (Z m - z) := by
    ext x
    apply WithLp.ofLp_injective
    apply Prod.ext <;>
      simp only [gradedBlockOperator, ContinuousLinearMap.comp_apply,
        sub_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coprod_apply, neg_apply,
        ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_apply,
        WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp,
        WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub] <;> abel
  -- The fixed ℓ²-sum norm constants send the four vanishing errors to zero.
  apply squeeze_zero (fun m ↦ norm_nonneg _)
    (fun m ↦ (congrArg norm (heq m)).trans_le
      (norm_gradedBlockOperator_le (U m - u) (V m - v) (W m - w) (Z m - z)))
  have hz := ((tendsto_iff_norm_sub_tendsto_zero.mp hU).add
    (tendsto_iff_norm_sub_tendsto_zero.mp hV)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hW) |>.add
        (tendsto_iff_norm_sub_tendsto_zero.mp hZ)
  simpa only [add_zero, mul_zero, zero_mul] using
    (hz.const_mul
      ‖(WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁).symm.toContinuousLinearMap‖).mul_const
        ‖(WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toContinuousLinearMap‖

end AtiyahSinger
