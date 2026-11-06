/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockOperator

/-!
# Addition and off-diagonal corrections of graded block operators

Public module ID: M0685.

The existing signed block operator is additive in its four entries. A specified
off-diagonal correction, written with the original product projections and
injections, therefore updates exactly the two off-diagonal entries.

These are elementary bounded-operator identities for normed complex vector
spaces. They require neither completeness nor an inner product. The intended
application is the two compact residual blocks in the index comparison;
this is project-level block algebra, not an additional result from Spin Geometry.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Adding the four entries adds their signed graded block operators. -/
theorem gradedBlockOperator_add {E₀ E₁ F₀ F₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    (U U' : E₀ →L[ℂ] F₀) (V V' : E₀ →L[ℂ] F₁)
    (W W' : E₁ →L[ℂ] F₀) (Z Z' : E₁ →L[ℂ] F₁) :
    gradedBlockOperator (U + U') (V + V') (W + W') (Z + Z') =
      gradedBlockOperator U V W Z + gradedBlockOperator U' V' W' Z' := by
  -- Pass through the fixed WithLp 2 product coordinates and compare the two rows.
  ext x
  apply WithLp.ofLp_injective
  apply Prod.ext <;>
    simp only [gradedBlockOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply, add_apply, neg_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_apply,
      WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp,
      WithLp.ofLp_add, Prod.fst_add, Prod.snd_add] <;> abel

/-- An off-diagonal correction updates the two original entries with their block signs.
The lower-left correction is `A`, while the upper-right correction is `-B`. -/
theorem gradedBlockOperator_add_offDiagonal {E₀ E₁ F₀ F₁ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    (U : E₀ →L[ℂ] F₀) (V : E₀ →L[ℂ] F₁)
    (W : E₁ →L[ℂ] F₀) (Z : E₁ →L[ℂ] F₁)
    (A : E₀ →L[ℂ] F₁) (B : E₁ →L[ℂ] F₀) :
    let cI := WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁
    let cO := WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁
    let p₀ := (ContinuousLinearMap.fst ℂ E₀ E₁).comp cI.toContinuousLinearMap
    let p₁ := (ContinuousLinearMap.snd ℂ E₀ E₁).comp cI.toContinuousLinearMap
    gradedBlockOperator U V W Z +
        (cO.symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.inr ℂ F₀ F₁).comp (A.comp p₀)) +
        cO.symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.inl ℂ F₀ F₁).comp ((-B).comp p₁))) =
      gradedBlockOperator U (V + A) (W + B) Z := by
  intro cI cO p₀ p₁
  -- The specified injections and projections give the block with zero diagonal.
  have hresidual :
      cO.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr ℂ F₀ F₁).comp (A.comp p₀)) +
      cO.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℂ F₀ F₁).comp ((-B).comp p₁)) =
      gradedBlockOperator (0 : E₀ →L[ℂ] F₀) A B (0 : E₁ →L[ℂ] F₁) := by
    ext x
    apply WithLp.ofLp_injective
    apply Prod.ext <;>
      simp only [gradedBlockOperator, p₀, p₁, cI, cO,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coprod_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', add_apply, neg_apply, _root_.zero_apply,
        ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_apply,
        WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp,
        WithLp.ofLp_add, Prod.fst_add, Prod.snd_add]
  -- Add that same block and use entrywise additivity; the diagonal entries stay fixed.
  calc
    _ = gradedBlockOperator U V W Z +
        gradedBlockOperator (0 : E₀ →L[ℂ] F₀) A B (0 : E₁ →L[ℂ] F₁) :=
      congrArg (fun T : WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁) ↦
        gradedBlockOperator U V W Z + T) hresidual
    _ = gradedBlockOperator (U + 0) (V + A) (W + B) (Z + 0) :=
      (gradedBlockOperator_add U 0 V A W B Z 0).symm
    _ = gradedBlockOperator U (V + A) (W + B) Z := by
      rw [add_zero, add_zero]

end AtiyahSinger
