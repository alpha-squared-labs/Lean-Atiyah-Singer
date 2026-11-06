/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Bounded graded block matrices on ℓ² direct sums

Public module ID: M0690.

The four specified bounded maps give the original graded matrix, including its
negative upper-right entry. The norm estimate compares these same maps and
uses the fixed equivalences between product and ℓ² direct-sum norms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]

/-- The bounded matrix with columns `(U,V)` and `(-W,Z)` in the fixed ℓ²-sums. -/
def gradedBlockOperator (U : E₀ →L[ℂ] F₀) (V : E₀ →L[ℂ] F₁)
    (W : E₁ →L[ℂ] F₀) (Z : E₁ →L[ℂ] F₁) :
    WithLp 2 (E₀ × E₁) →L[ℂ] WithLp 2 (F₀ × F₁) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁).symm.toContinuousLinearMap.comp
    (((U.coprod (-W)).prod (V.coprod Z)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toContinuousLinearMap)

/-- An explicit norm bound for the same four entries of the graded matrix. -/
theorem norm_gradedBlockOperator_le (U : E₀ →L[ℂ] F₀) (V : E₀ →L[ℂ] F₁)
    (W : E₁ →L[ℂ] F₀) (Z : E₁ →L[ℂ] F₁) :
    ‖gradedBlockOperator U V W Z‖ ≤
      ‖(WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁).symm.toContinuousLinearMap‖ *
        (‖U‖ + ‖V‖ + ‖W‖ + ‖Z‖) *
          ‖(WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toContinuousLinearMap‖ := by
  let I := (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toContinuousLinearMap
  let O := (WithLp.prodContinuousLinearEquiv 2 ℂ F₀ F₁).symm.toContinuousLinearMap
  let T := (U.coprod (-W)).prod (V.coprod Z)
  have hT : ‖T‖ ≤ ‖U‖ + ‖V‖ + ‖W‖ + ‖Z‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change max ‖U x.1 + -(W x.2)‖ ‖V x.1 + Z x.2‖ ≤ _
    apply max_le
    · calc
        ‖U x.1 + -(W x.2)‖ ≤ ‖U x.1‖ + ‖W x.2‖ := by
          simpa only [norm_neg] using norm_add_le (U x.1) (-(W x.2))
        _ ≤ ‖U‖ * ‖x.1‖ + ‖W‖ * ‖x.2‖ := add_le_add (U.le_opNorm _) (W.le_opNorm _)
        _ ≤ ‖U‖ * ‖x‖ + ‖W‖ * ‖x‖ := by
          gcongr
          · exact norm_fst_le x
          · exact norm_snd_le x
        _ ≤ _ := by nlinarith [norm_nonneg V, norm_nonneg Z, norm_nonneg x]
    · calc
        ‖V x.1 + Z x.2‖ ≤ ‖V x.1‖ + ‖Z x.2‖ := norm_add_le _ _
        _ ≤ ‖V‖ * ‖x.1‖ + ‖Z‖ * ‖x.2‖ := add_le_add (V.le_opNorm _) (Z.le_opNorm _)
        _ ≤ ‖V‖ * ‖x‖ + ‖Z‖ * ‖x‖ := by
          gcongr
          · exact norm_fst_le x
          · exact norm_snd_le x
        _ ≤ _ := by nlinarith [norm_nonneg U, norm_nonneg W, norm_nonneg x]
  exact ((O.opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (T.opNorm_comp_le I) (norm_nonneg O))).trans
      (by
        change ‖O‖ * (‖T‖ * ‖I‖) ≤ ‖O‖ * _ * ‖I‖
        rw [mul_assoc]
        gcongr)

end AtiyahSinger
