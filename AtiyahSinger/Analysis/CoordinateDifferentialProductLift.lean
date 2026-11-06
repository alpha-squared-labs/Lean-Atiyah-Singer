/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialSymbol

/-!
# The horizontal lift of an actual coordinate differential expression

Public module ID: M0408.

The original ordered coefficients are embedded in one extra Euclidean
direction, with zero coefficients for derivatives using that direction.
The total and principal polynomials therefore retain the original coefficients
and evaluate the original symbol at the horizontal frequency. This lets the
ordinary symbol estimates in dimension n+1 control a real resolvent parameter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open scoped ContDiff

variable {n r q m : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- Lift the original expression to the first factor, with no new directional derivative. -/
def firstFactorLift (P : CoordinateDifferentialOperator n r q m U) :
    CoordinateDifferentialOperator (n + 1) r q m
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U) := by
  classical
  let π₁ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin 1))).comp
        EuclideanSpace.finAddEquivProd.toContinuousLinearMap
  refine {
    coefficient k β z := ∑ α : Fin k.val → Fin n,
      if (fun j ↦ (α j).castSucc) = β then P.coefficient k α (π₁ z) else 0
    smooth_coefficient := ?_ }
  intro k β
  apply ContDiffOn.sum
  intro α _
  split_ifs
  · exact (P.smooth_coefficient k α).comp_continuousLinearMap π₁
  · exact contDiffOn_const

/-- The lifted total polynomial is the original polynomial at horizontal frequency. -/
theorem firstFactorLift_totalSymbol (P : CoordinateDifferentialOperator n r q m U)
    (z ζ : EuclideanSpace ℝ (Fin (n + 1))) :
    P.firstFactorLift.totalSymbol z ζ =
      P.totalSymbol (EuclideanSpace.finAddEquivProd z).1
        (EuclideanSpace.finAddEquivProd ζ).1 := by
  classical
  have hprojection (η : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) η).1 i =
        η i.castSucc := rfl
  unfold totalSymbol
  apply Finset.sum_congr rfl
  intro k _
  change (∑ β : Fin k.val → Fin (n + 1), (∏ j, ζ (β j)) •
      ∑ α : Fin k.val → Fin n,
        if (fun j ↦ (α j).castSucc) = β then
          P.coefficient k α (EuclideanSpace.finAddEquivProd z).1 else 0) = _
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp only [smul_ite, smul_zero, Fintype.sum_ite_eq, hprojection]

/-- The highest polynomial retains the same horizontal principal symbol, including order zero. -/
theorem firstFactorLift_principalSymbol (P : CoordinateDifferentialOperator n r q m U)
    (z ζ : EuclideanSpace ℝ (Fin (n + 1))) :
    P.firstFactorLift.principalSymbol z ζ =
      P.principalSymbol (EuclideanSpace.finAddEquivProd z).1
        (EuclideanSpace.finAddEquivProd ζ).1 := by
  classical
  have hprojection (η : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) η).1 i =
        η i.castSucc := rfl
  unfold principalSymbol
  change (∑ β : Fin m → Fin (n + 1), (∏ j, ζ (β j)) •
      ∑ α : Fin m → Fin n,
        if (fun j ↦ (α j).castSucc) = β then
          P.coefficient ⟨m, Nat.lt_succ_self m⟩ α
            (EuclideanSpace.finAddEquivProd z).1 else 0) = _
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp only [smul_ite, smul_zero, Fintype.sum_ite_eq, hprojection]

/-- The lifted expression acts on pullback functions by the same original differential operator. -/
theorem firstFactorLift_apply_comp (P : CoordinateDifferentialOperator n r q m U)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hu : ContDiff ℝ ∞ u) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    P.firstFactorLift.apply
        (fun w ↦ u (EuclideanSpace.finAddEquivProd w).1) z =
      P.apply u (EuclideanSpace.finAddEquivProd z).1 := by
  classical
  let π₁ : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin 1))).comp
        EuclideanSpace.finAddEquivProd.toContinuousLinearMap
  have hprojection (η : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
      π₁ η i = η i.castSucc := rfl
  have hsingle (i : Fin n) :
      π₁ (EuclideanSpace.single i.castSucc 1) = EuclideanSpace.single i 1 := by
    ext j
    simp only [hprojection, PiLp.single_apply, Fin.castSucc_inj]
  have hderivative (k : ℕ) (α : Fin k → Fin n) :
      iteratedFDeriv ℝ k (u ∘ π₁) z
          (fun j ↦ EuclideanSpace.single (α j).castSucc 1) =
        iteratedFDeriv ℝ k u (π₁ z) (fun j ↦ EuclideanSpace.single (α j) 1) := by
    rw [π₁.iteratedFDeriv_comp_right hu z (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hsingle]
  -- Reorder the finite coefficient sum and retain only the original horizontal indices.
  unfold apply
  apply Finset.sum_congr rfl
  intro k _
  change (∑ β : Fin k.val → Fin (n + 1),
      (∑ α : Fin k.val → Fin n,
        if (fun j ↦ (α j).castSucc) = β then P.coefficient k α (π₁ z) else 0)
          (((-Complex.I) ^ k.val) • iteratedFDeriv ℝ k.val (u ∘ π₁) z
            (fun j ↦ EuclideanSpace.single (β j) 1))) = _
  simp_rw [sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_eq_single (fun j ↦ (α j).castSucc)]
  · rw [ite_eq_left rfl, hderivative]
    rfl
  · intro β _ hβ
    simp only [ite_eq_right (Ne.symm hβ), zero_apply]
  · simp

end AtiyahSinger.CoordinateDifferentialOperator
