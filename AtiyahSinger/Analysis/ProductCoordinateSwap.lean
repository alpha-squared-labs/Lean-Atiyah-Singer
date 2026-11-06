/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IsometricQuantization

/-!
# The two exact coordinate permutations for tensor factors

Public module ID: M0874.

The real base coordinates use concatenation, while the complex tensor fiber
uses the finite product basis. Swapping the factors requires these two distinct
orthogonal permutations. Their formulas retain the original index order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Exchange the two concatenated Euclidean coordinate blocks. -/
def productCoordinateSwap (n m : ℕ) :
    EuclideanSpace ℝ (Fin (n + m)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin m))).trans finSumFinEquiv)

/-- The real block permutation swaps the two original concatenated coordinates. -/
theorem productCoordinateSwap_apply (n m : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    productCoordinateSwap n m (EuclideanSpace.finAddEquivProd.symm (x, y)) =
      EuclideanSpace.finAddEquivProd.symm (y, x) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    change (e.symm (x, y))
      (finSumFinEquiv ((Equiv.sumComm (Fin n) (Fin m)).symm
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))))) = y i
    rw [Equiv.symm_apply_apply]
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ z.2 i)
      (e.apply_symm_apply (x, y))
  · ext i
    change (e.symm (x, y))
      (finSumFinEquiv ((Equiv.sumComm (Fin n) (Fin m)).symm
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))))) = x i
    rw [Equiv.symm_apply_apply]
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ z.1 i)
      (e.apply_symm_apply (x, y))

/-- Exchange the factors of the fixed finite tensor-coordinate basis. -/
def tensorCoordinateSwap (r s : ℕ) :
    EuclideanSpace ℂ (Fin (r * s)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (s * r)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((finProdFinEquiv.symm.trans (Equiv.prodComm (Fin r) (Fin s))).trans finProdFinEquiv)

/-- The complex permutation uses the product-basis order, independently of base concatenation. -/
theorem tensorCoordinateSwap_apply (r s : ℕ) (u : EuclideanSpace ℂ (Fin (r * s)))
    (i : Fin r) (j : Fin s) :
    tensorCoordinateSwap r s u (finProdFinEquiv (j, i)) = u (finProdFinEquiv (i, j)) := by
  change u (finProdFinEquiv ((Equiv.prodComm (Fin r) (Fin s)).symm
    (finProdFinEquiv.symm (finProdFinEquiv (j, i))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end AtiyahSinger
