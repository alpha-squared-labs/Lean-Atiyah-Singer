/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RightProductCutoffRealization

/-!
# Right tensor coefficient matrices

Public module ID: M0933.

The fixed finite tensor-basis permutations realize identity tensored with a
coefficient map. The calculation identifies the actual right cutoff symbol
in the original product coordinates, before geometric frame conjugation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- Identity tensored with a coefficient map, in the original finite tensor basis. -/
def identityTensorSymbolMap (r s t : ℕ) :
    (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t)) →L[ℂ]
      (EuclideanSpace ℂ (Fin (r * s)) →L[ℂ] EuclideanSpace ℂ (Fin (r * t))) :=
  LinearMap.toContinuousLinearMap {
    toFun a := (tensorCoordinateSwap r t).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((tensorIdentitySymbolMap s t r a).comp
        (tensorCoordinateSwap r s).toContinuousLinearEquiv.toContinuousLinearMap)
    map_add' a b := by ext w; simp
    map_smul' z a := by ext w; simp }

/-- The right coefficient map retains the given order of the two pure tensor factors. -/
theorem identityTensorSymbolMap_apply {r s t : ℕ}
    (a : EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))
    (u : EuclideanSpace ℂ (Fin r)) (v : EuclideanSpace ℂ (Fin s))
    (w : EuclideanSpace ℂ (Fin (r * s)))
    (hw : ∀ i j, w (finProdFinEquiv (i, j)) = u i * v j) (i : Fin r) (j : Fin t) :
    identityTensorSymbolMap r s t a w (finProdFinEquiv (i, j)) = u i * a v j := by
  have hw' (j' : Fin s) (i' : Fin r) :
      tensorCoordinateSwap r s w (finProdFinEquiv (j', i')) = v j' * u i' := by
    rw [tensorCoordinateSwap_apply, hw]
    exact mul_comm _ _
  have ho (z : EuclideanSpace ℂ (Fin (t * r))) :
      (tensorCoordinateSwap r t).symm z (finProdFinEquiv (i, j)) =
        z (finProdFinEquiv (j, i)) := by
    have h := tensorCoordinateSwap_apply r t ((tensorCoordinateSwap r t).symm z) i j
    rw [(tensorCoordinateSwap r t).apply_symm_apply] at h
    exact h.symm
  change (tensorCoordinateSwap r t).symm
    (tensorIdentitySymbolMap s t r a (tensorCoordinateSwap r s w)) _ = _
  rw [ho, tensorIdentitySymbolMap_apply a v u _ hw']
  exact mul_comm _ _

/-- The actual right cutoff is its scalar frequency and spatial weights times id tensor a. -/
theorem rightProductCutoffSymbol_eq {n m r s t : ℕ} (a : SymbolFunction m s t)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (x ξ : EuclideanSpace ℝ (Fin n)) (y η : EuclideanSpace ℝ (Fin m)) :
    rightProductCutoffSymbol (fun y η ↦ tensorIdentitySymbolMap s t r (a y η)) χ ε
      (EuclideanSpace.finAddEquivProd.symm (x, y))
      (EuclideanSpace.finAddEquivProd.symm (ξ, η)) =
        (productFrequencyCutoff ε ‖η‖ ‖ξ‖ : ℂ) •
          ((χ x : ℂ) • identityTensorSymbolMap r s t (a y η)) := by
  ext w
  simp only [rightProductCutoffSymbol, isometricSymbolTransport,
    productCoordinateSwap_apply, productCutoffSymbol, liftedProductSymbol,
    ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  rfl

end AtiyahSinger
