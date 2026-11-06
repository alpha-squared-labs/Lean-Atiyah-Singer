/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IsometricSymbolTransport
public import AtiyahSinger.Analysis.ProductCoordinateSwap

/-!
# Right-factor product cutoffs in the original coordinate order

Public module ID: M0930.

The first coordinate block and first finite fiber remain first. Orthogonal
base and tensor-basis permutations transport the actual left-factor cutoff
operator to this order. Its Bessel realization and norm approximation retain
the original pure-tensor action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n m r s t : ℕ}

/-- The actual right-factor frequency cutoff in the original base and tensor coordinate order. -/
def rightProductCutoffSymbol (α : SymbolFunction m (s * r) (t * r))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) :
    SymbolFunction (n + m) (r * s) (r * t) :=
  isometricSymbolTransport (productCoordinateSwap n m) (tensorCoordinateSwap r s)
    (tensorCoordinateSwap r t).symm (productCutoffSymbol α χ ε)

/-- A positive right-factor cutoff is a genuine isotropic symbol of order one. -/
theorem isSymbol_rightProductCutoffSymbol (α : SymbolFunction m (s * r) (t * r))
    (hα : IsSymbol Set.univ 1 α) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (ε : ℝ) (hε : 0 < ε) :
    IsSymbol Set.univ 1 (rightProductCutoffSymbol α χ ε) :=
  isSymbol_isometricSymbolTransport _ _ _ 1 _ (isSymbol_productCutoffSymbol α hα χ hχ ε hε)

/-- The right-factor cutoff retains compact spatial support in the original coordinate order. -/
theorem hasCompactSupport_rightProductCutoffSymbol (α : SymbolFunction m (s * r) (t * r))
    (hα : HasCompactSupport α) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : HasCompactSupport χ) (ε : ℝ) :
    HasCompactSupport (rightProductCutoffSymbol α χ ε) :=
  hasCompactSupport_isometricSymbolTransport _ _ _ _
    (hasCompactSupport_productCutoffSymbol α hα χ hχ ε)

/-- Bessel realization of the right cutoff, using the two fixed coordinate isometries. -/
def rightProductCutoffSobolevOperator
    (α : SymbolFunction m (s * r) (t * r)) (hα : IsSymbol Set.univ 1 α)
    (hαK : HasCompactSupport α) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ) (ε : ℝ) (hε : 0 < ε) :
    Lp (EuclideanSpace ℂ (Fin (r * s))) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin (r * t))) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) :=
  let I := sobolevCoordinateIsometry (productCoordinateSwap n m).symm
    (tensorCoordinateSwap r s) 1
  let O := sobolevCoordinateIsometry (productCoordinateSwap n m)
    (tensorCoordinateSwap r t).symm 0
  O.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((productCutoffSobolevOperator α hα hαK χ hχ hχK ε hε).comp
      I.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The transported Bessel operator realizes the actual right-cutoff Fourier quantizer. -/
theorem rightProductCutoffSobolevOperator_apply
    (α : SymbolFunction m (s * r) (t * r)) (hα : IsSymbol Set.univ 1 α)
    (hαK : HasCompactSupport α) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ) (ε : ℝ) (hε : 0 < ε)
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s))))
    (z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * t))))
    (hz : ∀ x, quantize (rightProductCutoffSymbol α χ ε) w x = z x) :
    rightProductCutoffSobolevOperator α hα hαK χ hχ hχK ε hε
      (schwartzSobolevCoordinate 1 w) = schwartzSobolevCoordinate 0 z := by
  let e := productCoordinateSwap n m
  let i := tensorCoordinateSwap r s
  let o := (tensorCoordinateSwap r t).symm
  let w' := schwartzCoordinateEquiv e.symm i w
  let z' := schwartzCoordinateEquiv e.symm o.symm z
  have hw : schwartzCoordinateEquiv e i.symm w' = w := by
    apply SchwartzMap.ext
    intro x
    change i.symm (i (w (e.symm (e x)))) = w x
    rw [e.symm_apply_apply, i.symm_apply_apply]
  have hz' : schwartzCoordinateEquiv e o z' = z := by
    apply SchwartzMap.ext
    intro x
    change o (o.symm (z (e.symm (e x)))) = z x
    rw [e.symm_apply_apply, o.apply_symm_apply]
  -- The same symbol transport identifies the quantization before taking the completion.
  have hleft (x : EuclideanSpace ℝ (Fin (m + n))) :
      quantize (productCutoffSymbol α χ ε) w' x = z' x := by
    apply o.injective
    have h := quantize_isometricSymbolTransport e i o (productCutoffSymbol α χ ε) w'
      (e.symm x)
    rw [hw, e.apply_symm_apply] at h
    change quantize (rightProductCutoffSymbol α χ ε) w (e.symm x) =
      o (quantize (productCutoffSymbol α χ ε) w' x) at h
    rw [hz] at h
    change o (quantize (productCutoffSymbol α χ ε) w' x) = o (o.symm (z (e.symm x)))
    rw [o.apply_symm_apply]
    exact h.symm
  unfold rightProductCutoffSobolevOperator
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
  rw [sobolevCoordinateIsometry_apply,
    productCutoffSobolevOperator_apply α hα hαK χ hχ hχK ε hε w' z' hleft,
    sobolevCoordinateIsometry_apply, hz']


/-- Right-factor cutoffs converge in the original Bessel coordinates,
with the exact pure-tensor action. -/
theorem exists_rightTensorProductSobolev_approximation
    (a : SymbolFunction m s t) (α : SymbolFunction m (s * r) (t * r))
    (hα : IsSymbol Set.univ 1 α) (hαK : HasCompactSupport α)
    (hαeq : α = fun y η ↦ tensorIdentitySymbolMap s t r (a y η))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ L : Lp (EuclideanSpace ℂ (Fin (r * s))) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin (r * t))) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin s)))
        (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s)))),
        (∀ x y i j, w (EuclideanSpace.finAddEquivProd.symm (x, y))
          (finProdFinEquiv (i, j)) = u x i * v y j) →
          ∃ z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * t))),
            (∀ x y i j, z (EuclideanSpace.finAddEquivProd.symm (x, y))
              (finProdFinEquiv (i, j)) = (χ x : ℂ) * (u x i * quantize a v y j)) ∧
            L (schwartzSobolevCoordinate 1 w) = schwartzSobolevCoordinate 0 z) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
        ‖rightProductCutoffSobolevOperator α hα hαK χ hχ hχK ε hε - L‖ ≤ C * ε := by
  obtain ⟨L₀, hL₀, C₀, hC₀, hbound⟩ :=
    exists_tensorProductSobolev_approximation a α hα hαK hαeq χ hχ hχK
  let e := productCoordinateSwap n m
  let i := tensorCoordinateSwap r s
  let o := (tensorCoordinateSwap r t).symm
  let I := sobolevCoordinateIsometry e.symm i 1
  let O := sobolevCoordinateIsometry e o 0
  let I' := I.toContinuousLinearEquiv.toContinuousLinearMap
  let O' := O.toContinuousLinearEquiv.toContinuousLinearMap
  let L := O'.comp (L₀.comp I')
  refine ⟨L, ?_, ?_⟩
  · intro u v w hw
    let w' := schwartzCoordinateEquiv e.symm i w
    have hexy (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
        e (EuclideanSpace.finAddEquivProd.symm (x, y)) =
          EuclideanSpace.finAddEquivProd.symm (y, x) := productCoordinateSwap_apply n m x y
    -- The two distinct coordinate permutations send the same pure tensor to the reversed order.
    have hw' (y : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n))
        (j : Fin s) (i' : Fin r) :
        w' (EuclideanSpace.finAddEquivProd.symm (y, x)) (finProdFinEquiv (j, i')) =
          v y j * u x i' := by
      change i (w (e.symm (EuclideanSpace.finAddEquivProd.symm (y, x))))
        (finProdFinEquiv (j, i')) = _
      rw [tensorCoordinateSwap_apply, ← hexy x y, e.symm_apply_apply, hw]
      exact mul_comm _ _
    obtain ⟨z', hz', hL'⟩ := hL₀ v u w' hw'
    let z := schwartzCoordinateEquiv e o z'
    refine ⟨z, ?_, ?_⟩
    · have ho (v' : EuclideanSpace ℂ (Fin (t * r))) (i' : Fin r) (j : Fin t) :
          o v' (finProdFinEquiv (i', j)) = v' (finProdFinEquiv (j, i')) := by
        have h := tensorCoordinateSwap_apply r t (o v') i' j
        rw [(tensorCoordinateSwap r t).apply_symm_apply] at h
        exact h.symm
      intro x y i' j
      change o (z' (e (EuclideanSpace.finAddEquivProd.symm (x, y))))
        (finProdFinEquiv (i', j)) = _
      rw [ho, hexy, hz']
      ring
    · change O (L₀ (I (schwartzSobolevCoordinate 1 w))) = schwartzSobolevCoordinate 0 z
      rw [sobolevCoordinateIsometry_apply, hL', sobolevCoordinateIsometry_apply]
  · refine ⟨‖O'‖ * C₀ * ‖I'‖, mul_nonneg (mul_nonneg (norm_nonneg _) hC₀)
      (norm_nonneg _), ?_⟩
    intro ε hε hε₁
    -- Conjugating the very same local error retains its linear epsilon bound.
    have heq : rightProductCutoffSobolevOperator α hα hαK χ hχ hχK ε hε - L =
        O'.comp ((productCutoffSobolevOperator α hα hαK χ hχ hχK ε hε - L₀).comp I') := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      rfl
    rw [heq]
    calc
      _ ≤ ‖O'‖ * ‖(productCutoffSobolevOperator α hα hαK χ hχ hχK ε hε - L₀).comp I'‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖O'‖ * (‖productCutoffSobolevOperator α hα hαK χ hχ hχK ε hε - L₀‖ * ‖I'‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ ‖O'‖ * (C₀ * ε * ‖I'‖) := by gcongr; exact hbound ε hε hε₁
      _ = (‖O'‖ * C₀ * ‖I'‖) * ε := by ring

end AtiyahSinger
