/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasTensorCoefficientPiece
public import AtiyahSinger.Analysis.ProductSchwartzSlice
public import AtiyahSinger.Analysis.RightProductCutoffRealization

/-!
# The full right-factor Fourier action on original tensor rows

Public module ID: M0931.

The original base-first tensor coordinates are retained when a complete second-factor
symbol acts on each fixed-base row. The two specified orthogonal permutations
reduce the Fourier integral to the exact original second-factor quantizer. This applies
to arbitrary Schwartz input, with no separated-tensor or joint-symbol hypothesis.
It identifies the unregularized vertical limit used by the controlled cutoff.

Source: Fourier inversion in the original SG normalization, III.13.5--13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 20 in
/-- The unregularized right lift acts by the original full quantizer on every base-first row. -/
theorem quantize_rightProductLift_eq_slice
    {n m r s t : ℕ} (a : SymbolFunction m s t)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s))))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin r)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin s)))
    (hf : ∀ y j, f y j = w (EuclideanSpace.finAddEquivProd.symm (x, y))
      (finProdFinEquiv (i, j)))
    (y : EuclideanSpace ℝ (Fin m)) (j : Fin t) :
    quantize (isometricSymbolTransport (productCoordinateSwap n m) (tensorCoordinateSwap r s)
      (tensorCoordinateSwap r t).symm
      (liftedProductSymbol (fun z η ↦ tensorIdentitySymbolMap s t r (a z η)) ρ))
      w (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (i, j)) =
        (ρ x : ℂ) * quantize a f y j := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℂ (Fin (s * r))
  let e := productCoordinateSwap n m
  let h := tensorCoordinateSwap r s
  let o := (tensorCoordinateSwap r t).symm
  let w' := schwartzCoordinateEquiv e.symm h w
  let α : SymbolFunction m (s * r) (t * r) :=
    fun z η ↦ tensorIdentitySymbolMap s t r (a z η)
  have hα : IsSymbol Set.univ 1 α :=
    isSymbol_continuousLinearMap 1 a ha ((tensorIdentitySymbolMap s t r).restrictScalars ℝ)
  have hαK : HasCompactSupport α := by
    apply haK.of_isClosed_subset (isClosed_tsupport α)
    apply closure_minimal _ (isClosed_tsupport a)
    intro z hz
    by_contra hout
    apply hz
    funext η
    change tensorIdentitySymbolMap s t r (a z η) = 0
    rw [image_eq_zero_of_notMem_tsupport hout]
    exact (tensorIdentitySymbolMap s t r).map_zero
  -- Slice the full reversed tensor input at the same original base point.
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
  have hg : (fun z : Y ↦ (z, x)).HasTemperateGrowth := by
    convert (ContinuousLinearMap.inl ℝ Y X).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : Y), x)) using 1
    funext z
    simp
  let v : 𝓢(Y, V) := SchwartzMap.compCLM ℂ hg
    ⟨1, 1, fun z ↦ by
      simpa only [one_mul, pow_one] using
        (norm_fst_le (z, x)).trans (le_add_of_nonneg_left zero_le_one)⟩
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.symm w')
  have hv (z : Y) : v z = w' (c.symm (z, x)) := rfl
  obtain ⟨Q, hQ, hcolumns⟩ := exists_schwartz_tensorCoefficient r 1 a ha
    (quantizeSchwartz 1 a ha haK) (quantizeSchwartz_apply 1 a ha haK)
  obtain ⟨D, hD, hcolumn⟩ := hcolumns i
  have hDf : D v = f := by
    apply SchwartzMap.ext
    intro z
    apply PiLp.ext
    intro l
    rw [hD, hv, hf]
    change h (w (e.symm (c.symm (z, x)))) (finProdFinEquiv (l, i)) = _
    rw [tensorCoordinateSwap_apply]
    have he : e (EuclideanSpace.finAddEquivProd.symm (x, z)) = c.symm (z, x) :=
      productCoordinateSwap_apply n m x z
    rw [← he, e.symm_apply_apply]
  -- Use the same full Fourier transport and then the original complete second-factor quantizer.
  have hw : schwartzCoordinateEquiv e h.symm w' = w := by
    apply SchwartzMap.ext
    intro z
    change h.symm (h (w (e.symm (e z)))) = w z
    rw [e.symm_apply_apply, h.symm_apply_apply]
  have ho (u : EuclideanSpace ℂ (Fin (t * r))) :
      o u (finProdFinEquiv (i, j)) = u (finProdFinEquiv (j, i)) := by
    have h := tensorCoordinateSwap_apply r t (o u) i j
    rw [(tensorCoordinateSwap r t).apply_symm_apply] at h
    exact h.symm
  have htransport := quantize_isometricSymbolTransport e h o (liftedProductSymbol α ρ)
    w' (EuclideanSpace.finAddEquivProd.symm (x, y))
  rw [hw, productCoordinateSwap_apply] at htransport
  rw [htransport, ho, quantize_liftedProductSymbol_eq_slice α hα hαK ρ w' x v hv]
  change (ρ x : ℂ) * quantize α v y (finProdFinEquiv (j, i)) = _
  rw [← hQ, hcolumn, hDf, quantizeSchwartz_apply]

end AtiyahSinger
