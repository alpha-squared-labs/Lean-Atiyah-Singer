/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasTensorCoefficientPiece
public import AtiyahSinger.Analysis.ProductSchwartzSlice

/-!
# The exact columns of an unregularized tensor lift

Public module ID: M0883.

Finite coefficient amplification commutes with the original lifted Fourier
action on every joint Schwartz input. The statement uses the specified
base-first tensor index and the actual unamplified column, without imposing joint
symbol estimates on the unregularized lift.

The proof slices in the second-factor variable and uses the already established full
base-symbol coefficient amplification. This is the coordinate comparison
needed to identify a controlled associated horizontal limit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 20 in
/-- Each amplified tensor column has the original unamplified lifted Fourier action. -/
theorem quantize_liftedProductSymbol_tensorIdentity_column
    {n m r q k : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (ρ : EuclideanSpace ℝ (Fin m) → ℝ)
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * k))))
    (j : Fin k)
    (f : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
    (hf : ∀ z i, f z i = w z (finProdFinEquiv (i, j)))
    (z : EuclideanSpace ℝ (Fin (n + m))) (i : Fin q) :
    quantize (liftedProductSymbol
      (fun x ξ ↦ tensorIdentitySymbolMap r q k (a x ξ)) ρ) w z
        (finProdFinEquiv (i, j)) = quantize (liftedProductSymbol a ρ) f z i := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℂ (Fin (r * k))
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let α : SymbolFunction n (r * k) (q * k) :=
    fun x ξ ↦ tensorIdentitySymbolMap r q k (a x ξ)
  have hα : IsSymbol Set.univ 1 α :=
    isSymbol_continuousLinearMap 1 a ha ((tensorIdentitySymbolMap r q k).restrictScalars ℝ)
  have hαK : HasCompactSupport α := by
    apply haK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport a)
    intro x hx
    by_contra hout
    apply hx
    funext ξ
    change tensorIdentitySymbolMap r q k (a x ξ) = 0
    rw [image_eq_zero_of_notMem_tsupport hout]
    exact (tensorIdentitySymbolMap r q k).map_zero
  -- Use the same complete base-symbol quantizer and its prescribed original columns.
  obtain ⟨Q, hQ, hcolumns⟩ := exists_schwartz_tensorCoefficient k 1 a ha
    (quantizeSchwartz 1 a ha haK) (quantizeSchwartz_apply 1 a ha haK)
  obtain ⟨D, hD, hcolumn⟩ := hcolumns j
  let y : Y := (e z).2
  have hg : (fun x : X ↦ (x, y)).HasTemperateGrowth := by
    convert (ContinuousLinearMap.inl ℝ X Y).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : X), y)) using 1
    funext x
    simp
  let v : 𝓢(X, V) := SchwartzMap.compCLM ℂ hg
    ⟨1, 1, fun x ↦ by
      simpa only [one_mul, pow_one] using
        (norm_fst_le (x, y)).trans (le_add_of_nonneg_left zero_le_one)⟩
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm w)
  have hv (x : X) : v x = w (e.symm (x, y)) := rfl
  have hfSlice (x : X) : D v x = f (e.symm (x, y)) := by
    apply PiLp.ext
    intro l
    rw [hD, hv, hf]
  -- Both lifted Fourier integrals reduce to this identical affine input slice.
  have hfull := quantize_liftedProductSymbol_eq_slice α hα hαK ρ w y v hv
  have hscalar := quantize_liftedProductSymbol_eq_slice a ha haK ρ f y (D v) hfSlice
  have hz : e.symm ((e z).1, y) = z := e.symm_apply_apply z
  rw [← hz]
  rw [hfull, hscalar]
  change (ρ y : ℂ) * quantize α v (e z).1 (finProdFinEquiv (i, j)) =
    (ρ y : ℂ) * quantize a (D v) (e z).1 i
  rw [← hQ, hcolumn, quantizeSchwartz_apply]

end AtiyahSinger
