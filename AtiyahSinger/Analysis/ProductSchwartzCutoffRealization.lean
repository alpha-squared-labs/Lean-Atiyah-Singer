/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductCutoffRealization

import all AtiyahSinger.Analysis.GeometricProductCutoffRealization

/-!
# Controlled cutoff realization on full Schwartz inputs

Public module ID: M0880.

The bounded lift in the original Bessel coordinates has its actual Fourier
action on every Schwartz input whose unregularized output is Schwartz. The
same positive product-frequency cutoffs converge to that lift in operator
norm. This specification permits comparison with the actual compact local
coordinates of a geometric horizontal operator, without requiring those
coordinates to be separated tensors.

Source: SG III.13.5, p.250. The original lift need not satisfy joint symbol
estimates; the existing compact cutoff and its actual bounded error supply
the realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

/-- The controlled product cutoffs realize the full original Fourier action on Schwartz data. -/
theorem exists_liftedProductSobolev_approximation_schwartz
    {n m r q : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ L : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
        (z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q))),
        (∀ x, quantize (liftedProductSymbol a χ) u x = z x) →
          L (schwartzSobolevCoordinate 1 u) = schwartzSobolevCoordinate 0 z) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
        ‖productCutoffSobolevOperator a ha haK χ hχ hχK ε hε - L‖ ≤ C * ε := by
  let L := productCutoffSobolevOperator a ha haK χ hχ hχK 1 zero_lt_one +
    productCutoffErrorOperator a ha haK χ hχ hχK 1
  -- One fixed cutoff plus its actual error recovers the full original Fourier integral.
  have hL (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
      (z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q)))
      (hz : ∀ x, quantize (liftedProductSymbol a χ) u x = z x) :
      L (schwartzSobolevCoordinate 1 u) = schwartzSobolevCoordinate 0 z := by
    dsimp only [L]
    rw [add_apply]
    rw [productCutoffSobolevOperator_eq_sub a ha haK χ hχ hχK 1 zero_lt_one u z hz]
    exact sub_add_cancel _ _
  obtain ⟨T, hT, C, hC, hbound⟩ :=
    exists_liftedProductSobolev_approximation a ha haK χ hχ hχK
  -- The established limit has the same separated action, so density identifies the operators.
  have hLT : L = T := by
    apply eq_of_schwartz_products_bessel
    intro u v w hw
    obtain ⟨z, hz, hzvalue⟩ :=
      exists_schwartz_liftedProductSymbol a ha haK χ hχ hχK u v w hw
    obtain ⟨t, htvalue, ht⟩ := hT u v w hw
    have htz : t = z := by
      apply SchwartzMap.ext
      intro x
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
      have hx := (htvalue (e x).1 (e x).2).trans (hzvalue (e x).1 (e x).2).symm
      change t (e.symm (e x)) = z (e.symm (e x)) at hx
      simpa only [e.symm_apply_apply] using hx
    rw [hL w z hz, ht, htz]
  refine ⟨L, hL, C, hC, ?_⟩
  intro ε hε hε1
  rw [hLT]
  exact hbound ε hε hε1

end AtiyahSinger
