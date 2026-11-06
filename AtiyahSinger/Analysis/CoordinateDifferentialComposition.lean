/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateDifferentialModulation
public import AtiyahSinger.Analysis.CoordinateDifferentialQuantization
public import AtiyahSinger.Analysis.DifferentialCompositionExpansion

/-!
# Exact finite composition with a second-order coordinate differential operator

Public module ID: M0405.

The differentiated Fourier integral and its exact modulation identity identify the
actual differential action with the first three standard symbol composition terms.
The result uses the original local symbol on its original open spatial domain.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open MeasureTheory
open scoped ContDiff SchwartzMap

/-- A second-order differential operator composed with local quantization has exactly
three standard composition terms. No asymptotic remainder is discarded. -/
theorem apply_quantize_eq_quantize_sum_order_two
    {n r s t : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n s t 2 U)
    (m : ℝ) (a : SymbolFunction n r s) (ha : IsSymbol U m a)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    P.apply (quantize a u) x =
      quantize (∑ j : Fin 3, compositionExpansionTerm P.totalSymbol a j.val) u x := by
  -- Pass the actual differential expression through the same normalized Fourier integral.
  rw [(integrable_apply_quantization_integrand_and_apply_quantize
    hU P m a ha u x hx).2]
  unfold quantize
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  -- Only local smoothness of the original symbol slice is used in the product rule.
  have hs : ContDiffOn ℝ ∞ (fun y ↦ a y ξ) U :=
    ha.1.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun y hy ↦ ⟨hy, Set.mem_univ _⟩)
  let ev : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)) →L[ℝ]
      EuclideanSpace ℂ (Fin s) :=
    (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin s)) (fourierSG u ξ)).restrictScalars ℝ
  have hv : ContDiffOn ℝ ∞ (fun y ↦ a y ξ (fourierSG u ξ)) U :=
    ev.contDiff.comp_contDiffOn hs
  rw [apply_cexp_smul_order_two hU P _ hv x hx ξ]
  -- The same ordered coefficients equal the standard j = 0, 1, 2 composition terms.
  exact congrArg (fun w ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • w)
    (compositionExpansion_sum_order_two hU P a x hx ξ hs (fourierSG u ξ)).symm

end AtiyahSinger.CoordinateDifferentialOperator
