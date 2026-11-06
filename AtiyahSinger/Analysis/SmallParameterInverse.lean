/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Invertibility from two small composition errors

Public module ID: M2286.

The Banach-space Neumann criterion applies separately to the two actual products.
An invertible left product makes the original map injective, and an invertible
right product makes it surjective. This gives an actual continuous inverse.
Uniform errors bounded by `C * t` therefore supply a zero-index sample at a
strictly positive parameter. No continuity or value at parameter zero is used.

Sources: the standard Neumann-series criterion, as implemented in mathlib's
`Mathlib.Analysis.SpecificLimits.Normed`, and the bijective-index normalization in
`Mathlib.Algebra.Module.LinearMap.Index`. Quantitative estimates for a particular
quantizer are separate mathematical inputs to the second theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Two composition errors of norm less than one give an actual continuous inverse. -/
theorem isInvertible_of_comp_sub_id_norm_lt (P : E →L[𝕜] F) (Q : F →L[𝕜] E)
    (hleft : ‖Q.comp P - ContinuousLinearMap.id 𝕜 E‖ < 1)
    (hright : ‖P.comp Q - ContinuousLinearMap.id 𝕜 F‖ < 1) :
    P.IsInvertible := by
  -- Apply the Neumann series to each genuine endomorphism product.
  have hQP : IsUnit (Q.comp P) := by
    have hnorm : ‖(1 : E →L[𝕜] E) - Q.comp P‖ < 1 := by
      rw [norm_sub_rev]
      exact hleft
    simpa only [sub_sub_cancel] using IsUnit.one_sub_of_norm_lt_one hnorm
  have hPQ : IsUnit (P.comp Q) := by
    have hnorm : ‖(1 : F →L[𝕜] F) - P.comp Q‖ < 1 := by
      rw [norm_sub_rev]
      exact hright
    simpa only [sub_sub_cancel] using IsUnit.one_sub_of_norm_lt_one hnorm
  have hQP_bijective := ContinuousLinearMap.isUnit_iff_bijective.mp hQP
  have hPQ_bijective := ContinuousLinearMap.isUnit_iff_bijective.mp hPQ
  -- The same map P is injective from QP and surjective from PQ.
  have hP_injective : Function.Injective P := by
    intro x y hxy
    apply hQP_bijective.1
    change Q (P x) = Q (P y)
    rw [hxy]
  have hP_surjective : Function.Surjective P := by
    intro y
    obtain ⟨x, hx⟩ := hPQ_bijective.2 y
    exact ⟨Q x, hx⟩
  -- The Banach inverse theorem packages that bijection as a continuous equivalence.
  exact ⟨ContinuousLinearEquiv.ofBijective P (LinearMap.ker_eq_bot.mpr hP_injective)
    (LinearMap.range_eq_top.mpr hP_surjective),
    ContinuousLinearEquiv.coe_ofBijective P _ _⟩

/-- Uniform linear error bounds supply a zero-index sample at a positive parameter. -/
theorem exists_pos_index_eq_zero_of_comp_error_bound
    (P : ℝ → E →L[𝕜] F) (Q : ℝ → F →L[𝕜] E) (C : ℝ) (hC : 0 ≤ C)
    (hleft : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖(Q t).comp (P t) - ContinuousLinearMap.id 𝕜 E‖ ≤ C * t)
    (hright : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖(P t).comp (Q t) - ContinuousLinearMap.id 𝕜 F‖ ≤ C * t) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ (P t).toLinearMap.index = 0 := by
  -- Choose a positive parameter whose common error bound is strictly below one.
  let t : ℝ := 1 / (2 * (C + 1))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht_one : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hsmall : C * t < 1 := by
    dsimp [t]
    rw [mul_one_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  -- Both actual products are invertible, so this particular P t is a bijection.
  have hPt := isInvertible_of_comp_sub_id_norm_lt (P t) (Q t)
    ((hleft t ht ht_one).trans_lt hsmall) ((hright t ht ht_one).trans_lt hsmall)
  refine ⟨t, ht, ht_one, ?_⟩
  exact LinearMap.index_of_bijective hPt.bijective

end AtiyahSinger
