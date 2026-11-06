/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Symbol
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform frequency variation of first-order symbols

Public module ID: M1022.

On each compact spatial subset, an actual symbol of order one has a uniform
Lipschitz bound in its frequency variable. The estimate applies directly to
the given full symbol; no homogeneous representative or exact recovery from
a principal representative is required.

This estimate controls the mixed cotangent shifts of associated product
charts by their original transverse frequency.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff

variable {n r q : ℕ}

/-- An order-one full symbol is uniformly Lipschitz in frequency over each compact set. -/
theorem IsSymbol.exists_frequency_lipschitz_bound
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))}
    (ha : IsSymbol U 1 a) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ∀ ξ η, ‖a x η - a x ξ‖ ≤ D * ‖η - ξ‖ := by
  -- One frequency derivative has order zero, giving the same bound at every frequency.
  obtain ⟨D, hD, hbound⟩ := ha.2 K hKU hK 0 1
  refine ⟨D, hD, ?_⟩
  intro x hx ξ η
  have hderiv (ζ : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ (a x) ζ‖ ≤ D := by
    simpa only [symbolDerivative, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one,
      Nat.cast_one, sub_self, Real.rpow_zero, mul_one] using hbound x hx ζ
  -- Restrict smoothness to the complete frequency fiber and apply the mean value estimate.
  have hsmooth : ContDiff ℝ ∞ (a x) := by
    apply contDiffOn_univ.mp
    have hs : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ) := ha.1
    exact hs.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun ζ _ ↦ ⟨hKU hx, mem_univ ζ⟩)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ)
    (fun ζ _ ↦ hsmooth.differentiable (by simp) ζ) (fun ζ _ ↦ hderiv ζ)
    convex_univ (mem_univ ξ) (mem_univ η)

end AtiyahSinger
