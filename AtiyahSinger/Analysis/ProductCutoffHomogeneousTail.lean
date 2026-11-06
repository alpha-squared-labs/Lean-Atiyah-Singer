/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductSymbolCutoff

/-!
# The product-frequency cutoff preserves homogeneous tails

Public module ID: M0876.

Outside one radius the radial profile is one and only the angular profile
remains. A nonzero angular profile forces the retained frequency beyond the
original tail radius. The same statement at both ends of a positive dilation
therefore proves exact degree-one homogeneity of the actual cutoff symbol.

The radius is independent of the base parameter and of the symbol values.
This is used for the original finitely many associated chart pieces, before
the original cotangent coordinate and frame transports are composed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

variable {X Y α : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
  {W : α → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]

set_option maxHeartbeats 800000 in
-- The common radius must control the radial profile and both retained-frequency tails.
/-- The same product cutoff is degree one at infinity when its retained factor has that tail. -/
theorem exists_productFrequencyCutoff_homogeneous_of_tail
    (ε R₀ : ℝ) (hε : 0 < ε) (a : ∀ x : α, X → W x)
    (hscale : ∀ (x : α) (ξ : X) (t : ℝ), 0 < t →
      R₀ ≤ ‖ξ‖ → R₀ ≤ ‖t • ξ‖ → a x (t • ξ) = (t : ℂ) • a x ξ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : α) (ξ : X) (η : Y) (t : ℝ), 0 < t →
      R ≤ ‖ξ‖ + ‖η‖ → R ≤ ‖t • ξ‖ + ‖t • η‖ →
      (productFrequencyCutoff ε ‖t • ξ‖ ‖t • η‖ : ℂ) • a x (t • ξ) =
        (t : ℂ) • ((productFrequencyCutoff ε ‖ξ‖ ‖η‖ : ℂ) • a x ξ) := by
  let M := max R₀ 1
  let R := 4 / ε + (1 + 2 / ε) * M
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have hcoeff : 0 < 1 + 2 / ε := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hone (s : ℝ) (hs : 2 ≤ s) : productCutoffProfile s = 1 := by
    let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    change 1 - φ s = 1
    rw [φ.zero_of_le_dist (by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : 0 ≤ s), φ]
        using hs), sub_zero]
  -- The two lower radius bounds ensure that both exact radial profiles are one.
  have hradial (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hlarge : R ≤ r + s) :
      productCutoffProfile (ε * Real.sqrt (r ^ 2 + s ^ 2)) = 1 := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ r ^ 2 + s ^ 2 by positivity)
    have hsqrtnonneg := Real.sqrt_nonneg (r ^ 2 + s ^ 2)
    have hsum : r + s ≤ 2 * Real.sqrt (r ^ 2 + s ^ 2) := by
      nlinarith [sq_nonneg (r - s)]
    have hfour : 4 / ε ≤ r + s := by
      dsimp only [R] at hlarge
      linarith [mul_pos hcoeff hM]
    apply hone
    have hmul : 4 ≤ (r + s) * ε := (div_le_iff₀ hε).mp hfour
    nlinarith
  have htail (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hlarge : R ≤ r + s)
      (hcut : productFrequencyCutoff ε r s ≠ 0) : R₀ ≤ r := by
    have hrad := hradial r s hr hs hlarge
    have hrne : r ≠ 0 := by
      intro hz
      apply hcut
      dsimp only [productFrequencyCutoff]
      rw [hrad, ite_eq_left hz, mul_one, sub_self]
    have hratio : ε * s / r < 2 := by
      by_contra! hh
      apply hcut
      dsimp only [productFrequencyCutoff]
      rw [hrad, ite_eq_right hrne, hone _ hh, mul_one, sub_self]
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrne)
    have hcone : s < (2 / ε) * r := by
      have h := (div_lt_iff₀ hrpos).mp hratio
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hε).mpr
      nlinarith
    have hbound : (1 + 2 / ε) * R₀ ≤ (1 + 2 / ε) * r := by
      have hR₀M : R₀ ≤ M := le_max_left _ _
      have hfour : 0 < 4 / ε := by positivity
      have hR₀ := mul_le_mul_of_nonneg_left hR₀M hcoeff.le
      dsimp only [R] at hlarge
      nlinarith
    exact le_of_mul_le_mul_left hbound hcoeff
  refine ⟨R, hR, ?_⟩
  intro x ξ η t ht hlarge hlarge'
  have hnormξ : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hnormη : ‖t • η‖ = t * ‖η‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hcut : productFrequencyCutoff ε ‖t • ξ‖ ‖t • η‖ =
      productFrequencyCutoff ε ‖ξ‖ ‖η‖ := by
    have hrad := hradial ‖ξ‖ ‖η‖ (norm_nonneg _) (norm_nonneg _) hlarge
    have hrad' := hradial ‖t • ξ‖ ‖t • η‖ (norm_nonneg _) (norm_nonneg _) hlarge'
    dsimp only [productFrequencyCutoff]
    rw [hrad', hrad]
    simp only [one_mul, hnormξ, hnormη]
    by_cases hz : ‖ξ‖ = 0
    · simp only [hz, mul_zero, ite_eq_left]
    · rw [ite_eq_right hz, ite_eq_right (mul_ne_zero ht.ne' hz)]
      congr 2
      field_simp
  by_cases hzero : productFrequencyCutoff ε ‖ξ‖ ‖η‖ = 0
  · simp only [hcut, hzero, Complex.ofReal_zero, zero_smul, smul_zero]
  · have hfirst := htail ‖ξ‖ ‖η‖ (norm_nonneg _) (norm_nonneg _) hlarge hzero
    have hsecond := htail ‖t • ξ‖ ‖t • η‖ (norm_nonneg _) (norm_nonneg _) hlarge'
      (hcut ▸ hzero)
    rw [hscale x ξ t ht hfirst hsecond, hcut, smul_comm]

end AtiyahSinger
