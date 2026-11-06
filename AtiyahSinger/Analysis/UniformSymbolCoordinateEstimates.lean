/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolCoordinateEstimates

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform symbol bounds for coordinate families

Public module ID: M1044.

A fixed symbol retains its order under a family of smooth base substitutions
and invertible linear frequency substitutions with uniform normalized jet bounds.
No differentiability, topology, or measurable structure on the parameter is needed.
Compact geometric parameter sets supply these quantitative bounds after proving
joint continuity of the spatial jets and the inverse frequency matrices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff

set_option maxSynthPendingDepth 20 in
/-- Uniform normalized coordinate jets preserve the original symbol order under substitution. -/
theorem exists_uniform_bound_symbol_comp_linear_frequency
    {T : Type*} {Z X V : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : X → X → V) (hp : ContDiff ℝ ∞ (Function.uncurry p))
    (φ : T → Z → X) (hφ : ∀ t, ContDiff ℝ ∞ (φ t))
    (Θ : T → Z → X →L[ℝ] X) (hΘ : ∀ t, ContDiff ℝ ∞ (Θ t))
    (m : ℝ) (K : Set Z)
    (hgbound : ∀ a : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t,
      ∀ w ∈ K ×ˢ Metric.closedBall (0 : X) 1,
        ‖iteratedFDeriv ℝ a (fun z : Z × X ↦ (φ t z.1, Θ t z.1 z.2)) w‖ ≤ D)
    (hpbound : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t z, z ∈ K → ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (p x) ξ) (φ t z)‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (j : ℝ)))
    (B : ℝ) (hB : 1 ≤ B)
    (hupper : ∀ t z, z ∈ K → ∀ ξ, ‖Θ t z ξ‖ ≤ B * ‖ξ‖)
    (hlower : ∀ t z, z ∈ K → ∀ ξ, ‖ξ‖ ≤ B * ‖Θ t z ξ‖) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t z, z ∈ K → ∀ ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ t w) (Θ t w η)) ξ) z‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  -- Frequency dilation extracts exactly the order lost by every frequency derivative.
  have mixed_iteratedFDeriv_frequency_smul
      {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (R : ℝ) (hR : R ≠ 0) (i j : ℕ) (x : X) (y : Y) :
      iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ f z (R • η)) y) x =
        R ^ j • iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) (R • y)) x := by
    let e : Y ≃L[ℝ] Y := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR)
    have hfreq (z : X) : iteratedFDeriv ℝ j (fun η ↦ f z (R • η)) y =
        R ^ j • iteratedFDeriv ℝ j (f z) (R • y) := by
      have h := e.iteratedFDerivWithin_comp_right (f z) uniqueDiffOn_univ
        (x := y) (Set.mem_univ _) j
      simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
      change iteratedFDeriv ℝ j (f z ∘ e) y = _
      rw [h]
      ext v
      change (iteratedFDeriv ℝ j (f z) (R • y)) (fun a ↦ R • v a) = _
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp
    simp_rw [hfreq]
    let J : (Y [×j]→L[ℝ] V) ≃L[ℝ] (Y [×j]→L[ℝ] V) :=
      ContinuousLinearEquiv.smulLeft (Units.mk0 (R ^ j) (pow_ne_zero _ hR))
    exact J.iteratedFDeriv_comp_left
  have rpow_le_mul_rpow_of_comparable
      (a b B s : ℝ) (ha : 0 < a) (hb : 0 < b) (hB : 0 < B)
      (hab : a ≤ B * b) (hba : b ≤ B * a) :
      a ^ s ≤ B ^ |s| * b ^ s := by
    by_cases hs : 0 ≤ s
    · rw [abs_of_nonneg hs, ← Real.mul_rpow hB.le hb.le]
      exact Real.rpow_le_rpow ha.le hab hs
    · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
      have hcomp : (B * a) ^ s ≤ b ^ s :=
        Real.rpow_le_rpow_of_nonpos hb hba hs'
      calc
        a ^ s = B ^ |s| * (B * a) ^ s := by
          rw [Real.mul_rpow hB.le ha.le, abs_of_nonpos hs', ← mul_assoc,
            ← Real.rpow_add hB, neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ B ^ |s| * b ^ s := mul_le_mul_of_nonneg_left hcomp (by positivity)
  classical
  let k := i + j
  let g (t : T) : Z × X → X × X := fun z ↦ (φ t z.1, Θ t z.1 z.2)
  have hg (t : T) : ContDiff ℝ ∞ (g t) :=
    ((hφ t).comp contDiff_fst).prodMk (((hΘ t).comp contDiff_fst).clm_apply contDiff_snd)
  choose D hD hgD using hgbound
  choose C hC hpC using hpbound
  let D' := 1 + ∑ a ∈ Finset.range (k + 1), D a
  have hD' : 1 ≤ D' :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun a _ ↦ hD a))
  have hDD' (a : ℕ) (ha : a ≤ k) : D a ≤ D' := by
    apply le_trans (Finset.single_le_sum (fun b _ ↦ hD b)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ha)))
    exact le_add_of_nonneg_left zero_le_one
  let A := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
    C a b * B ^ |m - (b : ℝ)|
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg
      (fun b _ ↦ mul_nonneg (hC a b) (Real.rpow_nonneg (zero_le_one.trans hB) _)))
  have hCA (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
      C a b * B ^ |m - (b : ℝ)| ≤ A := by
    have hn (a b : ℕ) : 0 ≤ C a b * B ^ |m - (b : ℝ)| :=
      mul_nonneg (hC a b) (Real.rpow_nonneg (zero_le_one.trans hB) _)
    exact (Finset.single_le_sum (fun b _ ↦ hn a b)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))).trans
      (Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ hn a b))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ha)))
  let C' : ℝ := k.factorial * (2 ^ k * A) * D' ^ k
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  intro t z hz ξ
  let R : ℝ := 1 + ‖ξ‖
  have hR : 0 < R := by dsimp [R]; positivity
  let η : X := R⁻¹ • ξ
  have hη : ‖η‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    apply (inv_mul_le_iff₀ hR).mpr
    dsimp [R]
    linarith
  have hRη : R • η = ξ := smul_inv_smul₀ hR.ne' ξ
  let pR : X → X → V := fun x y ↦ p x (R • y)
  have hpR : ContDiff ℝ ∞ (Function.uncurry pR) :=
    hp.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))
  have hscaled (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
      ‖iteratedFDeriv ℝ a
        (fun x ↦ iteratedFDeriv ℝ b (pR x) (Θ t z η)) (φ t z)‖ ≤ A * R ^ m := by
    -- Each frequency derivative contributes R, while the symbol order loses the same power.
    rw [mixed_iteratedFDeriv_frequency_smul p R hR.ne' a b,
      norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR b)]
    have hfreq : R • Θ t z η = Θ t z ξ := by rw [← map_smul, hRη]
    rw [hfreq]
    have hweight : (1 + ‖Θ t z ξ‖) ^ (m - (b : ℝ)) ≤
        B ^ |m - (b : ℝ)| * R ^ (m - (b : ℝ)) := by
      apply rpow_le_mul_rpow_of_comparable _ _ _ _ (by positivity) hR
        (zero_lt_one.trans_le hB)
      · dsimp [R]
        nlinarith [hupper t z hz ξ]
      · dsimp [R]
        nlinarith [hlower t z hz ξ]
    calc
      _ ≤ R ^ b * (C a b * (B ^ |m - (b : ℝ)| * R ^ (m - (b : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left ((hpC a b t z hz (Θ t z ξ)).trans
          (mul_le_mul_of_nonneg_left hweight (hC a b))) (pow_nonneg hR.le _)
      _ = (C a b * B ^ |m - (b : ℝ)|) * R ^ m := by
        have hpow : R ^ b * R ^ (m - (b : ℝ)) = R ^ m := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (C a b * B ^ |m - (b : ℝ)|) *
              (R ^ b * R ^ (m - (b : ℝ))) := by ring
          _ = _ := by rw [hpow]
      _ ≤ A * R ^ m := mul_le_mul_of_nonneg_right (hCA a b ha hb) (by positivity)
  have houter (a : ℕ) (ha : a ≤ k) :
      ‖iteratedFDeriv ℝ a (Function.uncurry pR) (g t (z, η))‖ ≤
        (2 ^ k * A) * R ^ m := by
    have h := norm_iteratedFDeriv_uncurry_le_of_mixed pR hpR a (φ t z) (Θ t z η)
      (A * R ^ m) (mul_nonneg hA (by positivity))
      (fun b hb c hc ↦ hscaled b c (hb.trans ha) (hc.trans ha))
    apply h.trans
    calc
      2 ^ a * (A * R ^ m) ≤ 2 ^ k * (A * R ^ m) := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ha)
          (mul_nonneg hA (by positivity))
      _ = _ := by ring
  have hinner (a : ℕ) (ha : 1 ≤ a) (hak : a ≤ k) :
      ‖iteratedFDeriv ℝ a (g t) (z, η)‖ ≤ D' ^ a := by
    exact (hgD a t (z, η) ⟨hz, by simpa using hη⟩).trans
      ((hDD' a hak).trans (le_self_pow₀ hD' (by omega)))
  have hchain := norm_iteratedFDeriv_comp_le hpR (hg t) (n := k) (by simp) (z, η)
    houter hinner
  let q : Z → X → V := fun w ζ ↦ p (φ t w) (Θ t w ζ)
  have hq : ContDiff ℝ ∞ (Function.uncurry q) := hp.comp (hg t)
  have heq : Function.uncurry (fun w ζ ↦ q w (R • ζ)) = Function.uncurry pR ∘ g t := by
    ext w
    simp [q, pR, g, Function.uncurry, map_smul]
  have hfull : ‖iteratedFDeriv ℝ k
      (Function.uncurry (fun w ζ ↦ q w (R • ζ))) (z, η)‖ ≤ C' * R ^ m := by
    rw [heq]
    convert hchain using 1
    dsimp [C']
    ring
  have hmixed := norm_mixed_iteratedFDeriv_le (fun w ζ ↦ q w (R • ζ))
    (hq.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))) i j z η
  have hfinal := hmixed.trans hfull
  rw [mixed_iteratedFDeriv_frequency_smul q R hR.ne' i j,
    norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR j), hRη] at hfinal
  have hdivide : ‖iteratedFDeriv ℝ i
      (fun w ↦ iteratedFDeriv ℝ j (q w) ξ) z‖ ≤ (C' * R ^ m) / R ^ j :=
    (le_div_iff₀ (pow_pos hR j)).mpr (by simpa only [mul_comm] using hfinal)
  have hpower : (C' * R ^ m) / R ^ j = C' * R ^ (m - (j : ℝ)) := by
    rw [Real.rpow_sub hR, Real.rpow_natCast, mul_div_assoc]
  exact hdivide.trans_eq hpower

end AtiyahSinger
