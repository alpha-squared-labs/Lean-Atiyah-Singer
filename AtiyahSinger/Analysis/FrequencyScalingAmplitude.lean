/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude
public import AtiyahSinger.Analysis.FrequencyScaling

import all AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Uniform positive frequency scaling of the original amplitudes

Public module ID: M2296.

The original amplitude retains both spatial variables, every fixed coefficient and its
compact spatial control. Positive frequency contractions preserve its order-zero estimates.
One extra frequency derivative gives a uniform factor of the parameter in the weaker
order-zero weights. A fixed linear change of frequency commutes with this contraction, so
these estimates apply after the original coordinate, Jacobian and frame transformations.

Sources: SG III.3, (3.4)--(3.6), for the amplitude model; Taylor,
Pseudodifferential Operators, II.7, p. 53, for the bounded scaled-symbol family.
The explicit common extra-derivative estimate is a project supplement. It asserts
no operator-norm convergence at the zero parameter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

variable {n r q : ℕ}

/-- Positive frequency scaling retains both original spatial variables of the amplitude. -/
def frequencyScaleAmplitude (t : ℝ) (a : AmplitudeFunction n r q) :
    AmplitudeFunction n r q :=
  fun x y ξ ↦ a x y (t • ξ)

/-- The exact mixed chain rule retains the original order of the three derivatives. -/
private theorem amplitudeDerivative_frequencyScale (a : AmplitudeFunction n r q)
    (t : ℝ) (ht : t ≠ 0) (i j k : ℕ) (x y ξ : EuclideanSpace ℝ (Fin n)) :
    amplitudeDerivative (frequencyScaleAmplitude t a) i j k x y ξ =
      t ^ k • amplitudeDerivative a i j k x y (t • ξ) := by
  /- First apply the existing frequency chain rule together with the y derivatives.
  The remaining x derivative commutes with the same fixed scalar map. -/
  unfold amplitudeDerivative frequencyScaleAmplitude
  have hfreq (z : EuclideanSpace ℝ (Fin n)) :=
    mixed_iteratedFDeriv_frequency_smul (a z) t ht j k y ξ
  simp_rw [hfreq]
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := X [×j]→L[ℝ] (X [×k]→L[ℝ] H)
  let L : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 (t ^ k) (pow_ne_zero k ht))
  exact L.iteratedFDeriv_comp_left

-- The three nested derivative norms use the original amplitude inference depth.
set_option maxSynthPendingDepth 15 in
/-- Positive frequency contractions preserve order-zero amplitude estimates uniformly. -/
theorem IsAmplitude.frequencyScale {a : AmplitudeFunction n r q} (ha : IsAmplitude 0 a)
    (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) : IsAmplitude 0 (frequencyScaleAmplitude t a) := by
  /- The contraction is smooth on the same spatial-pair domain. The exact mixed
  chain rule extracts t^k, and the positive frequency weights absorb all k factors. -/
  refine ⟨ha.1.comp (contDiff_fst.prodMk (contDiff_snd.const_smul t)), ?_⟩
  intro K hK i j k
  obtain ⟨C, hC, hbound⟩ := ha.2 K hK i j k
  refine ⟨C, hC, ?_⟩
  intro x y hxy ξ
  have hratio : t ^ k / (1 + t * ‖ξ‖) ^ k ≤ 1 / (1 + ‖ξ‖) ^ k := by
    apply (div_le_div_iff₀ (pow_pos (by positivity) k) (pow_pos (by positivity) k)).mpr
    have hcomparison := pow_le_pow_left₀
      (show 0 ≤ t * (1 + ‖ξ‖) by positivity)
      (show t * (1 + ‖ξ‖) ≤ 1 + t * ‖ξ‖ by nlinarith) k
    simpa only [mul_pow, one_mul] using hcomparison
  have hscaled : ‖amplitudeDerivative a i j k x y (t • ξ)‖ ≤
      C * (1 + ‖t • ξ‖) ^ (-(k : ℝ)) := by
    simpa only [zero_sub] using hbound x y hxy (t • ξ)
  calc
    ‖amplitudeDerivative (frequencyScaleAmplitude t a) i j k x y ξ‖ =
        t ^ k * ‖amplitudeDerivative a i j k x y (t • ξ)‖ := by
      rw [amplitudeDerivative_frequencyScale a t ht.ne' i j k x y ξ, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le k)]
    _ ≤ t ^ k * (C * (1 + ‖t • ξ‖) ^ (-(k : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (pow_nonneg ht.le k)
    _ = C * (t ^ k / (1 + t * ‖ξ‖) ^ k) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    _ ≤ C * (1 / (1 + ‖ξ‖) ^ k) := mul_le_mul_of_nonneg_left hratio hC
    _ = C * (1 + ‖ξ‖) ^ (0 - (k : ℝ)) := by
      rw [zero_sub, Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring

-- The three nested derivative norms use the original amplitude inference depth.
set_option maxSynthPendingDepth 15 in
/-- An extra frequency derivative gives a uniform factor of the positive scale parameter. -/
theorem IsAmplitude.exists_frequencyScale_derivative_bound {a : AmplitudeFunction n r q}
    (ha : IsAmplitude 0 a) (K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (i j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖amplitudeDerivative (frequencyScaleAmplitude t a) i j (k + 1) x y ξ‖ ≤
        C * t * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- Choose the original compact-local mixed-jet bound before the parameter. Keep
  one of the k+1 chain-rule factors of t and absorb only the other k in the weights. -/
  obtain ⟨C, hC, hbound⟩ := ha.2 K hK i j (k + 1)
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x y hxy ξ
  have hratio : t ^ (k + 1) / (1 + t * ‖ξ‖) ^ (k + 1) ≤
      t / (1 + ‖ξ‖) ^ k := by
    apply (div_le_div_iff₀ (pow_pos (by positivity) (k + 1))
      (pow_pos (by positivity) k)).mpr
    have hcomparison : t ^ k * (1 + ‖ξ‖) ^ k ≤ (1 + t * ‖ξ‖) ^ k := by
      simpa only [mul_pow] using pow_le_pow_left₀
        (show 0 ≤ t * (1 + ‖ξ‖) by positivity)
        (show t * (1 + ‖ξ‖) ≤ 1 + t * ‖ξ‖ by nlinarith) k
    calc
      t ^ (k + 1) * (1 + ‖ξ‖) ^ k = t * (t ^ k * (1 + ‖ξ‖) ^ k) := by
        rw [pow_succ]
        ring
      _ ≤ t * (1 + t * ‖ξ‖) ^ k := mul_le_mul_of_nonneg_left hcomparison ht.le
      _ ≤ t * (1 + t * ‖ξ‖) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) (Nat.le_succ k)) ht.le
  have hscaled : ‖amplitudeDerivative a i j (k + 1) x y (t • ξ)‖ ≤
      C * (1 + ‖t • ξ‖) ^ (-((k + 1 : ℕ) : ℝ)) := by
    simpa only [zero_sub] using hbound x y hxy (t • ξ)
  calc
    ‖amplitudeDerivative (frequencyScaleAmplitude t a) i j (k + 1) x y ξ‖ =
        t ^ (k + 1) * ‖amplitudeDerivative a i j (k + 1) x y (t • ξ)‖ := by
      rw [amplitudeDerivative_frequencyScale a t ht.ne' i j (k + 1) x y ξ, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le (k + 1))]
    _ ≤ t ^ (k + 1) * (C * (1 + ‖t • ξ‖) ^ (-((k + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (pow_nonneg ht.le (k + 1))
    _ = C * (t ^ (k + 1) / (1 + t * ‖ξ‖) ^ (k + 1)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    _ ≤ C * (t / (1 + ‖ξ‖) ^ k) := mul_le_mul_of_nonneg_left hratio hC
    _ = C * t * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring

end AtiyahSinger
