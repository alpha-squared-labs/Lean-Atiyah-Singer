/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude

import AtiyahSinger.Analysis.SymbolCoordinateEstimates
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The symbol of a compact smooth kernel

Public module ID: M0353.

A compactly supported smooth Euclidean kernel has a concrete left symbol, given
by its partial Fourier transform with the Kohn–Nirenberg phase. This symbol has
every real order and quantizes to the original kernel integral, with precisely
the project's Fourier normalization. A compact frequency cutoff is used only
to invoke the already established exact amplitude reduction theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 20

set_option maxHeartbeats 1000000 in

private theorem compact_amplitude_isAmplitude {n r q : ℕ}
    (a : AmplitudeFunction n r q)
    (ha : ContDiff ℝ ∞ (fun z :
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) ↦
        a z.1.1 z.1.2 z.2))
    (hc : HasCompactSupport (fun z :
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) ↦
        a z.1.1 z.1.2 z.2))
    (m : ℝ) : IsAmplitude m a := by
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have parametric {P Y W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → Y → W) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : P × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y W).symm : _ →L[ℝ] Y [×0]→L[ℝ] W)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : P × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : P × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) W).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] W)
  refine ⟨ha, ?_⟩
  intro K _ i j k
  let F : (X × X) × X → H := fun z ↦ a z.1.1 z.1.2 z.2
  let D := iteratedFDeriv ℝ (i + j + k) F
  -- Full derivatives have compact support, so every frequency weight is bounded with them.
  have hD : Continuous D := ha.continuous_iteratedFDeriv (by simp)
  have hcD : HasCompactSupport D := hc.iteratedFDeriv _
  let w : (X × X) × X → ℝ := fun z ↦ (1 + ‖z.2‖) ^ ((k : ℝ) - m) * ‖D z‖
  have hw : Continuous w := by
    apply Continuous.mul _ hD.norm
    exact (continuous_const.add continuous_snd.norm).rpow_const
      (fun z ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + ‖z.2‖)))
  have hcw : HasCompactSupport w := hcD.norm.mul_left
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hcw
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x y _ ξ
  have hg : ContDiff ℝ ∞ (fun z : X × X ↦ iteratedFDeriv ℝ k (a z.1 z.2) ξ) :=
    (parametric (fun (z : X × X) η ↦ a z.1 z.2 η) ha k).comp
      (contDiff_id.prodMk contDiff_const)
  have hder₁ : ‖amplitudeDerivative a i j k x y ξ‖ ≤
      ‖iteratedFDeriv ℝ (i + j)
        (fun z : X × X ↦ iteratedFDeriv ℝ k (a z.1 z.2) ξ) (x, y)‖ :=
    norm_mixed_iteratedFDeriv_le (fun x y ↦ iteratedFDeriv ℝ k (a x y) ξ) hg i j x y
  have hder₂ : ‖iteratedFDeriv ℝ (i + j)
        (fun z : X × X ↦ iteratedFDeriv ℝ k (a z.1 z.2) ξ) (x, y)‖ ≤
      ‖D ((x, y), ξ)‖ :=
    norm_mixed_iteratedFDeriv_le (fun (z : X × X) η ↦ a z.1 z.2 η) ha
      (i + j) k (x, y) ξ
  have hb : w ((x, y), ξ) ≤ max C 0 :=
    (le_abs_self _).trans ((hC ((x, y), ξ)).trans (le_max_left _ _))
  have hpow : (1 + ‖ξ‖) ^ ((k : ℝ) - m) * (1 + ‖ξ‖) ^ (m - (k : ℝ)) = 1 := by
    rw [← Real.rpow_add (by positivity), sub_add_sub_cancel, sub_self, Real.rpow_zero]
  have hbound := mul_le_mul_of_nonneg_right hb
    (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖) (m - (k : ℝ)))
  dsimp [w] at hbound
  rw [mul_right_comm, hpow, one_mul] at hbound
  exact hder₁.trans (hder₂.trans hbound)

/-- The actual partial Fourier formula for the left symbol of a Euclidean kernel. -/
def compactKernelSymbol {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) : SymbolFunction n r q :=
  fun x ξ ↦ ∫ y, Complex.exp (-Complex.I * (inner ℝ (x - y) ξ : ℂ)) • k x y

private theorem compact_kernel_amplitude_spec {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hc : HasCompactSupport (Function.uncurry k)) :
    ∃ a : AmplitudeFunction n r q, (∀ m : ℝ, IsAmplitude m a) ∧
      HasCompactSupport (Function.uncurry a) ∧
      amplitudeSymbol a = compactKernelSymbol k ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) x,
        amplitudeApply a u x = ∫ y, k x y (u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let b : ContDiffBump (0 : X) := ⟨1, 2, by norm_num, by norm_num⟩
  let ρ : X → ℝ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hcρ : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hiρ : ∫ ξ, ρ ξ = 1 := b.integral_normed
  let c : ℝ := (2 * Real.pi) ^ n
  have hcpos : 0 < c := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  let a : AmplitudeFunction n r q := fun x y ξ ↦
    (c * ρ ξ) • Complex.exp (-Complex.I * (inner ℝ (x - y) ξ : ℂ)) • k x y
  have has : ContDiff ℝ ∞ (fun z : (X × X) × X ↦ a z.1.1 z.1.2 z.2) := by
    have hphase : ContDiff ℝ ∞ (fun z : (X × X) × X ↦
        Complex.exp (-Complex.I * (inner ℝ (z.1.1 - z.1.2) z.2 : ℂ))) := by
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd))).cexp
    exact (contDiff_const.mul (hρ.comp contDiff_snd)).smul
      (hphase.smul (hk.comp contDiff_fst))
  have hasupp : tsupport (Function.uncurry a) ⊆ tsupport (Function.uncurry k) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hzk
    have hkz : k z.1 z.2 = 0 :=
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry k) hzk
    apply hz
    funext ξ
    simp only [Function.uncurry, a, hkz, smul_zero, Pi.zero_apply]
  have haspatial : HasCompactSupport (Function.uncurry a) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hasupp
  have hac : HasCompactSupport (fun z : (X × X) × X ↦ a z.1.1 z.1.2 z.2) := by
    apply (hc.prod hcρ).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    by_contra hn
    rcases not_and_or.mp hn with h | h
    · have hkz : k z.1.1 z.1.2 = 0 :=
        image_eq_zero_of_notMem_tsupport (f := Function.uncurry k) h
      exact hz (by simp only [a, hkz, smul_zero])
    · exact hz (by simp [a, image_eq_zero_of_notMem_tsupport h])
  refine ⟨a, compact_amplitude_isAmplitude a has hac, haspatial, ?_, ?_⟩
  · -- After phase cancellation, the auxiliary cutoff integrates to one at every translation.
    funext x η
    have phase_cancel (y ζ : X) :
        Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ) =
          (c * ρ (η + ζ)) •
            (Complex.exp (-Complex.I * (inner ℝ (x - y) η : ℂ)) • k x y) := by
      dsimp [a]
      rw [smul_comm _ (c * ρ (η + ζ)), smul_smul, ← Complex.exp_add]
      have heq : Complex.I * (inner ℝ (x - y) ζ : ℂ) +
          -Complex.I * (inner ℝ (x - y) (η + ζ) : ℂ) =
            -Complex.I * (inner ℝ (x - y) η : ℂ) := by
        rw [inner_add_right, Complex.ofReal_add]
        ring
      rw [heq]
    have hiη : ∫ ζ, ρ (η + ζ) = 1 := by
      rw [integral_add_left_eq_self, hiρ]
    change c⁻¹ • (∫ ζ, ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)) = _
    simp_rw [phase_cancel, integral_smul]
    rw [integral_smul_const]
    rw [integral_const_mul, hiη, mul_one, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
    rfl
  · -- The same normalization gives the original kernel action before symbol reduction.
    intro u x
    have phase_cancel (y ξ : X) :
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y) =
          (c * ρ ξ) • k x y (u y) := by
      simp only [a, smul_apply]
      rw [smul_comm _ (c * ρ ξ), smul_smul, ← Complex.exp_add]
      have heq : Complex.I * (inner ℝ (x - y) ξ : ℂ) +
          -Complex.I * (inner ℝ (x - y) ξ : ℂ) = 0 := by ring
      rw [heq, Complex.exp_zero, one_smul]
    change c⁻¹ • (∫ ξ, ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y)) = _
    simp_rw [phase_cancel, integral_smul]
    rw [integral_smul_const]
    rw [integral_const_mul, hiρ, mul_one, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]

/-- The partial Fourier symbol of a compact smooth kernel has every real symbol order. -/
theorem isSmoothingSymbol_compactKernelSymbol {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hc : HasCompactSupport (Function.uncurry k)) :
    IsSmoothingSymbol Set.univ (compactKernelSymbol k) := by
  obtain ⟨a, ha, hs, heq, _⟩ := compact_kernel_amplitude_spec k hk hc
  intro m
  rw [← heq]
  exact isSymbol_amplitudeSymbol m a (ha m) hs

/-- Quantizing the actual Fourier symbol recovers exactly the original smooth kernel integral. -/
theorem quantize_compactKernelSymbol {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hc : HasCompactSupport (Function.uncurry k))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (compactKernelSymbol k) u x = ∫ y, k x y (u y) := by
  obtain ⟨a, ha, hs, heq, happly⟩ := compact_kernel_amplitude_spec k hk hc
  rw [← heq, quantize_amplitudeSymbol 0 a (ha 0) hs u]
  exact happly u x

/-- The same symbol retains compact support in the output position, uniformly in frequency. -/
theorem hasCompactSupport_compactKernelSymbol {n r q : ℕ}
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hc : HasCompactSupport (Function.uncurry k)) :
    HasCompactSupport (compactKernelSymbol k) := by
  obtain ⟨a, _, hs, heq, _⟩ := compact_kernel_amplitude_spec k hk hc
  rw [← heq]
  exact hasCompactSupport_amplitudeSymbol a hs

end AtiyahSinger
