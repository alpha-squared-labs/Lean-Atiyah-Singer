/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Pseudolocal
public import AtiyahSinger.Analysis.TwoSidedCutoff

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Smooth kernels of smoothing symbols

Public module ID: M0985.

The inverse Fourier integral of a smoothing symbol is an actual smooth
kernel. Local uniform bounds justify all spatial derivatives under the frequency
integral. Quantization equals its kernel action with the original Fourier constants.
Two-sided compact operator support then permits a compact smooth kernel representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 20

private theorem contDiff_integral_of_compact_bounds {n : ℕ} {P W : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [SecondCountableTopology W]
    (f : P → EuclideanSpace ℝ (Fin n) → W)
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hbound : ∀ K : Set P, IsCompact K → ∀ k : ℕ,
      ∃ b : EuclideanSpace ℝ (Fin n) → ℝ, Integrable b ∧
        ∀ x ∈ K, ∀ ξ, ‖iteratedFDeriv ℝ k (fun x ↦ f x ξ) x‖ ≤ b ξ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f x ξ) ∧
      ∀ k x, Integrable (fun ξ ↦ iteratedFDeriv ℝ k (fun x ↦ f x ξ) x) ∧
        iteratedFDeriv ℝ k (fun x ↦ ∫ ξ, f x ξ) x =
          ∫ ξ, iteratedFDeriv ℝ k (fun x ↦ f x ξ) x := by
  let V := EuclideanSpace ℝ (Fin n)
  -- All parameter derivatives remain jointly smooth before integration.
  have parametric {X Y Z : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (g : X → Y → Z) (hg : ContDiff ℝ ∞ (Function.uncurry g)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (g z.1) z.2) := by
    induction k with
    | zero =>
      exact hg.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y Z).symm : _ →L[ℝ] Y [×0]→L[ℝ] Z)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (g z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (g z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) Z).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] Z)
  let D (k : ℕ) (x : P) (ξ : V) := iteratedFDeriv ℝ k (fun x ↦ f x ξ) x
  have hs (k : ℕ) : ContDiff ℝ ∞ (Function.uncurry (D k)) := by
    exact (parametric (fun ξ x ↦ f x ξ)
      (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
        (contDiff_snd.prodMk contDiff_fst)
  have hi (k : ℕ) (x : P) : Integrable (D k x) := by
    obtain ⟨b, hb, hbk⟩ := hbound {x} isCompact_singleton k
    exact hb.mono' ((hs k).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall (hbk x (Set.mem_singleton x)))
  -- A compact neighborhood supplies the uniform bound needed to differentiate each integral.
  have hd (k : ℕ) (x : P) :
      HasFDerivAt (fun x ↦ ∫ ξ, D k x ξ)
        ((∫ ξ, D (k + 1) x ξ).curryLeft) x := by
    obtain ⟨b, hb, hbk⟩ := hbound (Metric.closedBall x 1) (isCompact_closedBall _ _) (k + 1)
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P) W
    have heq (z : P) (ξ : V) : fderiv ℝ (fun z ↦ D k z ξ) z = L (D (k + 1) z ξ) := by
      dsimp only [D]
      rw [iteratedFDeriv_succ_eq_comp_left]
      exact (L.apply_symm_apply _).symm
    have hdiff (ξ : V) (z : P) : HasFDerivAt (fun z ↦ D k z ξ) (L (D (k + 1) z ξ)) z := by
      rw [← heq]
      exact (((hs k).comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) z).hasFDerivAt
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := D k) (F' := fun z ξ ↦ L (D (k + 1) z ξ)) (s := Metric.ball x 1)
      (bound := b) (x₀ := x) (Metric.ball_mem_nhds _ zero_lt_one)
      (Filter.Eventually.of_forall (fun z ↦ (hi k z).1)) (hi k x)
      ((L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hi (k + 1) x)).1)
      (Filter.Eventually.of_forall (fun ξ z hz ↦ by
        simpa using hbk z (Metric.ball_subset_closedBall hz) ξ))
      hb (Filter.Eventually.of_forall (fun ξ z _ ↦ hdiff ξ z))
    have hL : (∫ ξ, L (D (k + 1) x ξ)) = L (∫ ξ, D (k + 1) x ξ) :=
      L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi (k + 1) x)
    rw [hL] at h
    exact h
  -- These compatible integral derivatives give the full derivative tower of the integral.
  have hTaylor : HasFTaylorSeriesUpTo (∞ : ℕ∞ω) (fun x ↦ ∫ ξ, f x ξ)
      (fun x k ↦ ∫ ξ, D k x ξ) := by
    constructor
    · intro x
      let L := continuousMultilinearCurryFin0 ℝ P W
      calc
        _ = ∫ ξ, L (D 0 x ξ) :=
          (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi 0 x)).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with ξ
          simp [D, L]
    · intro k _ x
      exact hd k x
    · intro k _
      exact (show Differentiable ℝ (fun x ↦ ∫ ξ, D k x ξ) from
        fun x ↦ (hd k x).differentiableAt).continuous
  exact ⟨hTaylor.contDiff, fun k x ↦
    ⟨hi k x, (hTaylor.eq_iteratedFDeriv (by simp) x).symm⟩⟩

private theorem kernel_phase_bounds {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (k : ℕ) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        Complex.exp (Complex.I * (inner ℝ (z.1 - z.2) ξ : ℂ))) z‖ ≤
          C * (1 + ‖ξ‖) ^ d := by
  let X := EuclideanSpace ℝ (Fin n)
  -- The phase is a one-variable exponential composed with a frequency-dependent linear map.
  let D : X × X →L[ℝ] X := ContinuousLinearMap.fst ℝ X X - ContinuousLinearMap.snd ℝ X X
  have hD : ‖D‖ ≤ 2 := by
    apply D.opNorm_le_bound (by norm_num)
    intro z
    change ‖z.1 - z.2‖ ≤ 2 * ‖z‖
    exact (norm_sub_le _ _).trans (by nlinarith [norm_fst_le z, norm_snd_le z])
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨d, C, hC, hder⟩ :=
    Complex.hasTemperateGrowth_exp_mul_I.norm_iteratedFDeriv_le_uniform k
  refine ⟨d + k, C * (1 + 2 * max R 0) ^ d * 2 ^ k, by positivity, ?_⟩
  intro i hi z hz ξ
  let L : X × X →L[ℝ] ℝ := (innerSL ℝ ξ).comp D
  let e : ℝ → ℂ := fun t ↦ Complex.exp (t * Complex.I)
  have he : ContDiff ℝ ∞ e := Complex.hasTemperateGrowth_exp_mul_I.1
  have hfun : (fun z : X × X ↦
      Complex.exp (Complex.I * (inner ℝ (z.1 - z.2) ξ : ℂ))) = e ∘ L := by
    funext z
    simp [e, L, D, real_inner_comm, mul_comm, inner_sub_right]
  have hL : ‖L‖ ≤ 2 * ‖ξ‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [innerSL_apply_norm]
    nlinarith [norm_nonneg ξ]
  -- Compactness bounds the spatial parameter; only polynomial frequency growth remains.
  have hbase : 1 + ‖L z‖ ≤ (1 + 2 * max R 0) * (1 + ‖ξ‖) := by
    have hzR := (hR z hz).trans (le_max_left R 0)
    have hn := (L.le_opNorm z).trans (mul_le_mul hL hzR (norm_nonneg z) (by positivity))
    nlinarith [norm_nonneg ξ, le_max_right R 0]
  rw [hfun, L.iteratedFDeriv_comp_right he z (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i e (L z)‖ * ‖L‖ ^ i := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i e (L z)) (fun _ ↦ L)
    _ ≤ (C * (1 + ‖L z‖) ^ d) * ‖L‖ ^ i := by
      gcongr
      exact hder i hi (L z)
    _ ≤ (C * ((1 + 2 * max R 0) * (1 + ‖ξ‖)) ^ d) *
        (2 * (1 + ‖ξ‖)) ^ k := by
      gcongr
      exact (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i).trans
        (pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) hi)
    _ = _ := by rw [mul_pow, mul_pow, pow_add]; ring

private theorem symbol_spatial_bounds {n r q : ℕ} (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun x ↦ p x ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ m := by
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  -- The zero frequency derivative is an isometry, so the original mixed bounds apply directly.
  choose C hC hbound using fun i ↦ hp.2 K (Set.subset_univ _) hK i 0
  refine ⟨∑ j ∈ Finset.range (k + 1), C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro i hi x hx ξ
  have hb := hbound i x hx ξ
  have hzero : (fun y ↦ iteratedFDeriv ℝ 0 (p y) ξ) =
      (continuousMultilinearCurryFin0 ℝ X H).symm ∘ (fun y ↦ p y ξ) := by
    funext y
    exact congrFun iteratedFDeriv_zero_eq_comp ξ
  simp only [symbolDerivative, hzero, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
    Nat.cast_zero, sub_zero] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_range.mpr (by omega)))
    (Real.rpow_nonneg (by positivity) _))

set_option maxHeartbeats 1000000 in

private theorem smoothing_kernel_integrand_bounds {n r q : ℕ} (p : SymbolFunction n r q)
    (hp : IsSmoothingSymbol Set.univ p)
    (K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (k : ℕ) :
    ∃ b : EuclideanSpace ℝ (Fin n) → ℝ, Integrable b ∧ ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        Complex.exp (Complex.I * (inner ℝ (z.1 - z.2) ξ : ℂ)) • p z.1 ξ) z‖ ≤ b ξ := by
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨d, A, hA, hphase⟩ := kernel_phase_bounds K hK k
  -- Choose a negative symbol order that absorbs phase growth and leaves integrable decay.
  let m : ℝ := -(d : ℝ) - ((n + 1 : ℕ) : ℝ)
  obtain ⟨B, hB, hsymbol⟩ := symbol_spatial_bounds m p (hp m)
    (Prod.fst '' K) (hK.image continuous_fst) k
  let C : ℝ := (2 : ℝ) ^ k * A * B
  let decay : X → ℝ := fun ξ ↦ (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [X])
  refine ⟨fun ξ ↦ C * decay ξ, hdecay.const_mul C, ?_⟩
  intro z hz ξ
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using (hp m).1
  have hpx : ContDiff ℝ ∞ (fun z : X × X ↦ p z.1 ξ) :=
    hps.comp (contDiff_fst.prodMk contDiff_const)
  have hphaseSmooth : ContDiff ℝ ∞ (fun z : X × X ↦
      Complex.exp (Complex.I * (inner ℝ (z.1 - z.2) ξ : ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      ((contDiff_fst.sub contDiff_snd).inner ℝ contDiff_const))).cexp
  have hproj (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun z : X × X ↦ p z.1 ξ) z‖ ≤ B * (1 + ‖ξ‖) ^ m := by
    let F : X × X →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
    have hF : ‖F‖ ≤ 1 := by
      apply F.opNorm_le_bound zero_le_one
      intro w
      simpa [F] using norm_fst_le w
    have hs : ContDiff ℝ ∞ (fun x ↦ p x ξ) :=
      hps.comp (contDiff_id.prodMk contDiff_const)
    change ‖iteratedFDeriv ℝ i ((fun x ↦ p x ξ) ∘ F) z‖ ≤ _
    rw [F.iteratedFDeriv_comp_right hs z (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    apply (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg F) hF) (norm_nonneg _)).trans
    rw [mul_one]
    exact hsymbol i hi z.1 ⟨z, hz, rfl⟩ ξ
  -- Leibniz bounds every mixed term by the same integrable frequency weight.
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i
          (fun z : X × X ↦ Complex.exp (Complex.I * (inner ℝ (z.1 - z.2) ξ : ℂ))) z‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun z : X × X ↦ p z.1 ξ) z‖ :=
      norm_iteratedFDeriv_smul_le hphaseSmooth hpx z (by simp)
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (A * (1 + ‖ξ‖) ^ d) * (B * (1 + ‖ξ‖) ^ m) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact hphase i (by simpa using hi) z hz ξ
      · exact hproj (k - i) (Nat.sub_le _ _)
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (A * B * decay ξ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      have he : (1 + ‖ξ‖) ^ d * (1 + ‖ξ‖) ^ m = decay ξ := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
        congr 1
        dsimp [m]
        ring
      calc
        _ = (k.choose i : ℝ) * (A * B * ((1 + ‖ξ‖) ^ d * (1 + ‖ξ‖) ^ m)) := by ring
        _ = _ := by rw [he]
    _ = _ := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [C]
      ring

/-- The actual inverse Fourier kernel of a rapidly decreasing symbol. -/
def smoothingSymbolKernel {n r q : ℕ} (p : SymbolFunction n r q)
    (x y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  ((2 * Real.pi) ^ n)⁻¹ •
    ∫ ξ, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • p x ξ

/-- Arbitrarily negative symbol orders make the inverse Fourier kernel jointly smooth. -/
theorem contDiff_smoothingSymbolKernel {n r q : ℕ} (p : SymbolFunction n r q)
    (hp : IsSmoothingSymbol Set.univ p) :
    ContDiff ℝ ∞ (Function.uncurry (smoothingSymbolKernel p)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let f (z : X × X) (ξ : X) :=
    Complex.exp (Complex.I * (inner ℝ (z.1 - z.2) ξ : ℂ)) • p z.1 ξ
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using (hp 0).1
  have hf : ContDiff ℝ ∞ (Function.uncurry f) := by
    have he : ContDiff ℝ ∞ (fun z : (X × X) × X ↦
        Complex.exp (Complex.I * (inner ℝ (z.1.1 - z.1.2) z.2 : ℂ))) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd))).cexp
    exact he.smul (hps.comp (contDiff_fst.fst.prodMk contDiff_snd))
  exact ((contDiff_integral_of_compact_bounds f hf
    (smoothing_kernel_integrand_bounds p hp)).1).const_smul _

private theorem integrable_smoothing_symbol_at {n r q : ℕ} (p : SymbolFunction n r q)
    (hp : IsSmoothingSymbol Set.univ p) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (p x) := by
  let X := EuclideanSpace ℝ (Fin n)
  let m : ℝ := -((n + 1 : ℕ) : ℝ)
  obtain ⟨C, _, hC⟩ := symbol_spatial_bounds m p (hp m) {x} isCompact_singleton 0
  have hdecay : Integrable (fun ξ : X ↦ (1 + ‖ξ‖) ^ m) :=
    integrable_one_add_norm (by simp [X])
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using (hp 0).1
  apply (hdecay.const_mul C).mono'
    (hps.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  filter_upwards [] with ξ
  change ‖p x ξ‖ ≤ C * (1 + ‖ξ‖) ^ m
  simpa only [norm_iteratedFDeriv_zero] using hC 0 le_rfl x (Set.mem_singleton x) ξ

/-- The inverse Fourier kernel acts by exactly the original quantization on Schwartz inputs. -/
theorem quantize_eq_integral_smoothingSymbolKernel {n r q : ℕ} (p : SymbolFunction n r q)
    (hp : IsSmoothingSymbol Set.univ p)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize p u x = ∫ y, smoothingSymbolKernel p x y (u y) := by
  let X := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin q)
  let f (ξ y : X) : F :=
    Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • p x ξ (u y)
  have hpInt : Integrable (p x) := integrable_smoothing_symbol_at p hp x
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using (hp 0).1
  have hpcont : Continuous (p x) :=
    hps.continuous.comp (continuous_const.prodMk continuous_id)
  have hf : Continuous (Function.uncurry f) := by
    have he : Continuous (fun z : X × X ↦
        Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ))) := by fun_prop
    exact he.smul ((hpcont.comp continuous_fst).clm_apply (u.continuous.comp continuous_snd))
  -- Both factors are absolutely integrable, so this frequency/input interchange is justified.
  have hfInt : Integrable (Function.uncurry f) (volume.prod volume) := by
    apply (hpInt.norm.mul_prod u.integrable.norm).mono' hf.aestronglyMeasurable
    filter_upwards [] with z
    have he : ‖Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    simpa only [Function.uncurry, f, norm_smul, he, one_mul] using (p x z.1).le_opNorm (u z.2)
  have hfourier (ξ : X) :
      fourierSG u ξ = ∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • u y := by
    unfold fourierSG
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [] with y
    congr 2
    rw [inner_smul_right]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hinput (ξ : X) : Integrable
      (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • u y) := by
    apply u.integrable.norm.mono' (by fun_prop)
    filter_upwards [] with y
    simp [norm_smul, Complex.norm_exp, Complex.mul_re]
  have hinner (ξ : X) :
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ (fourierSG u ξ) =
        ∫ y, f ξ y := by
    rw [hfourier, ← (p x ξ).integral_comp_comm (hinput ξ), ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [map_smul, smul_smul, f]
    rw [← Complex.exp_add]
    congr 2
    rw [inner_sub_left, Complex.ofReal_sub]
    ring
  have hrow (y : X) : Integrable
      (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • p x ξ) := by
    apply hpInt.norm.mono' (by fun_prop)
    filter_upwards [] with ξ
    simp [norm_smul, Complex.norm_exp, Complex.mul_re]
  change ((2 * Real.pi) ^ n)⁻¹ •
    (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ (fourierSG u ξ)) = _
  simp_rw [hinner]
  rw [integral_integral_swap hfInt, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [smoothingSymbolKernel, smul_apply, ContinuousLinearMap.integral_apply (hrow y) (u y)]
  rfl

/-- A smoothing symbol with compact two-sided operator support has a compact smooth kernel. -/
theorem exists_compactSmoothKernel_of_smoothingSymbol {n r q : ℕ}
    (p : SymbolFunction n r q) (hp : IsSmoothingSymbol Set.univ p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P) :
    ∃ k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)),
      ContDiff ℝ ∞ (Function.uncurry k) ∧ HasCompactSupport (Function.uncurry k) ∧
        ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) x,
          P u x = ∫ y, k x y (u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  -- A compact smooth cutoff is one on an open neighborhood of the full operator support.
  obtain ⟨O, hOo, hKO, _, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (Set.subset_univ K)
  obtain ⟨O', hO'o, hOO', _, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc isOpen_univ (Set.subset_univ _)
  obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hχsupport : tsupport χ = closure O' := congrArg closure hsχ
  have hcχ : HasCompactSupport χ := by
    simpa [HasCompactSupport, hχsupport] using hO'c
  have hχone : K ⊆ interior {x | χ x = 1} := by
    intro x hx
    apply mem_interior.mpr
    refine ⟨O, ?_, hOo, hKO hx⟩
    intro y hy
    exact (honeχ y).mp (subset_closure hy)
  let k := fun x y : X ↦ χ x • (χ y • smoothingSymbolKernel p x y)
  have hk : ContDiff ℝ ∞ (Function.uncurry k) :=
    (hχ.comp contDiff_fst).smul
      ((hχ.comp contDiff_snd).smul (contDiff_smoothingSymbolKernel p hp))
  have hck : HasCompactSupport (Function.uncurry k) := by
    apply (hcχ.prod hcχ).of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport χ))
    intro z hz
    constructor
    · by_contra hx
      apply hz
      simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport hx]
    · by_contra hy
      apply hz
      simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport hy]
  refine ⟨k, hk, hck, ?_⟩
  intro u x
  let v : 𝓢(X, E) := SchwartzMap.smulLeftCLM E (fun y ↦ (χ y : ℂ)) u
  have hgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hv (y : X) : v y = χ y • u y := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
    exact algebraMap_smul ℂ (χ y) (u y)
  -- The input difference vanishes near K, so the original support hypothesis kills it.
  have hinput : P v = P u := by
    have hd : Disjoint (tsupport (v - u)) K := by
      apply Set.disjoint_left.mpr
      intro y hy hyK
      have hnear : (fun z ↦ (v - u) z) =ᶠ[nhds y] 0 := by
        filter_upwards [isOpen_interior.mem_nhds (hχone hyK)] with z hz
        have hχz : z ∈ {w : X | χ w = 1} := interior_subset hz
        change χ z = 1 at hχz
        simp only [sub_apply, hv, hχz, one_smul, sub_self, Pi.zero_apply]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hnear) hy
    have hzero := hPK.2 (v - u) hd
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  -- Output support gives the second exact cutoff identity, including points outside K.
  have houtput : χ x • P u x = P u x := by
    by_cases hx : x ∈ K
    · have hχx : x ∈ {w : X | χ w = 1} := interior_subset (hχone hx)
      change χ x = 1 at hχx
      rw [hχx, one_smul]
    · have hz : P u x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hPK.1 u h))
      rw [hz, smul_zero]
  calc
    P u x = χ x • P v x := by rw [hinput, houtput]
    _ = χ x • quantize p v x := by rw [hP]
    _ = χ x • ∫ y, smoothingSymbolKernel p x y (v y) := by
      rw [quantize_eq_integral_smoothingSymbolKernel p hp]
    _ = ∫ y, k x y (u y) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [hv, ContinuousLinearMap.map_smul_of_tower, k, smul_apply]

end AtiyahSinger
