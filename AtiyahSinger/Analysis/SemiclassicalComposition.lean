/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FrequencyScaling
public import AtiyahSinger.Analysis.FrequencyScalingAmplitude
public import AtiyahSinger.Analysis.LocalComposition
public import AtiyahSinger.Analysis.SymbolCoordinateEstimates

import all AtiyahSinger.Analysis.Amplitude
import AtiyahSinger.Analysis.CompactJetIntegral
import AtiyahSinger.Analysis.NoncompactSymbolIntegral
import all AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Uniform estimates for the actual semiclassical composition

Public module ID: M2293.

The preparatory Fourier estimates retain a parameter weight in common constants for
families with one fixed compact spatial support. The integration formulas are the existing
amplitude reduction and quantization formulas. Spatial symbol support and two-sided
operator support are separate conditions when using the exact composition identity.

Sources: SG III.3.5 and III.3.10 for amplitude reduction and composition. The explicit
uniform parameter estimates are project supplements for positive frequency contractions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff FourierTransform SchwartzMap

/-- Joint smoothness of a partial derivative follows from the full smooth function. -/
private theorem contDiff_partial_iteratedFDeriv
    {P Q W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P → Q → W) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ContDiff ℝ ∞ (fun z : P × Q ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
  induction k with
  | zero =>
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ Q W).symm : _ →L[ℝ] Q [×0]→L[ℝ] W)
  | succ k ih =>
    have h : ContDiff ℝ ∞
        (Function.uncurry (fun p : P × Q ↦ fun y : Q ↦ iteratedFDeriv ℝ k (f p.1) y)) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd : ContDiff ℝ ∞
        (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ k (f p.1)) p.2) :=
      h.fderiv contDiff_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Q) W).symm :
        _ →L[ℝ] Q [×(k + 1)]→L[ℝ] W)

/-- Use the existing compact-jet integral theorem on the original compact spatial support. -/
private theorem compact_spatial_integral
    {n : ℕ} {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : X → EuclideanSpace ℝ (Fin n) → W)
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hzero : ∀ x y, y ∉ K → f x y = 0) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, f x y) ∧
      ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ y, f x y) x =
        ∫ y, iteratedFDeriv ℝ i (fun x ↦ f x y) x := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let ν : Measure ↥K := Measure.comap Subtype.val (volume : Measure V)
  let : IsFiniteMeasure ν := ⟨by
    change Measure.comap Subtype.val (volume : Measure V) univ < ⊤
    rw [comap_subtype_coe_apply hK.measurableSet]
    simpa only [Set.image_univ, Subtype.range_coe] using hK.measure_lt_top⟩
  let g (y : ↥K) (x : X) := f x y.val
  have hg (y : ↥K) : ContDiffOn ℝ ∞ (g y) univ :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
  have hD (k : ℕ) : ContDiff ℝ ∞
      (fun z : X × V ↦ iteratedFDeriv ℝ k (fun x ↦ f x z.2) z.1) :=
    (contDiff_partial_iteratedFDeriv (fun y x ↦ f x y)
      (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
        (contDiff_snd.prodMk contDiff_fst)
  have hjets (k : ℕ) : ContinuousOn
      (fun z : ↥K × X ↦ iteratedFDeriv ℝ k (g z.1) z.2) (univ ×ˢ univ) :=
    ((hD k).continuous.comp (continuous_snd.prodMk
      (continuous_subtype_val.comp continuous_fst))).continuousOn
  have heq (x : X) : (∫ y : ↥K, g y x ∂ν) = ∫ y : V, f x y := by
    change (∫ y : ↥K, f x y.val ∂Measure.comap Subtype.val (volume : Measure V)) = _
    rw [integral_subtype_comap hK.measurableSet]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ hzero x y hy)
  have hfun : (fun x ↦ ∫ y : ↥K, g y x ∂ν) = fun x ↦ ∫ y : V, f x y := funext heq
  have hs : ContDiff ℝ ∞ (fun x ↦ ∫ y : ↥K, g y x ∂ν) := by
    exact contDiffOn_univ.mp
      (contDiffOn_integral_of_continuous_jets ν isOpen_univ hg hjets)
  refine ⟨hfun ▸ hs, ?_⟩
  intro i x
  have h := iteratedFDeriv_integral_of_continuous_jets ν isOpen_univ hg hjets i
    (mem_univ x)
  rw [hfun] at h
  refine h.trans ?_
  change (∫ y : ↥K, iteratedFDeriv ℝ i (fun x ↦ f x y.val) x
    ∂Measure.comap Subtype.val (volume : Measure V)) = _
  rw [integral_subtype_comap hK.measurableSet
    (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hz : (fun x ↦ f x y) = 0 := funext (fun x ↦ hzero x y hy)
  simp [hz]

/-- Weighted Fourier decay preserves a nonnegative parameter factor in one common bound. -/
private theorem exists_weighted_fourier_bound
    {T : Type*} {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f : T → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) → W)
    (hf : ∀ z η ζ, ContDiff ℝ ∞ (f z η ζ))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ z η ζ, tsupport (f z η ζ) ⊆ K)
    (s : ℝ) (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z η ζ y, y ∈ K →
      ‖iteratedFDeriv ℝ j (f z η ζ) y‖ ≤ C * w z * (1 + ‖η + ζ‖) ^ s)
    (c : ℝ) (hc : c ≠ 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z η ζ,
      ‖𝓕 (f z η ζ) (c • ζ)‖ ≤
        C * w z * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  /- Peetre's inequality moves the external frequency weight outside the Fourier integral.
  Normalize only in that external frequency and the parameter. The existing uniform
  compact-support Fourier estimate then chooses its constant before all parameters. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  have hweight (η ζ : V) :
      (1 + ‖η + ζ‖) ^ s ≤ (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ |s| := by
    have htriangle (x y : V) : 1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
      have hnorm := norm_add_le x y
      have hprod := mul_nonneg (norm_nonneg x) (norm_nonneg y)
      nlinarith
    by_cases hs : 0 ≤ s
    · rw [abs_of_nonneg hs, ← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (htriangle η ζ) hs
    · have hs' : s ≤ 0 := le_of_not_ge hs
      have hreverse : 1 + ‖η‖ ≤ (1 + ‖η + ζ‖) * (1 + ‖ζ‖) := by
        simpa only [add_neg_cancel_right, norm_neg] using htriangle (η + ζ) (-ζ)
      have h := Real.rpow_le_rpow_of_nonpos (by positivity) hreverse hs'
      rw [Real.mul_rpow (by positivity) (by positivity)] at h
      calc
        _ ≤ (1 + ‖η‖) ^ s / (1 + ‖ζ‖) ^ s :=
          (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) s)).mpr h
        _ = _ := by rw [abs_of_nonpos hs', Real.rpow_neg (by positivity), div_eq_mul_inv]
  let g (p : T × V) (ζ y : V) : W :=
    (w p.1 * (1 + ‖p.2‖) ^ s)⁻¹ • f p.1 p.2 ζ y
  have hg (p : T × V) (ζ : V) : ContDiff ℝ ∞ (g p ζ) :=
    (hf p.1 p.2 ζ).const_smul _
  have hgsupp (p : T × V) (ζ : V) : tsupport (g p ζ) ⊆ K :=
    (tsupport_smul_subset_right (fun _ ↦ (w p.1 * (1 + ‖p.2‖) ^ s)⁻¹) _).trans
      (hsupp p.1 p.2 ζ)
  have hgb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ζ y, y ∈ K →
      ‖iteratedFDeriv ℝ j (g p ζ) y‖ ≤ C * (1 + ‖ζ‖) ^ ⌈|s|⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := hb j
    refine ⟨C, hC, ?_⟩
    intro p ζ y hy
    by_cases hwzero : w p.1 = 0
    · have hgzero : g p ζ = 0 := by
        funext y
        simp only [g, hwzero, zero_mul, inv_zero, zero_smul, Pi.zero_apply]
      rw [hgzero]
      simpa only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero] using
        mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ 1 + ‖ζ‖) ⌈|s|⌉₊)
    have hwpos : 0 < w p.1 := lt_of_le_of_ne (hw p.1) (Ne.symm hwzero)
    have hp : 0 < (1 + ‖p.2‖) ^ s := Real.rpow_pos_of_pos (by positivity) s
    have hz : (1 + ‖ζ‖) ^ |s| ≤ (1 + ‖ζ‖) ^ ⌈|s|⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le
        (by have := norm_nonneg ζ; linarith) (Nat.le_ceil |s|)
    change ‖iteratedFDeriv ℝ j (fun y ↦ _ • f p.1 p.2 ζ y) y‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hf p.1 p.2 ζ).of_le (by simp)).contDiffAt,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hwpos.le hp.le))]
    calc
      _ ≤ (w p.1 * (1 + ‖p.2‖) ^ s)⁻¹ *
          (C * w p.1 * (1 + ‖p.2 + ζ‖) ^ s) := by
        gcongr
        exact hbound p.1 p.2 ζ y hy
      _ ≤ (w p.1 * (1 + ‖p.2‖) ^ s)⁻¹ *
          (C * w p.1 * ((1 + ‖p.2‖) ^ s * (1 + ‖ζ‖) ^ |s|)) := by
        gcongr
        exact hweight p.2 ζ
      _ = C * (1 + ‖ζ‖) ^ |s| := by field_simp
      _ ≤ C * (1 + ‖ζ‖) ^ ⌈|s|⌉₊ := mul_le_mul_of_nonneg_left hz hC
  obtain ⟨C, hC, hdecay⟩ :=
    fourier_diagonal_decay_of_compact_support g hg K hK hgsupp ⌈|s|⌉₊ hgb c hc N
  refine ⟨C, hC, ?_⟩
  intro z η ζ
  by_cases hwzero : w z = 0
  · obtain ⟨D, _hD, hD⟩ := hb 0
    have hfzero : f z η ζ = 0 := by
      funext y
      by_cases hy : y ∈ K
      · apply norm_eq_zero.mp
        apply le_antisymm _ (norm_nonneg _)
        have h := hD z η ζ y hy
        simpa only [hwzero, mul_zero, zero_mul, norm_iteratedFDeriv_zero] using h
      · exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsupp z η ζ h))
    rw [hfzero, Real.fourier_eq]
    simp only [Pi.zero_apply, smul_zero, integral_zero, norm_zero, hwzero, mul_zero, zero_mul]
    exact le_rfl
  have hwpos : 0 < w z := lt_of_le_of_ne (hw z) (Ne.symm hwzero)
  have hp : 0 < (1 + ‖η‖) ^ s := Real.rpow_pos_of_pos (by positivity) s
  have h := hdecay (z, η) ζ
  change ‖𝓕 ((w z * (1 + ‖η‖) ^ s)⁻¹ • f z η ζ) (c • ζ)‖ ≤ _ at h
  have hscale : 𝓕 ((w z * (1 + ‖η‖) ^ s)⁻¹ • f z η ζ) (c • ζ) =
      (w z * (1 + ‖η‖) ^ s)⁻¹ • 𝓕 (f z η ζ) (c • ζ) := by
    simp only [Real.fourier_eq, Pi.smul_apply,
      smul_comm _ (w z * (1 + ‖η‖) ^ s)⁻¹, integral_smul]
  rw [hscale, norm_smul, Real.norm_of_nonneg
    (inv_nonneg.mpr (mul_nonneg hwpos.le hp.le))] at h
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg hwpos.le hp.le)
  have hcancel : w z * (1 + ‖η‖) ^ s ≠ 0 := (mul_pos hwpos hp).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hcancel, one_mul] at h'
  convert h' using 1
  ring

/-- Spatial jets vanish outside a closed common support of the original amplitude. -/
private theorem amplitudeDerivative_eq_zero_of_notMem_common_support
    {n r q : ℕ} (a : AmplitudeFunction n r q) (ha : IsAmplitude 0 a)
    (S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hS : IsClosed S) (hsupp : tsupport (Function.uncurry a) ⊆ S)
    (i j k : ℕ) (x y ξ : EuclideanSpace ℝ (Fin n)) (hxy : (x, y) ∉ S) :
    amplitudeDerivative a i j k x y ξ = 0 := by
  let V := EuclideanSpace ℝ (Fin n)
  let D (x y : V) := iteratedFDeriv ℝ k (a x y) ξ
  have hD : ContDiff ℝ ∞ (Function.uncurry D) :=
    (contDiff_partial_iteratedFDeriv (Function.uncurry a) ha.1 k).comp
      (contDiff_id.prodMk contDiff_const)
  have hsupport : tsupport (Function.uncurry D) ⊆ S := by
    apply closure_minimal ?_ hS
    intro p hp
    by_contra hpS
    have hz : a p.1 p.2 = 0 :=
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry a)
        (fun h ↦ hpS (hsupp h))
    apply hp
    change iteratedFDeriv ℝ k (a p.1 p.2) ξ = 0
    rw [hz, iteratedFDeriv_zero, Pi.zero_apply]
  have hz : iteratedFDeriv ℝ (i + j) (Function.uncurry D) (x, y) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h ↦ hxy (hsupport (tsupport_iteratedFDeriv_subset (i + j) h)))
  have h := norm_mixed_iteratedFDeriv_le D hD i j x y
  rw [hz, norm_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- Polynomial bounds for the derivatives of the actual phase on a compact output window. -/
private theorem exists_phase_derivative_bound
    {n : ℕ} (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (k : ℕ) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ L,
      ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ i
            (fun x ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) x‖ ≤
          C * (1 + ‖ξ‖) ^ d := by
  let V := EuclideanSpace ℝ (Fin n)
  obtain ⟨R, hR⟩ := hL.isBounded.exists_norm_le
  obtain ⟨d, C, hC, hder⟩ :=
    Complex.hasTemperateGrowth_exp_mul_I.norm_iteratedFDeriv_le_uniform k
  refine ⟨d + k, C * (1 + max R 0) ^ d, by positivity, ?_⟩
  intro i hi x hx ξ
  let T : V →L[ℝ] ℝ := innerSL ℝ ξ
  let e : ℝ → ℂ := fun t ↦ Complex.exp (t * Complex.I)
  have he : ContDiff ℝ ∞ e := Complex.hasTemperateGrowth_exp_mul_I.1
  have hfun : (fun x : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) = e ∘ T := by
    funext x
    simp [e, T, real_inner_comm, mul_comm]
  rw [hfun, T.iteratedFDeriv_comp_right he x (by simp)]
  have hbase : 1 + ‖T x‖ ≤ (1 + max R 0) * (1 + ‖ξ‖) := by
    have hnorm : ‖T x‖ ≤ ‖ξ‖ * max R 0 :=
      (norm_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_left
        ((hR x hx).trans (le_max_left _ _)) (norm_nonneg _))
    nlinarith [norm_nonneg ξ, le_max_right R 0]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i e (T x)‖ * ‖T‖ ^ i := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i e (T x)) (fun _ ↦ T)
    _ ≤ (C * (1 + ‖T x‖) ^ d) * ‖T‖ ^ i := by
      gcongr
      exact hder i hi (T x)
    _ ≤ (C * ((1 + max R 0) * (1 + ‖ξ‖)) ^ d) * (1 + ‖ξ‖) ^ k := by
      gcongr
      calc
        ‖T‖ ^ i = ‖ξ‖ ^ i := by rw [innerSL_apply_norm]
        _ ≤ (1 + ‖ξ‖) ^ i := by gcongr; linarith [norm_nonneg ξ]
        _ ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hi
    _ = _ := by rw [mul_pow, pow_add]; ring

set_option maxHeartbeats 2000000 in
-- The common Fourier bounds compare several nested spatial and frequency jet targets.
/-- Common bounds for the actual inner amplitude integral retain a parameter weight. -/
private theorem exists_weighted_amplitude_inner_bound
    {T : Type*} {n r q : ℕ} (a : T → AmplitudeFunction n r q)
    (ha : ∀ z, IsAmplitude 0 (a z))
    (S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hS : IsCompact S)
    (hsupp : ∀ z, tsupport (Function.uncurry (a z)) ⊆ S)
    (k : ℕ) (s : ℝ) (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hbound : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x y, (x, y) ∈ S → ∀ ξ,
      ‖amplitudeDerivative (a z) i j k x y ξ‖ ≤ C * w z * (1 + ‖ξ‖) ^ s)
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i N : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let R (z : T) (x η ζ : V) : H :=
      ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a z x y (η + ζ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ η ζ,
      ‖iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R z x η ζ) η) x‖ ≤
        C * w z * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  /- All parameters use the same compact spatial support. Derivatives in the reversed
  spatial order are bounded through full derivatives, so no additional commutation
  theorem is needed. Common Fourier decay then absorbs the phase derivatives. -/
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let K : Set V := Prod.snd '' S
  have hK : IsCompact K := hS.image continuous_snd
  have hazero (z : T) (x y : V) (hy : y ∉ K) : a z x y = 0 :=
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry (a z))
      (fun h ↦ hy ⟨(x, y), hsupp z h, rfl⟩)
  have hcompact (z : T) : HasCompactSupport (Function.uncurry (a z)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp z)
  choose A hA hAb using hbound
  have hglobal (u v : ℕ) (z : T) (x y ξ : V) :
      ‖amplitudeDerivative (a z) u v k x y ξ‖ ≤ A u v * w z * (1 + ‖ξ‖) ^ s := by
    by_cases hxy : (x, y) ∈ S
    · exact hAb u v z x y hxy ξ
    · rw [amplitudeDerivative_eq_zero_of_notMem_common_support
        (a z) (ha z) S hS.isClosed (hsupp z) u v k x y ξ hxy]
      have hnorm : ‖(0 : V [×u]→L[ℝ] V [×v]→L[ℝ] V [×k]→L[ℝ] H)‖ = 0 :=
        norm_zero (E := V [×u]→L[ℝ] V [×v]→L[ℝ] V [×k]→L[ℝ] H)
      rw [hnorm]
      exact mul_nonneg (mul_nonneg (hA u v) (hw z))
        (Real.rpow_nonneg (by positivity) s)
  let D (z : T) (x η ζ y : V) : V [×k]→L[ℝ] H :=
    iteratedFDeriv ℝ k (a z x y) (η + ζ)
  have hD (z : T) (η ζ : V) :
      ContDiff ℝ ∞ (Function.uncurry (fun x y : V ↦ D z x η ζ y)) :=
    (contDiff_partial_iteratedFDeriv (Function.uncurry (a z)) (ha z).1 k).comp
      (contDiff_id.prodMk contDiff_const)
  have hDzero (z : T) (x η ζ y : V) (hy : y ∉ K) : D z x η ζ y = 0 := by
    change iteratedFDeriv ℝ k (a z x y) (η + ζ) = 0
    rw [hazero z x y hy, iteratedFDeriv_zero, Pi.zero_apply]
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let phase (x ζ : V) : ℂ := Complex.exp (Complex.I * (inner ℝ x ζ : ℂ))
  have hphase (ζ : V) : ContDiff ℝ ∞ (fun x ↦ phase x ζ) := by
    simpa [phase, Function.comp_def, real_inner_comm, mul_comm] using
      Complex.hasTemperateGrowth_exp_mul_I.1.comp (innerSL ℝ ζ).contDiff
  let F (z : T) (x η ζ : V) : V [×k]→L[ℝ] H := 𝓕 (D z x η ζ) (c • ζ)
  have hFint (z : T) (x η ζ : V) : F z x η ζ =
      ∫ y, phase (-y) ζ • D z x η ζ y := by
    dsimp only [F]
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    simp only [phase, inner_neg_left, inner_smul_right]
    congr 1
    push_cast
    dsimp [c]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hFderiv (l : ℕ) (z : T) (x η ζ : V) :
      iteratedFDeriv ℝ l (fun x ↦ F z x η ζ) x =
        𝓕 (fun y ↦ iteratedFDeriv ℝ l (fun x ↦ D z x η ζ y) x) (c • ζ) := by
    have hker : ContDiff ℝ ∞ (Function.uncurry
        (fun x y : V ↦ phase (-y) ζ • D z x η ζ y)) :=
      ((hphase ζ).comp contDiff_snd.neg).smul (hD z η ζ)
    have h := (compact_spatial_integral _ hker K hK
      (fun x y hy ↦ by simp only [hDzero z x η ζ y hy, smul_zero])).2 l x
    have heq : (fun x ↦ F z x η ζ) = fun x ↦ ∫ y, phase (-y) ζ • D z x η ζ y :=
      funext (fun x ↦ hFint z x η ζ)
    rw [heq, h, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    have hxy : ContDiff ℝ ∞ (fun x : V ↦ D z x η ζ y) :=
      (hD z η ζ).comp (contDiff_id.prodMk contDiff_const)
    rw [iteratedFDeriv_const_smul_apply' (hxy.contDiffAt.of_le (by simp))]
    congr 1
    simp only [phase, inner_neg_left, inner_smul_right]
    congr 1
    push_cast
    dsimp [c]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hFs (z : T) (η ζ : V) : ContDiff ℝ ∞ (fun x ↦ F z x η ζ) := by
    have hker : ContDiff ℝ ∞ (Function.uncurry
        (fun x y : V ↦ phase (-y) ζ • D z x η ζ y)) :=
      ((hphase ζ).comp contDiff_snd.neg).smul (hD z η ζ)
    have heq : (fun x ↦ F z x η ζ) = fun x ↦ ∫ y, phase (-y) ζ • D z x η ζ y :=
      funext (fun x ↦ hFint z x η ζ)
    rw [heq]
    exact (compact_spatial_integral _ hker K hK
      (fun x y hy ↦ by simp only [hDzero z x η ζ y hy, smul_zero])).1
  have hFbound (l M : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ η ζ,
      ‖iteratedFDeriv ℝ l (fun x ↦ F z x η ζ) x‖ ≤
        C * w z * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-(M : ℝ)) := by
    let f (p : T × ↥L) (η ζ y : V) :=
      iteratedFDeriv ℝ l (fun x ↦ D p.1 x η ζ y) p.2.val
    have hder (z : T) (η ζ : V) : ContDiff ℝ ∞
        (fun p : V × V ↦ iteratedFDeriv ℝ l (fun x ↦ D z x η ζ p.2) p.1) :=
      (contDiff_partial_iteratedFDeriv (fun y x : V ↦ D z x η ζ y)
        ((hD z η ζ).comp (contDiff_snd.prodMk contDiff_fst)) l).comp
          (contDiff_snd.prodMk contDiff_fst)
    have hf (p : T × ↥L) (η ζ : V) : ContDiff ℝ ∞ (f p η ζ) :=
      (hder p.1 η ζ).comp (contDiff_const.prodMk contDiff_id)
    have hs (p : T × ↥L) (η ζ : V) : tsupport (f p η ζ) ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      have hz : (fun x ↦ D p.1 x η ζ y) = 0 :=
        funext (fun x ↦ hDzero p.1 x η ζ y hyK)
      apply hy
      change iteratedFDeriv ℝ l (fun x ↦ D p.1 x η ζ y) p.2.val = 0
      rw [hz, iteratedFDeriv_zero, Pi.zero_apply]
    have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p η ζ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (f p η ζ) y‖ ≤ C * w p.1 * (1 + ‖η + ζ‖) ^ s := by
      let B : ℝ := ∑ u ∈ Finset.range (l + j + 1),
        ∑ v ∈ Finset.range (l + j + 1), A u v
      have hB : 0 ≤ B := Finset.sum_nonneg
        (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦ hA u v))
      refine ⟨2 ^ (l + j) * B, by positivity, ?_⟩
      intro p η ζ y _hy
      have hfull : ‖iteratedFDeriv ℝ (l + j)
          (Function.uncurry (fun x y ↦ D p.1 x η ζ y)) (p.2.val, y)‖ ≤
          2 ^ (l + j) * (B * w p.1 * (1 + ‖η + ζ‖) ^ s) := by
        apply norm_iteratedFDeriv_uncurry_le_of_mixed _ (hD p.1 η ζ)
          (l + j) p.2.val y (B * w p.1 * (1 + ‖η + ζ‖) ^ s)
          (mul_nonneg (mul_nonneg hB (hw p.1))
            (Real.rpow_nonneg (x := 1 + ‖η + ζ‖) (by positivity) s))
        intro u hu v hv
        have hAv : A u v ≤ ∑ t ∈ Finset.range (l + j + 1), A u t :=
          Finset.single_le_sum (fun t _ ↦ hA u t) (by simpa using hv)
        have hAu : (∑ t ∈ Finset.range (l + j + 1), A u t) ≤ B :=
          Finset.single_le_sum
            (fun t _ ↦ Finset.sum_nonneg (fun v _ ↦ hA t v)) (by simpa using hu)
        apply (hglobal u v p.1 p.2.val y (η + ζ)).trans
        have hm := mul_le_mul_of_nonneg_right (hAv.trans hAu)
          (mul_nonneg (hw p.1)
            (Real.rpow_nonneg (x := 1 + ‖η + ζ‖) (by positivity) s))
        simpa only [mul_assoc] using hm
      dsimp only [f]
      calc
        _ ≤ ‖iteratedFDeriv ℝ (j + l)
            (Function.uncurry (fun y x ↦ D p.1 x η ζ y)) (y, p.2.val)‖ :=
          norm_mixed_iteratedFDeriv_le (fun y x ↦ D p.1 x η ζ y)
            ((hD p.1 η ζ).comp (contDiff_snd.prodMk contDiff_fst)) j l y p.2.val
        _ = ‖iteratedFDeriv ℝ (j + l)
            (Function.uncurry (fun x y ↦ D p.1 x η ζ y)) (p.2.val, y)‖ :=
          (LinearIsometryEquiv.prodComm ℝ V V).norm_iteratedFDeriv_comp_right
            (Function.uncurry (fun x y ↦ D p.1 x η ζ y)) (y, p.2.val) (j + l)
        _ ≤ 2 ^ (l + j) * (B * w p.1 * (1 + ‖η + ζ‖) ^ s) := by
          rw [Nat.add_comm j l]
          exact hfull
        _ = _ := by ring
    obtain ⟨C, hC, hb⟩ := exists_weighted_fourier_bound f hf K hK hs s
      (fun p ↦ w p.1) (fun p ↦ hw p.1) hb c hc M
    refine ⟨C, hC, ?_⟩
    intro z x hx η ζ
    rw [hFderiv]
    exact hb (z, ⟨x, hx⟩) η ζ
  let R (z : T) (x η ζ : V) : H :=
    ∫ y, phase (x - y) ζ • a z x y (η + ζ)
  have hReta (z : T) (x η ζ : V) :
      iteratedFDeriv ℝ k (fun η ↦ R z x η ζ) η = phase x ζ • F z x η ζ :=
    (amplitude_reduction_estimates 0 (a z) (ha z) (hcompact z)).2.2.2.1 k x η ζ
  obtain ⟨d, C₀, hC₀, hp⟩ := exists_phase_derivative_bound L hL i
  choose C hC hb using fun l ↦ hFbound (i - l) (N + d)
  let B : ℝ := ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C₀ * C l
  have hB : 0 ≤ B := Finset.sum_nonneg
    (fun l _ ↦ mul_nonneg (mul_nonneg (by positivity) hC₀) (hC l))
  refine ⟨B, hB, ?_⟩
  intro z x hx η ζ
  have heq : (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R z x η ζ) η) =
      fun x ↦ phase x ζ • F z x η ζ := funext (fun x ↦ hReta z x η ζ)
  rw [heq]
  calc
    _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun x ↦ phase x ζ) x‖ *
          ‖iteratedFDeriv ℝ (i - l) (fun x ↦ F z x η ζ) x‖ :=
      norm_iteratedFDeriv_smul_le (hphase ζ) (hFs z η ζ) x (by simp)
    _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
        (C₀ * (1 + ‖ζ‖) ^ d) *
          (C l * w z * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-((N + d : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro l hl
      have hCl := hC l
      have hwz := hw z
      gcongr
      · exact hp l (by simpa using hl) x hx ζ
      · exact hb l z x hx η ζ
    _ = B * w z * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
      dsimp only [B]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      have hpζ : 0 < 1 + ‖ζ‖ := by positivity
      have he : (1 + ‖ζ‖) ^ d * (1 + ‖ζ‖) ^ (-((N + d : ℕ) : ℝ)) =
          (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hpζ]
        congr 1
        push_cast
        ring
      calc
        _ = ((i.choose l : ℝ) * C₀ * C l) * w z * (1 + ‖η‖) ^ s *
            ((1 + ‖ζ‖) ^ d * (1 + ‖ζ‖) ^ (-((N + d : ℕ) : ℝ))) := by ring
        _ = _ := by rw [he]

/-- One common compact spatial support and common amplitude seminorm bounds give common
mixed bounds for the actual reduced symbols. The constant precedes the family parameter. -/
theorem exists_uniform_amplitudeSymbol_bound
    {T : Type*} {n r q : ℕ} (a : T → AmplitudeFunction n r q)
    (ha : ∀ z, IsAmplitude 0 (a z))
    (S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hS : IsCompact S)
    (hsupp : ∀ z, tsupport (Function.uncurry (a z)) ⊆ S)
    (hbound : ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x y, (x, y) ∈ S → ∀ ξ,
      ‖amplitudeDerivative (a z) i j k x y ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(k : ℝ)))
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (amplitudeSymbol (a z)) i k x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  -- Use exact mixed derivative identities and a common integrable Fourier decay.
  let V := EuclideanSpace ℝ (Fin n)
  let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [V])
  have hnonneg (ζ : V) : 0 ≤ decay ζ := Real.rpow_nonneg (by positivity) _
  have hb : ∀ u v : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x y, (x, y) ∈ S → ∀ ξ,
      ‖amplitudeDerivative (a z) u v k x y ξ‖ ≤
        C * (fun _ : T ↦ (1 : ℝ)) z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    intro u v
    simpa only [mul_one] using hbound u v k
  obtain ⟨C, hC, hCb⟩ := exists_weighted_amplitude_inner_bound a ha S hS hsupp k
    (-(k : ℝ)) (fun _ ↦ 1) (fun _ ↦ zero_le_one) hb L hL i (n + 1)
  let c₀ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  refine ⟨‖c₀‖ * C * (∫ ζ, decay ζ), by positivity, ?_⟩
  intro z x hx ξ
  have hcompact : HasCompactSupport (Function.uncurry (a z)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp z)
  rw [(amplitude_reduction_estimates 0 (a z) (ha z) hcompact).2.2.2.2 i k x ξ,
    norm_smul]
  have hboundIntegral :
      ‖∫ ζ, iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦
            ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) •
              a z x y (η + ζ)) ξ) x‖ ≤
        C * (1 + ‖ξ‖) ^ (-(k : ℝ)) * (∫ ζ, decay ζ) := by
    calc
      _ ≤ ∫ ζ, C * (1 + ‖ξ‖) ^ (-(k : ℝ)) * decay ζ :=
        norm_integral_le_of_norm_le (hdecay.const_mul _)
          (Filter.Eventually.of_forall (fun ζ ↦ by
            simpa only [mul_one] using hCb z x hx ξ ζ))
      _ = _ := integral_const_mul _ _
  exact (mul_le_mul_of_nonneg_left hboundIntegral (norm_nonneg _)).trans_eq (by ring)

/-- Apply the existing compact-jet theorem to the fixed real Taylor interval. -/
private theorem interval_integral_spatial_derivatives
    {X W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : ℝ → X → W) (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, f t x) ∧
      ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ t in (0 : ℝ)..1, f t x) x =
        ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ i (f t) x := by
  let J : Set ℝ := Icc 0 1
  let : CompactSpace ↥J := isCompact_iff_compactSpace.mp isCompact_Icc
  let ν : Measure ↥J := Measure.comap Subtype.val (volume : Measure ℝ)
  have hν : ν univ = 1 := by
    change Measure.comap Subtype.val (volume : Measure ℝ) univ = 1
    rw [comap_subtype_coe_apply measurableSet_Icc]
    simp only [Set.image_univ, Subtype.range_coe, J, Real.volume_Icc,
      sub_zero, ENNReal.ofReal_one]
  let : IsFiniteMeasure ν := ⟨by rw [hν]; norm_num⟩
  let g (t : ↥J) (x : X) := f t.val x
  have hg (t : ↥J) : ContDiffOn ℝ ∞ (g t) univ :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).contDiffOn
  have hjets (k : ℕ) : ContinuousOn
      (fun p : ↥J × X ↦ iteratedFDeriv ℝ k (g p.1) p.2) (univ ×ˢ univ) :=
    ((contDiff_partial_iteratedFDeriv f hf k).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).continuousOn
  have heq (x : X) : (∫ t : ↥J, g t x ∂ν) = ∫ t in (0 : ℝ)..1, f t x := by
    change (∫ t : ↥J, f t.val x ∂Measure.comap Subtype.val (volume : Measure ℝ)) = _
    rw [integral_subtype_comap measurableSet_Icc (fun t ↦ f t x),
      intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  have hfun : (fun x ↦ ∫ t : ↥J, g t x ∂ν) = fun x ↦ ∫ t in (0 : ℝ)..1, f t x :=
    funext heq
  refine ⟨hfun ▸ contDiffOn_univ.mp
    (contDiffOn_integral_of_continuous_jets ν isOpen_univ hg hjets), ?_⟩
  intro i x
  have h := iteratedFDeriv_integral_of_continuous_jets ν isOpen_univ hg hjets i
    (mem_univ x)
  rw [hfun] at h
  refine h.trans ?_
  change (∫ t : ↥J, iteratedFDeriv ℝ i (f t.val) x
    ∂Measure.comap Subtype.val (volume : Measure ℝ)) = _
  rw [integral_subtype_comap measurableSet_Icc (fun t ↦ iteratedFDeriv ℝ i (f t) x),
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- The weaker order-zero frequency weight is uniform along the actual Taylor segment. -/
private theorem shifted_negative_frequency_weight_le
    {n : ℕ} (η ζ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    (1 + ‖η - ζ + t • ζ‖) ^ (-(k : ℝ)) ≤
      (1 + ‖η‖) ^ (-(k : ℝ)) * (1 + ‖ζ‖) ^ (k : ℝ) := by
  have hδ : ‖(1 - t) • ζ‖ ≤ ‖ζ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
    exact mul_le_of_le_one_left (norm_nonneg ζ) (by linarith [ht.1])
  have heq : η = (η - ζ + t • ζ) + (1 - t) • ζ := by
    rw [sub_smul, one_smul]
    abel
  have hnorm : ‖η‖ ≤ ‖η - ζ + t • ζ‖ + ‖ζ‖ := by
    calc
      _ = ‖(η - ζ + t • ζ) + (1 - t) • ζ‖ := congrArg norm heq
      _ ≤ ‖η - ζ + t • ζ‖ + ‖(1 - t) • ζ‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hδ _
  have hreverse : 1 + ‖η‖ ≤ (1 + ‖η - ζ + t • ζ‖) * (1 + ‖ζ‖) := by
    nlinarith [mul_nonneg (norm_nonneg (η - ζ + t • ζ)) (norm_nonneg ζ)]
  have hpow := Real.rpow_le_rpow_of_nonpos
    (by positivity : 0 < 1 + ‖η‖) hreverse (neg_nonpos.mpr (Nat.cast_nonneg k))
  rw [Real.mul_rpow (by positivity) (by positivity)] at hpow
  calc
    _ ≤ (1 + ‖η‖) ^ (-(k : ℝ)) / (1 + ‖ζ‖) ^ (-(k : ℝ)) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < 1 + ‖ζ‖)
        (-(k : ℝ)))).mpr hpow
    _ = _ := by rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖ζ‖), div_inv_eq_mul]

set_option maxHeartbeats 2000000 in
-- The Taylor-jet integral retains nested multilinear targets through the original derivatives.
/-- The actual inner Taylor difference retains a common nonnegative parameter factor. -/
private theorem exists_weighted_inner_taylor_difference_bound
    {T : Type*} {n : ℕ} {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W]
    (R : T → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) → W)
    (hR : ∀ z, ContDiff ℝ ∞
      (fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) ↦ R z p.1.1 p.1.2 p.2))
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (L : Set (EuclideanSpace ℝ (Fin n))) (i k N : ℕ)
    (hbound : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ η ζ,
      ‖iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ (k + 1) (fun η ↦ R z x η ζ) η) x‖ ≤
        C * w z * (1 + ‖η‖) ^ (-(k : ℝ)) * (1 + ‖ζ‖) ^ (-(M : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ η ζ,
      ‖iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k
            (fun η ↦ R z x η ζ - R z x (η - ζ) ζ) η) x‖ ≤
        C * w z * (1 + ‖η‖) ^ (-(k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  /- Frequency differentiation of the difference is the same difference of frequency
  jets. The fundamental theorem of calculus expresses it through one further frequency
  jet. Compact-interval integration commutes with the original spatial derivatives.
  Peetre's inequality absorbs the segment shift and its direction into Fourier decay. -/
  let V := EuclideanSpace ℝ (Fin n)
  obtain ⟨C, hC, hCb⟩ := hbound (N + k + 1)
  refine ⟨C, hC, ?_⟩
  intro z x hx η ζ
  let J := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ V) W
  let Eζ : (V [×(k + 1)]→L[ℝ] W) →L[ℝ] V [×k]→L[ℝ] W :=
    (ContinuousLinearMap.apply ℝ (V [×k]→L[ℝ] W) ζ).comp
      J.toContinuousLinearEquiv.toContinuousLinearMap
  have hEζ : ‖Eζ‖ ≤ ‖ζ‖ := by
    apply Eζ.opNorm_le_bound (norm_nonneg ζ)
    intro D
    calc
      _ ≤ ‖J D‖ * ‖ζ‖ := (J D).le_opNorm ζ
      _ = ‖ζ‖ * ‖D‖ := by rw [J.norm_map]; ring
  have hRs : ContDiff ℝ ∞ (Function.uncurry (fun x η : V ↦ R z x η ζ)) :=
    (hR z).comp (contDiff_id.prodMk contDiff_const)
  have hD (j : ℕ) : ContDiff ℝ ∞
      (fun p : V × V ↦ iteratedFDeriv ℝ j (fun η ↦ R z p.1 η ζ) p.2) :=
    contDiff_partial_iteratedFDeriv _ hRs j
  let B (t : ℝ) (x : V) : V [×k]→L[ℝ] W :=
    Eζ (iteratedFDeriv ℝ (k + 1) (fun η ↦ R z x η ζ) (η - ζ + t • ζ))
  have hB : ContDiff ℝ ∞ (Function.uncurry B) :=
    Eζ.contDiff.comp ((hD (k + 1)).comp
      (contDiff_snd.prodMk (contDiff_const.add (contDiff_fst.smul_const ζ))))
  have hderiv (x : V) (α : V) :
      Eζ (iteratedFDeriv ℝ (k + 1) (fun η ↦ R z x η ζ) α) =
        fderiv ℝ (iteratedFDeriv ℝ k (fun η ↦ R z x η ζ)) α ζ := by
    dsimp only [Eζ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact congrArg (fun D : V →L[ℝ] V [×k]→L[ℝ] W ↦ D ζ) (J.apply_symm_apply _)
  have hftc (x : V) :
      (iteratedFDeriv ℝ k (fun η ↦ R z x η ζ) η -
        iteratedFDeriv ℝ k (fun η ↦ R z x η ζ) (η - ζ)) =
        ∫ t in (0 : ℝ)..1, B t x := by
    have hs : ContDiff ℝ ∞ (iteratedFDeriv ℝ k (fun η ↦ R z x η ζ)) :=
      ((hRs.comp (contDiff_const.prodMk contDiff_id)).iteratedFDeriv_right (by simp))
    have hd (t : ℝ) : HasDerivAt
        (fun t : ℝ ↦ iteratedFDeriv ℝ k (fun η ↦ R z x η ζ) (η - ζ + t • ζ))
        (B t x) t := by
      -- Infer the line derivative from the same normed-space instances as the chain rule.
      have hγ := ((hasDerivAt_id t).smul_const ζ).const_add (η - ζ)
      have h := (hs.differentiable (by simp) (η - ζ + t • ζ)).hasFDerivAt.comp_hasDerivAt
        t hγ
      simp only [one_smul, id_eq] at h
      rw [← hderiv x (η - ζ + t • ζ)] at h
      exact h
    have hint : IntervalIntegrable (fun t ↦ B t x) volume (0 : ℝ) 1 :=
      (hB.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hint
    simpa only [zero_smul, add_zero, one_smul, sub_add_cancel] using h.symm
  have hjets (x : V) :
      iteratedFDeriv ℝ k (fun η ↦ R z x η ζ - R z x (η - ζ) ζ) η =
        ∫ t in (0 : ℝ)..1, B t x := by
    have hsF : ContDiff ℝ ∞ (fun α : V ↦ R z x α ζ) :=
      hRs.comp (contDiff_const.prodMk contDiff_id)
    have hsG : ContDiff ℝ ∞ (fun α : V ↦ R z x (α - ζ) ζ) :=
      hRs.comp (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
    change iteratedFDeriv ℝ k
      ((fun α : V ↦ R z x α ζ) - (fun α : V ↦ R z x (α - ζ) ζ)) η = _
    rw [iteratedFDeriv_sub_apply (hsF.contDiffAt.of_le (by simp))
      (hsG.contDiffAt.of_le (by simp)),
      iteratedFDeriv_comp_sub (f := fun α : V ↦ R z x α ζ) k ζ η]
    exact hftc x
  have heq : (fun x ↦ iteratedFDeriv ℝ k
      (fun η ↦ R z x η ζ - R z x (η - ζ) ζ) η) =
      fun x ↦ ∫ t in (0 : ℝ)..1, B t x := funext hjets
  rw [heq, (interval_integral_spatial_derivatives B hB).2 i x]
  suffices h : ‖∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ i (B t) x‖ ≤
      (C * w z * (1 + ‖η‖) ^ (-(k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))) *
        |(1 : ℝ) - 0| by simpa only [sub_zero, abs_one, mul_one] using h
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [Set.uIoc_of_le zero_le_one] at ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hs : ContDiff ℝ ∞
      (fun x ↦ iteratedFDeriv ℝ (k + 1) (fun η ↦ R z x η ζ) (η - ζ + t • ζ)) :=
    (hD (k + 1)).comp (contDiff_id.prodMk contDiff_const)
  have hwz := hw z
  calc
    _ ≤ ‖Eζ‖ * ‖iteratedFDeriv ℝ i
        (fun x ↦ iteratedFDeriv ℝ (k + 1) (fun η ↦ R z x η ζ)
          (η - ζ + t • ζ)) x‖ := Eζ.norm_iteratedFDeriv_comp_left hs.contDiffAt (by simp)
    _ ≤ ‖ζ‖ * (C * w z * (1 + ‖η - ζ + t • ζ‖) ^ (-(k : ℝ)) *
        (1 + ‖ζ‖) ^ (-((N + k + 1 : ℕ) : ℝ))) := by
      exact mul_le_mul hEζ (hCb z x hx (η - ζ + t • ζ) ζ)
        (norm_nonneg _) (norm_nonneg ζ)
    _ ≤ (1 + ‖ζ‖) * (C * w z *
        ((1 + ‖η‖) ^ (-(k : ℝ)) * (1 + ‖ζ‖) ^ (k : ℝ)) *
          (1 + ‖ζ‖) ^ (-((N + k + 1 : ℕ) : ℝ))) := by
      gcongr
      · linarith
      · exact shifted_negative_frequency_weight_le η ζ t ht' k
    _ = C * w z * (1 + ‖η‖) ^ (-(k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
      have hp : 0 < 1 + ‖ζ‖ := by positivity
      have hpow : (1 + ‖ζ‖) * (1 + ‖ζ‖) ^ (k : ℝ) *
          (1 + ‖ζ‖) ^ (-((N + k + 1 : ℕ) : ℝ)) = (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
        calc
          _ = (1 + ‖ζ‖) ^ (1 : ℝ) * (1 + ‖ζ‖) ^ (k : ℝ) *
              (1 + ‖ζ‖) ^ (-((N + k + 1 : ℕ) : ℝ)) := by rw [Real.rpow_one]
          _ = (1 + ‖ζ‖) ^ ((1 : ℝ) + (k : ℝ) +
              (-((N + k + 1 : ℕ) : ℝ))) := by
            rw [← Real.rpow_add hp, ← Real.rpow_add hp]
          _ = _ := by
            congr 1
            push_cast
            ring
      calc
        _ = C * w z * (1 + ‖η‖) ^ (-(k : ℝ)) *
            ((1 + ‖ζ‖) * (1 + ‖ζ‖) ^ (k : ℝ) *
              (1 + ‖ζ‖) ^ (-((N + k + 1 : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hpow]

/-- The original mixed symbol derivative commutes with a constant real scalar. -/
private theorem symbolDerivative_const_real_smul
    {n r q : ℕ} (p : SymbolFunction n r q)
    (hp : ContDiff ℝ ∞ (Function.uncurry p)) (c : ℝ) (i k : ℕ)
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    symbolDerivative (fun x ξ ↦ c • p x ξ) i k x ξ = c • symbolDerivative p i k x ξ := by
  have heq : (fun x ↦ iteratedFDeriv ℝ k (fun ξ ↦ c • p x ξ) ξ) =
      fun x ↦ c • iteratedFDeriv ℝ k (p x) ξ := by
    funext x
    exact iteratedFDeriv_const_smul_apply'
      ((hp.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hs : ContDiff ℝ ∞ (fun x ↦ iteratedFDeriv ℝ k (p x) ξ) :=
    (contDiff_partial_iteratedFDeriv p hp k).comp (contDiff_id.prodMk contDiff_const)
  unfold symbolDerivative
  rw [heq, iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by simp))]

/-- The reduced symbol uses exactly the original ordered integrals and 2π normalization. -/
private theorem amplitudeSymbol_eq_integral
    {n r q : ℕ} (a : AmplitudeFunction n r q) (x η : EuclideanSpace ℝ (Fin n)) :
    amplitudeSymbol a x η = ((2 * Real.pi) ^ n)⁻¹ •
      ∫ ζ, ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ) := by
  unfold amplitudeSymbol
  rfl

/-- Fourier inversion identifies the actual zeroth Taylor coefficient with the diagonal. -/
private theorem integral_inner_frozen_frequency_eq_diagonal
    {n r q : ℕ} (a : AmplitudeFunction n r q) (ha : IsAmplitude 0 a)
    (hsupp : HasCompactSupport (Function.uncurry a))
    (x η : EuclideanSpace ℝ (Fin n)) :
    ((2 * Real.pi) ^ n)⁻¹ •
        ∫ ζ, ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y η =
      a x x η := by
  /- The compact input-position slice is the original amplitude at the fixed frequency.
  Fourier inversion after the prescribed 2π rescaling recovers its value at y=x. -/
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let K : Set V := Prod.snd '' tsupport (Function.uncurry a)
  have hK : IsCompact K := hsupp.image continuous_snd
  let f (y : V) : H := a x y η
  have hfs : ContDiff ℝ ∞ f :=
    ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hfc : HasCompactSupport f := by
    apply hK.of_isClosed_subset (isClosed_tsupport f)
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    have hz : a x y = 0 := image_eq_zero_of_notMem_tsupport (f := Function.uncurry a)
      (fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    apply hy
    change a x y η = 0
    rw [hz, Pi.zero_apply]
  let F : 𝓢(V, H) := hfc.toSchwartzMap hfs
  let d : ℝ := 2 * Real.pi
  have hd : 0 < d := mul_pos (by norm_num) Real.pi_pos
  let phase (x ζ : V) : ℂ := Complex.exp (Complex.I * (inner ℝ x ζ : ℂ))
  let G (ζ : V) : H := phase x ζ • (𝓕 F) (d⁻¹ • ζ)
  have hFourier (ζ : V) : (𝓕 F) (d⁻¹ • ζ) = ∫ y, phase (-y) ζ • f y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    simp only [phase, inner_neg_left, inner_smul_right]
    congr 1
    push_cast
    dsimp only [d]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hG (ζ : V) : G ζ =
      ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y η := by
    dsimp only [G]
    rw [hFourier, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_smul]
    congr 1
    simp only [phase, ← Complex.exp_add, inner_sub_left, inner_neg_left]
    congr 1
    push_cast
    ring
  have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure V) G d (hR := hd.le)
  have hnormalize : ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, G ζ = ∫ ζ, G (d • ζ) := by
    simpa only [V, finrank_euclideanSpace_fin, d] using hscale.symm
  have hscaled (ζ : V) : G (d • ζ) =
      Complex.exp (((2 * Real.pi * inner ℝ ζ x : ℝ) : ℂ) * Complex.I) • (𝓕 F) ζ := by
    dsimp only [G]
    rw [inv_smul_smul₀ hd.ne']
    congr 1
    simp only [phase, inner_smul_right, real_inner_comm x ζ]
    congr 1
    dsimp only [d]
    push_cast
    ring
  have hInv := congrArg (fun u : 𝓢(V, H) ↦ u x)
    (show (𝓕⁻ (𝓕 F) : 𝓢(V, H)) = F from FourierTransform.fourierInv_fourier_eq F)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hInv
  simp_rw [← hG]
  rw [hnormalize]
  simp_rw [hscaled]
  exact hInv

set_option maxHeartbeats 2000000 in
-- The existing dominated integral provider tracks the original nested multilinear jet targets.
/-- Integrate a uniformly dominated symbol family without unfolding its particular integrand. -/
private theorem exists_weighted_symbol_integral_bound
    {T : Type*} {n r q : ℕ}
    (B : T → EuclideanSpace ℝ (Fin n) → SymbolFunction n r q)
    (hB : ∀ z, ContDiff ℝ ∞
      (fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) ↦ B z p.2 p.1.1 p.1.2))
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → ∀ u v N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ η ζ,
        ‖symbolDerivative (B z ζ) u v x η‖ ≤
          C * w z * (1 + ‖η‖) ^ (-(v : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)))
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (fun x ξ ↦ ∫ ζ, B z ζ x ξ) i k x ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- The integrand remains abstract here. Its actual mixed jets are measurable and
  uniformly dominated on a compact spatial neighborhood times the whole frequency
  space. Apply the existing integral derivative identity, then integrate the bound. -/
  let V := EuclideanSpace ℝ (Fin n)
  have hBslice (z : T) (ζ : V) : ContDiff ℝ ∞ (Function.uncurry (B z ζ)) :=
    (hB z).comp (contDiff_id.prodMk contDiff_const)
  let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [V])
  have hnonneg (ζ : V) : 0 ≤ decay ζ := Real.rpow_nonneg (by positivity) _
  have hBmix (z : T) (u v : ℕ) : ContDiff ℝ ∞ (fun p : (V × V) × V ↦
      symbolDerivative (B z p.2) u v p.1.1 p.1.2) := by
    have hη : ContDiff ℝ ∞ (Function.uncurry
        (fun p : V × V ↦ fun η : V ↦ B z p.2 p.1 η)) :=
      (hB z).comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
    have hηjet : ContDiff ℝ ∞ (fun p : (V × V) × V ↦
        iteratedFDeriv ℝ v (B z p.2 p.1.1) p.1.2) :=
      (contDiff_partial_iteratedFDeriv _ hη v).comp
        ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
    have hx : ContDiff ℝ ∞ (Function.uncurry
        (fun p : V × V ↦ fun x : V ↦ iteratedFDeriv ℝ v (B z p.2 x) p.1)) :=
      hηjet.comp ((contDiff_snd.prodMk contDiff_fst.fst).prodMk contDiff_fst.snd)
    exact (contDiff_partial_iteratedFDeriv _ hx u).comp
      ((contDiff_fst.snd.prodMk contDiff_snd).prodMk contDiff_fst.fst)
  have hmeas (z : T) (u v : ℕ) (p : V × V) (_hp : p ∈ univ ×ˢ univ) :
      AEStronglyMeasurable (fun ζ ↦ symbolDerivative (B z ζ) u v p.1 p.2) := by
    -- The source is second countable; the nested jet target needs no countability search.
    have : SecondCountableTopologyEither V
        (V [×u]→L[ℝ] V [×v]→L[ℝ]
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) :=
      ⟨Or.inl (inferInstanceAs (SecondCountableTopology (EuclideanSpace ℝ (Fin n))))⟩
    exact ((hBmix z u v).continuous.comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)).aestronglyMeasurable
  have hdom (z : T) (u v : ℕ) (p : V × V) (_hp : p ∈ univ ×ˢ univ) :
      ∃ t : Set (V × V), t ∈ 𝓝 p ∧ t ⊆ univ ×ˢ univ ∧
        ∃ b : V → ℝ, Integrable b ∧
          ∀ᵐ ζ, ∀ y ∈ t, ‖symbolDerivative (B z ζ) u v y.1 y.2‖ ≤ b ζ := by
    obtain ⟨C, hC, hCb⟩ := hbound (Metric.closedBall p.1 1) (isCompact_closedBall _ _) u v
      (n + 1)
    refine ⟨Metric.closedBall p.1 1 ×ˢ univ,
      prod_mem_nhds (Metric.closedBall_mem_nhds p.1 (by norm_num)) univ_mem,
      prod_mono (subset_univ _) Subset.rfl, fun ζ ↦ C * w z * decay ζ,
      hdecay.const_mul _, Filter.Eventually.of_forall ?_⟩
    intro ζ y hy
    have hwz := hw z
    have hweight : (1 + ‖y.2‖) ^ (-(v : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y.2])
        (neg_nonpos.mpr (Nat.cast_nonneg v))
    calc
      _ ≤ C * w z * (1 + ‖y.2‖) ^ (-(v : ℝ)) * decay ζ := hCb z y.1 hy.1 y.2 ζ
      _ ≤ C * w z * 1 * decay ζ := by gcongr
      _ = _ := by rw [mul_one]
  obtain ⟨C, hC, hCb⟩ := hbound L hL i k (n + 1)
  refine ⟨C * (∫ ζ, decay ζ), mul_nonneg hC (integral_nonneg hnonneg), ?_⟩
  intro z x hx ξ
  rw [symbolDerivative_integral_of_locally_dominated_jets volume isOpen_univ
    (B z) (fun ζ ↦ (hBslice z ζ).contDiffOn) (hmeas z) (hdom z) i k (mem_univ x) ξ]
  calc
    _ ≤ ∫ ζ, C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) * decay ζ :=
      norm_integral_le_of_norm_le (hdecay.const_mul _)
        (Filter.Eventually.of_forall (hCb z x hx ξ))
    _ = C * (∫ ζ, decay ζ) * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      rw [integral_const_mul]
      ring

set_option maxHeartbeats 2000000 in
-- Keep the Taylor and scalar adapters abstract while preserving their original mixed jets.
/-- Integrate the actual inner difference through a small abstract reduction adapter. -/
private theorem exists_weighted_inner_remainder_integral_bound
    {T : Type*} {n r q : ℕ}
    (R : T → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hR : ∀ z, ContDiff ℝ ∞
      (fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) ↦ R z p.1.1 p.1.2 p.2))
    (c : ℝ) (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → ∀ u v M : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ η ζ,
        ‖iteratedFDeriv ℝ u
            (fun x ↦ iteratedFDeriv ℝ (v + 1) (fun η ↦ R z x η ζ) η) x‖ ≤
          C * w z * (1 + ‖η‖) ^ (-(v : ℝ)) * (1 + ‖ζ‖) ^ (-(M : ℝ)))
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative
          (fun x ξ ↦ ∫ ζ, c • (R z x ξ ζ - R z x (ξ - ζ) ζ)) i k x ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- Only the elaboration context is abstracted. The difference is formed from the same
  R at the original and frozen frequencies, with the same real normalization c. -/
  let V := EuclideanSpace ℝ (Fin n)
  let D (z : T) (ζ : V) : SymbolFunction n r q :=
    fun x η ↦ R z x η ζ - R z x (η - ζ) ζ
  let B (z : T) (ζ : V) : SymbolFunction n r q := fun x η ↦ c • D z ζ x η
  have hD (z : T) : ContDiff ℝ ∞
      (fun p : (V × V) × V ↦ D z p.2 p.1.1 p.1.2) :=
    (hR z).sub ((hR z).comp
      ((contDiff_fst.fst.prodMk (contDiff_fst.snd.sub contDiff_snd)).prodMk contDiff_snd))
  have hB (z : T) : ContDiff ℝ ∞
      (fun p : (V × V) × V ↦ B z p.2 p.1.1 p.1.2) := (hD z).const_smul c
  have hDb (K : Set V) (hK : IsCompact K) (u v N : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ η ζ,
        ‖symbolDerivative (D z ζ) u v x η‖ ≤
          C * w z * (1 + ‖η‖) ^ (-(v : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) :=
    exists_weighted_inner_taylor_difference_bound R hR w hw K u v N (hbound K hK u v)
  have hBb (K : Set V) (hK : IsCompact K) (u v N : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ η ζ,
        ‖symbolDerivative (B z ζ) u v x η‖ ≤
          C * w z * (1 + ‖η‖) ^ (-(v : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
    obtain ⟨C, hC, hCb⟩ := hDb K hK u v N
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, ?_⟩
    intro z x hx η ζ
    have hsD : ContDiff ℝ ∞ (Function.uncurry (D z ζ)) :=
      (hD z).comp (contDiff_id.prodMk contDiff_const)
    change ‖symbolDerivative (fun x η : V ↦ c • D z ζ x η) u v x η‖ ≤ _
    rw [symbolDerivative_const_real_smul (D z ζ) hsD c u v x η, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hCb z x hx η ζ) (norm_nonneg c)).trans_eq (by ring)
  exact exists_weighted_symbol_integral_bound B hB w hw hBb L hL i k

set_option maxHeartbeats 2000000 in
-- The actual remainder combines both integral identities and all mixed parameter jets.
/-- A common extra-frequency-derivative bound gives the same parameter factor in the actual
first amplitude remainder, in the weaker order-zero weights. -/
theorem exists_uniform_amplitudeSymbol_sub_diagonal_bound
    {T : Type*} {n r q : ℕ} (a : T → AmplitudeFunction n r q)
    (ha : ∀ z, IsAmplitude 0 (a z))
    (S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hS : IsCompact S)
    (hsupp : ∀ z, tsupport (Function.uncurry (a z)) ⊆ S)
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hbound : ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x y, (x, y) ∈ S → ∀ ξ,
      ‖amplitudeDerivative (a z) i j (k + 1) x y ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)))
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (amplitudeSymbol (a z) - (fun x ξ ↦ a z x x ξ)) i k x ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- The actual reduced symbol minus the actual diagonal is the normalized integral
  of its first inner Taylor difference. Uniform Fourier decay retains the supplied
  extra-frequency factor. The abstract adapter integrates the derivatives of that same
  difference; every original compact-support and smoothing term is retained. -/
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let c₀ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  let R (z : T) (x η ζ : V) : H :=
    ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a z x y (η + ζ)
  have hcompact (z : T) : HasCompactSupport (Function.uncurry (a z)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp z)
  have hR (z : T) : ContDiff ℝ ∞ (fun p : (V × V) × V ↦ R z p.1.1 p.1.2 p.2) :=
    (amplitude_reduction_estimates 0 (a z) (ha z) (hcompact z)).2.1
  let B (z : T) (ζ : V) : SymbolFunction n r q :=
    fun x η ↦ c₀ • (R z x η ζ - R z x (η - ζ) ζ)
  have hinner (K : Set V) (hK : IsCompact K) (u v M : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ η ζ,
        ‖iteratedFDeriv ℝ u
            (fun x ↦ iteratedFDeriv ℝ (v + 1) (fun η ↦ R z x η ζ) η) x‖ ≤
          C * w z * (1 + ‖η‖) ^ (-(v : ℝ)) * (1 + ‖ζ‖) ^ (-(M : ℝ)) :=
    exists_weighted_amplitude_inner_bound a ha S hS hsupp (v + 1) (-(v : ℝ))
      w hw (fun j l ↦ hbound j l v) K hK u M
  let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [V])
  have heq (z : T) (x η : V) :
      (amplitudeSymbol (a z) - (fun x η ↦ a z x x η)) x η = ∫ ζ, B z ζ x η := by
    have hi : Integrable (fun ζ ↦ R z x η ζ) :=
      integrable_amplitudeSymbol_outer 0 (a z) (ha z) (hcompact z) x η
    have hshift : Integrable (fun ζ ↦ R z x (η - ζ) ζ) := by
      obtain ⟨C, hC, hCb⟩ :=
        (amplitude_reduction_estimates 0 (a z) (ha z) (hcompact z)).2.2.1
          {x} isCompact_singleton 0 0 (n + 1)
      apply (hdecay.const_mul C).mono'
        (((hR z).continuous.comp
          ((continuous_const.prodMk (continuous_const.sub continuous_id)).prodMk
            continuous_id)).aestronglyMeasurable)
      apply Filter.Eventually.of_forall
      intro ζ
      simpa only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, Real.rpow_zero,
        mul_one, Function.comp_def, Pi.sub_apply, id_eq, R, decay, sub_add_cancel]
        using hCb x (mem_singleton x) (η - ζ) ζ
    have hdiag : c₀ • ∫ ζ, R z x (η - ζ) ζ = a z x x η := by
      simpa only [R, sub_add_cancel] using
        integral_inner_frozen_frequency_eq_diagonal (a z) (ha z) (hcompact z) x η
    have hactual : amplitudeSymbol (a z) x η = c₀ • ∫ ζ, R z x η ζ :=
      amplitudeSymbol_eq_integral (a z) x η
    simp only [Pi.sub_apply, hactual]
    rw [← hdiag, ← smul_sub, ← integral_sub hi hshift, integral_smul]
  have hfun (z : T) : (amplitudeSymbol (a z) - (fun x ξ ↦ a z x x ξ)) =
      fun x ξ ↦ ∫ ζ, B z ζ x ξ := funext (fun x ↦ funext (fun ξ ↦ heq z x ξ))
  simp_rw [hfun]
  exact exists_weighted_inner_remainder_integral_bound R hR c₀ w hw hinner L hL i k

/-- The matrix adjoint is the same isometry over the real differentiation field. -/
private def realMatrixAdjointIsometry (r q : ℕ) :
    (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) where
  toEquiv := ContinuousLinearMap.adjoint.toEquiv
  map_add' := map_add ContinuousLinearMap.adjoint
  map_smul' := by
    intro c A
    change (c • A).adjoint = c • A.adjoint
    rw [← Complex.coe_smul c A, map_smulₛₗ]
    simp
  norm_map' := ContinuousLinearMap.adjoint.norm_map

/-- Pointwise adjoint preserves each original mixed derivative norm. -/
private theorem norm_symbolDerivative_symbolAdjoint
    {n r q : ℕ} (p : SymbolFunction n r q) (i k : ℕ)
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    ‖symbolDerivative (symbolAdjoint p) i k x ξ‖ = ‖symbolDerivative p i k x ξ‖ := by
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let H' := EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)
  let J : H ≃ₗᵢ[ℝ] H' := realMatrixAdjointIsometry r q
  let Jk : (V [×k]→L[ℝ] H) ≃ₗᵢ[ℝ] (V [×k]→L[ℝ] H') := {
    toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
      (fun _ : Fin k ↦ V)).toLinearEquiv
    norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
  have heq : (fun x ↦ iteratedFDeriv ℝ k (symbolAdjoint p x) ξ) =
      Jk ∘ (fun x ↦ iteratedFDeriv ℝ k (p x) ξ) := by
    funext x
    exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
  unfold symbolDerivative
  rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]

/-- Frequency scaling cannot enlarge the original uniform spatial support. -/
private theorem tsupport_frequencyScaleSymbol_subset
    {n r q : ℕ} (p : SymbolFunction n r q) (t : ℝ) :
    tsupport (frequencyScaleSymbol t p) ⊆ tsupport p := by
  apply closure_minimal ?_ (isClosed_tsupport p)
  intro x hx
  by_contra hxp
  have hz : p x = 0 := image_eq_zero_of_notMem_tsupport hxp
  apply hx
  funext ξ
  change p x (t • ξ) = 0
  rw [hz, Pi.zero_apply]

/-- Choose the base scaling seminorm constant before the contraction parameter. -/
private theorem exists_uniform_frequencyScaleSymbol_bound
    {n r q : ℕ} (p : SymbolFunction n r q) (hp : IsSymbol univ 0 p)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (frequencyScaleSymbol t p) i k x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := hp.2 K (subset_univ _) hK i k
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x hx ξ
  have hderiv : symbolDerivative (frequencyScaleSymbol t p) i k x ξ =
      t ^ k • symbolDerivative p i k x (t • ξ) :=
    mixed_iteratedFDeriv_frequency_smul p t ht.ne' i k x ξ
  have hratio : t ^ k / (1 + t * ‖ξ‖) ^ k ≤ 1 / (1 + ‖ξ‖) ^ k := by
    apply (div_le_div_iff₀ (pow_pos (by positivity) k) (pow_pos (by positivity) k)).mpr
    have hcomparison := pow_le_pow_left₀
      (show 0 ≤ t * (1 + ‖ξ‖) by positivity)
      (show t * (1 + ‖ξ‖) ≤ 1 + t * ‖ξ‖ by nlinarith) k
    simpa only [mul_pow, one_mul] using hcomparison
  have hscaled : ‖symbolDerivative p i k x (t • ξ)‖ ≤
      C * (1 + ‖t • ξ‖) ^ (-(k : ℝ)) := by
    simpa only [zero_sub] using hCb x hx (t • ξ)
  calc
    _ = t ^ k * ‖symbolDerivative p i k x (t • ξ)‖ := by
      rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le k)]
    _ ≤ t ^ k * (C * (1 + ‖t • ξ‖) ^ (-(k : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (pow_nonneg ht.le k)
    _ = C * (t ^ k / (1 + t * ‖ξ‖) ^ k) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    _ ≤ C * (1 / (1 + ‖ξ‖) ^ k) := mul_le_mul_of_nonneg_left hratio hC
    _ = C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring

set_option maxHeartbeats 2000000 in
-- Uniform family constants are retained through bilinear derivatives at nested jet targets.
/-- Parameter-uniform version of the original separated bilinear amplitude estimate. -/
private theorem uniform_bilinear_amplitude_estimate
    {T : Type*} {n : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    ∀ {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (B : V →L[ℝ] W →L[ℝ] Z)
      (f : T → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → V)
      (g : T → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
      (l m : ℝ) (w₁ w₂ : T → ℝ),
      (∀ z, 0 ≤ w₁ z) → (∀ z, 0 ≤ w₂ z) →
      (∀ z, ContDiff ℝ ∞ (Function.uncurry (f z))) →
      (∀ z, ContDiff ℝ ∞ (Function.uncurry (g z))) →
      (∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ ξ,
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f z x) ξ) x‖ ≤
          C * w₁ z * (1 + ‖ξ‖) ^ (l - (j : ℝ))) →
      (∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, y ∈ L → ∀ ξ,
        ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (g z y) ξ) y‖ ≤
          C * w₂ z * (1 + ‖ξ‖) ^ (m - (j : ℝ))) →
      ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ y, y ∈ L → ∀ ξ,
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j
            (fun y ↦ iteratedFDeriv ℝ k (fun ξ ↦ B (f z x ξ) (g z y ξ)) ξ) y) x‖ ≤
          C * w₁ z * w₂ z * (1 + ‖ξ‖) ^ (l + m - (k : ℝ)) := by
  /- The original bilinear proof differentiates in frequency by Leibniz and leaves the
  spatial factors separated. Keep every chosen seminorm constant before the family
  parameter and carry its two nonnegative weights through that same induction. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let mixed {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  let triple {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : P → P → P → V) (i j k : ℕ) (x y ξ : P) :=
    iteratedFDeriv ℝ i
      (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ iteratedFDeriv ℝ k (a z w) ξ) y) x
  have parametric {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
    contDiff_partial_iteratedFDeriv f hf k
  have nested_isometry {V W : Type}
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (J : V ≃ₗᵢ[ℝ] W) (f : P → P → V) (i j : ℕ) (x y : P) :
      ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (J ∘ f z) y) x‖ =
        ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x‖ := by
    let Jj : (P [×j]→L[ℝ] V) ≃ₗᵢ[ℝ] (P [×j]→L[ℝ] W) := {
      toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
        (fun _ : Fin j ↦ P)).toLinearEquiv
      norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
    have heq : (fun z ↦ iteratedFDeriv ℝ j (J ∘ f z) y) =
        Jj ∘ (fun z ↦ iteratedFDeriv ℝ j (f z) y) := by
      funext z
      exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have mixed_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have mixed_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i : ℕ) (x ξ : P) :
      ‖mixed f i 0 x ξ‖ = ‖iteratedFDeriv ℝ i (fun y ↦ f y ξ) x‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ 0 (f y) ξ) =
        (continuousMultilinearCurryFin0 ℝ P V).symm ∘ (fun y ↦ f y ξ) := rfl
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have triple_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : P → P → P → V) (i j : ℕ) (x y ξ : P) :
      ‖triple a i j 0 x y ξ‖ =
        ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ a z w ξ) y) x‖ := by
    exact nested_isometry (continuousMultilinearCurryFin0 ℝ P V).symm
      (fun z w ↦ a z w ξ) i j x y
  have triple_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (a : P → P → P → V) (i j k : ℕ) (x y ξ : P) :
      ‖triple (fun z w η ↦ fderiv ℝ (a z w) η) i j k x y ξ‖ =
        ‖triple a i j (k + 1) x y ξ‖ := by
    unfold triple
    simp_rw [iteratedFDeriv_succ_eq_comp_right]
    exact (nested_isometry (continuousMultilinearCurryRightEquiv' ℝ k P V).symm
      (fun z w ↦ iteratedFDeriv ℝ k (fderiv ℝ (a z w)) ξ) i j x y).symm
  have nested_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f g : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (hg : ContDiff ℝ ∞ (Function.uncurry g)) (i j : ℕ) (x y : P) :
      iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ f z w + g z w) y) x =
        iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x +
          iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (g z) y) x := by
    have heq (z : P) : iteratedFDeriv ℝ j (fun w ↦ f z w + g z w) y =
        iteratedFDeriv ℝ j (f z) y + iteratedFDeriv ℝ j (g z) y :=
      iteratedFDeriv_add_apply
        (((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le (by simp))
        (((hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le (by simp))
    simp_rw [heq]
    exact iteratedFDeriv_add_apply
      ((((parametric f hf j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt).of_le
        (by simp))
      ((((parametric g hg j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt).of_le
        (by simp))
  have triple_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f g : P → P → P → V)
      (hf : ContDiff ℝ ∞ (fun z : (P × P) × P ↦ f z.1.1 z.1.2 z.2))
      (hg : ContDiff ℝ ∞ (fun z : (P × P) × P ↦ g z.1.1 z.1.2 z.2))
      (i j k : ℕ) (x y ξ : P) :
      triple (fun z w η ↦ f z w η + g z w η) i j k x y ξ =
        triple f i j k x y ξ + triple g i j k x y ξ := by
    have heq (z w : P) : iteratedFDeriv ℝ k (fun η ↦ f z w η + g z w η) ξ =
        iteratedFDeriv ℝ k (f z w) ξ + iteratedFDeriv ℝ k (g z w) ξ := by
      have hff : ContDiff ℝ ∞ (f z w) :=
        hf.comp ((contDiff_const (c := (z, w))).prodMk contDiff_id)
      have hgg : ContDiff ℝ ∞ (g z w) :=
        hg.comp ((contDiff_const (c := (z, w))).prodMk contDiff_id)
      exact iteratedFDeriv_add_apply (hff.contDiffAt.of_le (by simp))
        (hgg.contDiffAt.of_le (by simp))
    unfold triple
    simp_rw [heq]
    apply nested_add
    · exact (parametric (Function.uncurry f) hf k).comp (contDiff_id.prodMk contDiff_const)
    · exact (parametric (Function.uncurry g) hg k).comp (contDiff_id.prodMk contDiff_const)
  have estimate (k : ℕ) :
      ∀ {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (B : V →L[ℝ] W →L[ℝ] Z) (f : T → P → P → V) (g : T → P → P → W)
        (l m : ℝ) (w₁ w₂ : T → ℝ),
        (∀ z, 0 ≤ w₁ z) → (∀ z, 0 ≤ w₂ z) →
        (∀ z, ContDiff ℝ ∞ (Function.uncurry (f z))) →
        (∀ z, ContDiff ℝ ∞ (Function.uncurry (g z))) →
        (∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ ξ,
          ‖mixed (f z) i j x ξ‖ ≤ C * w₁ z * (1 + ‖ξ‖) ^ (l - (j : ℝ))) →
        (∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, y ∈ L → ∀ ξ,
          ‖mixed (g z) i j y ξ‖ ≤ C * w₂ z * (1 + ‖ξ‖) ^ (m - (j : ℝ))) →
        ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ y, y ∈ L → ∀ ξ,
          ‖triple (fun x y ξ ↦ B (f z x ξ) (g z y ξ)) i j k x y ξ‖ ≤
            C * w₁ z * w₂ z * (1 + ‖ξ‖) ^ (l + m - (k : ℝ)) := by
    induction k with
    | zero =>
      intro V W Z _ _ _ _ _ _ B f g l m w₁ w₂ hw₁ hw₂ hf hg hfb hgb i j
      obtain ⟨C, hC, hfc⟩ := hfb i 0
      obtain ⟨D, hD, hgd⟩ := hgb j 0
      refine ⟨‖B‖ * C * D, mul_nonneg (mul_nonneg (norm_nonneg _) hC) hD, ?_⟩
      intro z x hx y hy ξ
      have hwf := hw₁ z
      have hwg := hw₂ z
      rw [triple_zero]
      let d := iteratedFDeriv ℝ j (fun y ↦ g z y ξ) y
      let A : V →L[ℝ] P [×j]→L[ℝ] Z :=
        ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
          (fun _ : Fin j ↦ P) W Z).flip d).comp B
      have hgf : ContDiff ℝ ∞ (fun y ↦ g z y ξ) :=
        (hg z).comp (contDiff_id.prodMk contDiff_const)
      have hff : ContDiff ℝ ∞ (fun x ↦ f z x ξ) :=
        (hf z).comp (contDiff_id.prodMk contDiff_const)
      have heq : (fun x ↦ iteratedFDeriv ℝ j (fun y ↦ B (f z x ξ) (g z y ξ)) y) =
          A ∘ (fun x ↦ f z x ξ) := by
        funext x
        exact (B (f z x ξ)).iteratedFDeriv_comp_left hgf.contDiffAt (by simp)
      have hA : ‖A‖ ≤ ‖B‖ * ‖d‖ := by
        apply A.opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro v
        calc
          ‖A v‖ ≤ ‖B v‖ * ‖d‖ := (B v).norm_compContinuousMultilinearMap_le d
          _ ≤ (‖B‖ * ‖v‖) * ‖d‖ :=
            mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg _)
          _ = _ := by ring
      rw [heq]
      have hbound := A.norm_iteratedFDeriv_comp_left hff.contDiffAt (x := x) (n := i)
        (by simp)
      have hc := hfc z x hx ξ
      have hd := hgd z y hy ξ
      simp only [mixed_zero, Nat.cast_zero, sub_zero] at hc hd
      simp only [Nat.cast_zero, sub_zero]
      apply hbound.trans
      calc
        ‖A‖ * ‖iteratedFDeriv ℝ i (fun x ↦ f z x ξ) x‖ ≤
            (‖B‖ * ‖d‖) * (C * w₁ z * (1 + ‖ξ‖) ^ l) :=
          mul_le_mul hA hc (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ (‖B‖ * (D * w₂ z * (1 + ‖ξ‖) ^ m)) *
            (C * w₁ z * (1 + ‖ξ‖) ^ l) := by
          gcongr
        _ = _ := by
          rw [Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖)]
          ring
    | succ k ih =>
      intro V W Z _ _ _ _ _ _ B f g l m w₁ w₂ hw₁ hw₂ hf hg hfb hgb i j
      let df : T → P → P → P →L[ℝ] V := fun z x ξ ↦ fderiv ℝ (f z x) ξ
      let dg : T → P → P → P →L[ℝ] W := fun z y ξ ↦ fderiv ℝ (g z y) ξ
      have hdf (z : T) : ContDiff ℝ ∞ (Function.uncurry (df z)) := by
        have h : ContDiff ℝ ∞ (fun p : (P × P) × P ↦ f z p.1.1 p.2) :=
          (hf z).comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact h.fderiv contDiff_snd (by simp)
      have hdg (z : T) : ContDiff ℝ ∞ (Function.uncurry (dg z)) := by
        have h : ContDiff ℝ ∞ (fun p : (P × P) × P ↦ g z p.1.1 p.2) :=
          (hg z).comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact h.fderiv contDiff_snd (by simp)
      have hdfb : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ K → ∀ ξ,
          ‖mixed (df z) a b x ξ‖ ≤ C * w₁ z * (1 + ‖ξ‖) ^ ((l - 1) - (b : ℝ)) := by
        intro a b
        obtain ⟨C, hC, hbound⟩ := hfb a (b + 1)
        refine ⟨C, hC, ?_⟩
        intro z x hx ξ
        have h := hbound z x hx ξ
        rw [← mixed_shift] at h
        have hexp : l - ((b + 1 : ℕ) : ℝ) = l - 1 - (b : ℝ) := by
          push_cast
          ring
        rw [hexp] at h
        exact h
      have hdgb : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, y ∈ L → ∀ ξ,
          ‖mixed (dg z) a b y ξ‖ ≤ C * w₂ z * (1 + ‖ξ‖) ^ ((m - 1) - (b : ℝ)) := by
        intro a b
        obtain ⟨C, hC, hbound⟩ := hgb a (b + 1)
        refine ⟨C, hC, ?_⟩
        intro z y hy ξ
        have h := hbound z y hy ξ
        rw [← mixed_shift] at h
        have hexp : m - ((b + 1 : ℕ) : ℝ) = m - 1 - (b : ℝ) := by
          push_cast
          ring
        rw [hexp] at h
        exact h
      let p₁ : T → P → P → P → P →L[ℝ] Z :=
        fun z x y ξ ↦ B.precompR P (f z x ξ) (dg z y ξ)
      let p₂ : T → P → P → P → P →L[ℝ] Z :=
        fun z x y ξ ↦ B.precompL P (df z x ξ) (g z y ξ)
      obtain ⟨C, hC, h₁⟩ := ih (B.precompR P) f dg l (m - 1) w₁ w₂ hw₁ hw₂
        hf hdg hfb hdgb i j
      obtain ⟨D, hD, h₂⟩ := ih (B.precompL P) df g (l - 1) m w₁ w₂ hw₁ hw₂
        hdf hg hdfb hgb i j
      refine ⟨C + D, add_nonneg hC hD, ?_⟩
      intro z x hx y hy ξ
      have hp₁ : ContDiff ℝ ∞ (fun p : (P × P) × P ↦ p₁ z p.1.1 p.1.2 p.2) :=
        (B.precompR P).isBoundedBilinearMap.contDiff.comp₂
          ((hf z).comp (contDiff_fst.fst.prodMk contDiff_snd))
          ((hdg z).comp (contDiff_fst.snd.prodMk contDiff_snd))
      have hp₂ : ContDiff ℝ ∞ (fun p : (P × P) × P ↦ p₂ z p.1.1 p.1.2 p.2) :=
        (B.precompL P).isBoundedBilinearMap.contDiff.comp₂
          ((hdf z).comp (contDiff_fst.fst.prodMk contDiff_snd))
          ((hg z).comp (contDiff_fst.snd.prodMk contDiff_snd))
      have heq : (fun x y η ↦ fderiv ℝ (fun η ↦ B (f z x η) (g z y η)) η) =
          (fun x y η ↦ p₁ z x y η + p₂ z x y η) := by
        funext x y η
        exact B.fderiv_of_bilinear
          ((((hf z).comp (contDiff_const.prodMk contDiff_id)).contDiffAt).differentiableAt
            (by simp))
          ((((hg z).comp (contDiff_const.prodMk contDiff_id)).contDiffAt).differentiableAt
            (by simp))
      rw [← triple_shift, heq, triple_add (p₁ z) (p₂ z) hp₁ hp₂]
      have h := (norm_add_le _ _).trans
        (add_le_add (h₁ z x hx y hy ξ) (h₂ z x hx y hy ξ))
      have he₁ : l + (m - 1) - (k : ℝ) = l + m - ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have he₂ : (l - 1) + m - (k : ℝ) = l + m - ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he₁, he₂] at h
      convert h using 1
      ring
  intro V W Z _ _ _ _ _ _ B f g l m w₁ w₂ hw₁ hw₂ hf hg hfb hgb i j
  exact estimate k (V := V) (W := W) (Z := Z) B f g l m w₁ w₂ hw₁ hw₂
    hf hg hfb hgb i j

/-- Frequency scaling preserves the same uniform compact spatial-pair support. -/
private theorem tsupport_frequencyScaleAmplitude_subset
    {n r q : ℕ} (a : AmplitudeFunction n r q) (t : ℝ) :
    tsupport (Function.uncurry (frequencyScaleAmplitude t a)) ⊆
      tsupport (Function.uncurry a) := by
  apply closure_minimal ?_ (isClosed_tsupport (Function.uncurry a))
  intro z hz
  by_contra hzS
  have hz0 : Function.uncurry a z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry a) hzS
  apply hz
  funext ξ
  change a z.1 z.2 (t • ξ) = 0
  simpa only [Function.uncurry, Pi.zero_apply] using congrFun hz0 (t • ξ)

/-- The original left-right amplitude stays inside the two prescribed closed spatial supports. -/
private theorem tsupport_leftRightAmplitude_subset_product
    {n r s q : ℕ} (p : SymbolFunction n s q) (a : SymbolFunction n r s)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K) (hL : IsClosed L)
    (hp : tsupport p ⊆ K) (ha : tsupport a ⊆ L) :
    tsupport (Function.uncurry (leftRightAmplitude p a)) ⊆ K ×ˢ L := by
  apply closure_minimal ?_ (hK.prod hL)
  intro z hz
  constructor
  · by_contra hzK
    have hzero : p z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hx ↦ hzK (hp hx))
    apply hz
    funext ξ
    simp [Function.uncurry, leftRightAmplitude, hzero]
  · by_contra hzL
    have hzero : a z.2 = 0 := image_eq_zero_of_notMem_tsupport (fun hy ↦ hzL (ha hy))
    apply hz
    funext ξ
    simp [Function.uncurry, leftRightAmplitude, hzero]

set_option maxHeartbeats 2000000 in
-- The same Fourier estimate retains its nonnegative parameter factor after integration.
/-- A common amplitude weight remains in the actual reduced symbol's mixed bounds. -/
private theorem exists_weighted_amplitudeSymbol_bound
    {T : Type*} {n r q : ℕ} (a : T → AmplitudeFunction n r q)
    (ha : ∀ z, IsAmplitude 0 (a z))
    (S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hS : IsCompact S)
    (hsupp : ∀ z, tsupport (Function.uncurry (a z)) ⊆ S)
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hbound : ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z x y, (x, y) ∈ S → ∀ ξ,
      ‖amplitudeDerivative (a z) i j k x y ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)))
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (amplitudeSymbol (a z)) i k x ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- Use the same actual inner jets and integral derivative identity as the unweighted
  estimate. Keep w outside both the Fourier-decay constant and the final integral. -/
  let V := EuclideanSpace ℝ (Fin n)
  let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [V])
  have hnonneg (ζ : V) : 0 ≤ decay ζ := Real.rpow_nonneg (by positivity) _
  obtain ⟨C, hC, hCb⟩ := exists_weighted_amplitude_inner_bound a ha S hS hsupp k
    (-(k : ℝ)) w hw (fun u v ↦ hbound u v k) L hL i (n + 1)
  let c₀ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  refine ⟨‖c₀‖ * C * (∫ ζ, decay ζ), by positivity, ?_⟩
  intro z x hx ξ
  have hcompact : HasCompactSupport (Function.uncurry (a z)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp z)
  rw [(amplitude_reduction_estimates 0 (a z) (ha z) hcompact).2.2.2.2 i k x ξ,
    norm_smul]
  have hboundIntegral :
      ‖∫ ζ, iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦
            ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) •
              a z x y (η + ζ)) ξ) x‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) * (∫ ζ, decay ζ) := by
    calc
      _ ≤ ∫ ζ, C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) * decay ζ :=
        norm_integral_le_of_norm_le (hdecay.const_mul _)
          (Filter.Eventually.of_forall (hCb z x hx ξ))
      _ = _ := integral_const_mul _ _
  exact (mul_le_mul_of_nonneg_left hboundIntegral (norm_nonneg c₀)).trans_eq (by ring)

/-- The two original ordered Bochner integrals are additive when each input is integrable. -/
private theorem amplitudeSymbol_add
    {n r q : ℕ} (a b : AmplitudeFunction n r q)
    (ha : IsAmplitude 0 a) (hb : IsAmplitude 0 b)
    (hca : HasCompactSupport (Function.uncurry a))
    (hcb : HasCompactSupport (Function.uncurry b)) :
    amplitudeSymbol (a + b) = amplitudeSymbol a + amplitudeSymbol b := by
  funext x η
  simp only [Pi.add_apply, amplitudeSymbol_eq_integral]
  have hinner (ζ : EuclideanSpace ℝ (Fin n)) :
      (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) •
        (a x y (η + ζ) + b x y (η + ζ))) =
      (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)) +
        ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • b x y (η + ζ) := by
    simp only [smul_add]
    exact integral_add (integrable_amplitudeSymbol_inner 0 a ha hca x η ζ)
      (integrable_amplitudeSymbol_inner 0 b hb hcb x η ζ)
  simp_rw [hinner]
  rw [integral_add (integrable_amplitudeSymbol_outer 0 a ha hca x η)
    (integrable_amplitudeSymbol_outer 0 b hb hcb x η), smul_add]

/-- Smooth original mixed symbol derivatives commute with pointwise addition. -/
private theorem symbolDerivative_add_of_contDiff
    {n r q : ℕ} (p a : SymbolFunction n r q)
    (hp : ContDiff ℝ ∞ (Function.uncurry p))
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (i k : ℕ) (x ξ : EuclideanSpace ℝ (Fin n)) :
    symbolDerivative (p + a) i k x ξ =
      symbolDerivative p i k x ξ + symbolDerivative a i k x ξ := by
  have hfreq (x : EuclideanSpace ℝ (Fin n)) :
      iteratedFDeriv ℝ k ((p + a) x) ξ =
        iteratedFDeriv ℝ k (p x) ξ + iteratedFDeriv ℝ k (a x) ξ :=
    iteratedFDeriv_add_apply
      ((hp.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
      ((ha.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  unfold symbolDerivative
  simp_rw [hfreq]
  exact iteratedFDeriv_add_apply
    (((contDiff_partial_iteratedFDeriv p hp k).comp
      (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp))
    (((contDiff_partial_iteratedFDeriv a ha k).comp
      (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp))

/-- Two exact symbol families with common weighted bounds have a common weighted sum bound. -/
private theorem exists_weighted_symbol_add_bound
    {T : Type*} {n r q : ℕ} (p a : T → SymbolFunction n r q)
    (hp : ∀ z, ContDiff ℝ ∞ (Function.uncurry (p z)))
    (ha : ∀ z, ContDiff ℝ ∞ (Function.uncurry (a z)))
    (w : T → ℝ) (L : Set (EuclideanSpace ℝ (Fin n))) (i k : ℕ)
    (hpb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (p z) i k x ξ‖ ≤ C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)))
    (hab : ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (a z) i k x ξ‖ ≤ C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (p z + a z) i k x ξ‖ ≤
        C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := hpb
  obtain ⟨D, hD, hDb⟩ := hab
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro z x hx ξ
  rw [symbolDerivative_add_of_contDiff (p z) (a z) (hp z) (ha z)]
  exact ((norm_add_le _ _).trans (add_le_add (hCb z x hx ξ) (hDb z x hx ξ))).trans_eq
    (by ring)

set_option maxHeartbeats 2000000 in
-- Preserve the exact two amplitude reductions while choosing every constant before the scale.
/-- The original composition symbol differs from the ordered scaled product by a common
first-order parameter bound in every order-zero mixed seminorm. -/
theorem exists_compositionSymbol_frequencyScale_sub_bound
    {n r s q : ℕ} (p : SymbolFunction n s q) (a : SymbolFunction n r s)
    (hp : IsSymbol Set.univ 0 p) (ha : IsSymbol Set.univ 0 a)
    (hpSupp : HasCompactSupport p) (haSupp : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχone : ∀ x ∈ tsupport a, χ x = 1)
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x ∈ L, ∀ ξ,
      ‖symbolDerivative
          (compositionSymbol χ (frequencyScaleSymbol h p) (frequencyScaleSymbol h a) -
            symbolComp (frequencyScaleSymbol h p) (frequencyScaleSymbol h a)) i j x ξ‖ ≤
        C * h * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
  /- First reduce the actual scaled adjoint amplitude. Its diagonal is the original
  pointwise adjoint, and the first remainder bounds the actual right-symbol difference δ.
  By linearity of the same two Bochner integrals, the full composition then splits into
  the reduction of the original scaled left-right amplitude and the reduction containing
  δ. The first part uses its extra frequency derivative; the second uses δ's weighted
  amplitude bounds. This retains both reductions and all their smoothing contributions. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let T := {h : ℝ // 0 < h ∧ h ≤ 1}
  let ph : T → SymbolFunction n s q := fun h ↦ frequencyScaleSymbol h.val p
  let ah : T → SymbolFunction n r s := fun h ↦ frequencyScaleSymbol h.val a
  have hph (h : T) : IsSymbol univ 0 (ph h) :=
    hp.frequencyScale h.val h.property.1 h.property.2
  have hah (h : T) : IsSymbol univ 0 (ah h) :=
    ha.frequencyScale h.val h.property.1 h.property.2
  have hcph (h : T) : HasCompactSupport (ph h) :=
    hpSupp.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_frequencyScaleSymbol_subset p h.val)
  have hcah (h : T) : HasCompactSupport (ah h) :=
    haSupp.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_frequencyScaleSymbol_subset a h.val)
  have hχscaled (h : T) : ∀ x ∈ tsupport (ah h), χ x = 1 :=
    fun x hx ↦ hχone x (tsupport_frequencyScaleSymbol_subset a h.val hx)
  -- Combine the accepted scaling estimate and the first remainder on one original amplitude.
  have scaledRemainder {r' q' : ℕ} (b : AmplitudeFunction n r' q')
      (hb : IsAmplitude 0 b) (hcb : HasCompactSupport (Function.uncurry b))
      (K : Set V) (hK : IsCompact K) (u v : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ K → ∀ ξ,
        ‖symbolDerivative (amplitudeSymbol (frequencyScaleAmplitude h.val b) -
            (fun x ξ ↦ frequencyScaleAmplitude h.val b x x ξ)) u v x ξ‖ ≤
          C * h.val * (1 + ‖ξ‖) ^ (-(v : ℝ)) := by
    let family : T → AmplitudeFunction n r' q' :=
      fun h ↦ frequencyScaleAmplitude h.val b
    let S := tsupport (Function.uncurry b)
    have hfamily (h : T) : IsAmplitude 0 (family h) :=
      hb.frequencyScale h.val h.property.1 h.property.2
    have hsupp (h : T) : tsupport (Function.uncurry (family h)) ⊆ S :=
      tsupport_frequencyScaleAmplitude_subset b h.val
    have hbound : ∀ u v k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x y,
        (x, y) ∈ S → ∀ ξ,
          ‖amplitudeDerivative (family h) u v (k + 1) x y ξ‖ ≤
            C * h.val * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      intro u v k
      obtain ⟨C, hC, hCb⟩ := hb.exists_frequencyScale_derivative_bound S hcb u v k
      exact ⟨C, hC, fun h x y hxy ξ ↦
        hCb h.val h.property.1 h.property.2 x y hxy ξ⟩
    exact exists_uniform_amplitudeSymbol_sub_diagonal_bound family hfamily S hcb hsupp
      (fun h : T ↦ h.val) (fun h ↦ h.property.1.le) hbound K hK u v
  -- The actual right symbol is the adjoint of the actual reduced adjoint symbol.
  let rSym : T → SymbolFunction n r s := fun h ↦ symbolAdjoint (adjointSymbol χ (ah h))
  let δ : T → SymbolFunction n r s := fun h ↦ rSym h - ah h
  have hδadj (h : T) : δ h =
      symbolAdjoint (adjointSymbol χ (ah h) - symbolAdjoint (ah h)) := by
    funext x ξ
    simp only [δ, rSym, Pi.sub_apply, symbolAdjoint, map_sub,
      ContinuousLinearMap.adjoint_adjoint]
  have hδsymbol (h : T) : IsSymbol univ 0 (δ h) := by
    rw [hδadj h]
    have hsub := isSymbol_adjointSymbol_sub 0 (ah h) (hah h) (hcah h) χ hχ hcχ
      (hχscaled h)
    exact IsSymbol.symbolAdjoint isOpen_univ (hsub.mono (by norm_num))
  have hAdjScale (h : T) : frequencyScaleAmplitude h.val (adjointAmplitude χ a) =
      adjointAmplitude χ (ah h) := rfl
  have hAdjDiag (h : T) : (fun x ξ ↦ adjointAmplitude χ (ah h) x x ξ) =
      symbolAdjoint (ah h) := by
    funext x ξ
    by_cases hx : x ∈ tsupport a
    · simp only [adjointAmplitude, symbolAdjoint, hχone x hx, one_smul]
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [adjointAmplitude, symbolAdjoint, ah, frequencyScaleSymbol, hz]
  have hδbound (K : Set V) (hK : IsCompact K) (u v : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ K → ∀ ξ,
        ‖symbolDerivative (δ h) u v x ξ‖ ≤
          C * h.val * (1 + ‖ξ‖) ^ (-(v : ℝ)) := by
    obtain ⟨C, hC, hCb⟩ := scaledRemainder (adjointAmplitude χ a)
      (isAmplitude_adjointAmplitude 0 a ha χ hχ)
      (hasCompactSupport_adjointAmplitude a haSupp χ hcχ) K hK u v
    refine ⟨C, hC, ?_⟩
    intro h x hx ξ
    rw [hδadj h, norm_symbolDerivative_symbolAdjoint]
    simpa only [adjointSymbol, hAdjScale, hAdjDiag] using hCb h x hx ξ
  -- All actual δ symbols have the same compact spatial control.
  let Kδ : Set V := tsupport χ ∪ tsupport a
  have hKδ : IsCompact Kδ := hcχ.union haSupp
  have hδsupp (h : T) : tsupport (δ h) ⊆ Kδ := by
    have hr : tsupport (rSym h) ⊆ tsupport χ := by
      simpa only [rSym, tsupport_symbolAdjoint] using
        tsupport_adjointSymbol_subset χ (ah h)
    exact (tsupport_sub (rSym h) (ah h)).trans
      (union_subset_union hr (tsupport_frequencyScaleSymbol_subset a h.val))
  let S : Set (V × V) := tsupport p ×ˢ Kδ
  have hS : IsCompact S := hpSupp.prod hKδ
  let β : T → AmplitudeFunction n r q := fun h ↦ leftRightAmplitude (ph h) (ah h)
  let θ : T → AmplitudeFunction n r q := fun h ↦ leftRightAmplitude (ph h) (δ h)
  have hβ (h : T) : IsAmplitude 0 (β h) := by
    simpa only [zero_add] using isAmplitude_leftRightAmplitude 0 0 (ph h) (ah h)
      (hph h) (hah h)
  have hcβ (h : T) : HasCompactSupport (Function.uncurry (β h)) :=
    hasCompactSupport_leftRightAmplitude (ph h) (ah h) (hcph h) (hcah h)
  have hθ (h : T) : IsAmplitude 0 (θ h) := by
    simpa only [zero_add] using isAmplitude_leftRightAmplitude 0 0 (ph h) (δ h)
      (hph h) (hδsymbol h)
  have hθsupp (h : T) : tsupport (Function.uncurry (θ h)) ⊆ S :=
    tsupport_leftRightAmplitude_subset_product (ph h) (δ h) (tsupport p) Kδ
      (isClosed_tsupport _) hKδ.isClosed (tsupport_frequencyScaleSymbol_subset p h.val)
      (hδsupp h)
  have hcθ (h : T) : HasCompactSupport (Function.uncurry (θ h)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hθsupp h)
  -- Weighted bilinearity controls the original second reduction containing δ.
  have hθbound : ∀ u v k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x y,
      (x, y) ∈ S → ∀ ξ,
        ‖amplitudeDerivative (θ h) u v k x y ξ‖ ≤
          C * h.val * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    intro u v k
    let B := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace ℂ (Fin s)) (EuclideanSpace ℂ (Fin q))).bilinearRestrictScalars ℝ
    have hps (h : T) : ContDiff ℝ ∞ (Function.uncurry (ph h)) := by
      simpa only [univ_prod_univ, contDiffOn_univ] using (hph h).1
    have hδs (h : T) : ContDiff ℝ ∞ (Function.uncurry (δ h)) := by
      simpa only [univ_prod_univ, contDiffOn_univ] using (hδsymbol h).1
    have hfb : ∀ u v : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x,
        x ∈ Prod.fst '' S → ∀ ξ,
          ‖iteratedFDeriv ℝ u (fun x ↦ iteratedFDeriv ℝ v (ph h x) ξ) x‖ ≤
            C * (fun _ : T ↦ (1 : ℝ)) h * (1 + ‖ξ‖) ^ (0 - (v : ℝ)) := by
      intro u v
      obtain ⟨C, hC, hCb⟩ := exists_uniform_frequencyScaleSymbol_bound p hp
        (Prod.fst '' S) (hS.image continuous_fst) u v
      refine ⟨C, hC, ?_⟩
      intro h x hx ξ
      simpa only [symbolDerivative, mul_one, zero_sub] using
        hCb h.val h.property.1 h.property.2 x hx ξ
    have hgb : ∀ u v : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ y,
        y ∈ Prod.snd '' S → ∀ ξ,
          ‖iteratedFDeriv ℝ u (fun y ↦ iteratedFDeriv ℝ v (δ h y) ξ) y‖ ≤
            C * h.val * (1 + ‖ξ‖) ^ (0 - (v : ℝ)) := by
      intro u v
      simpa only [symbolDerivative, zero_sub] using
        hδbound (Prod.snd '' S) (hS.image continuous_snd) u v
    obtain ⟨C, hC, hCb⟩ := uniform_bilinear_amplitude_estimate
      (Prod.fst '' S) (Prod.snd '' S) k B ph δ 0 0 (fun _ ↦ 1) (fun h ↦ h.val)
      (fun _ ↦ zero_le_one) (fun h ↦ h.property.1.le) hps hδs hfb hgb u v
    have hmodel (h : T) : θ h = fun x y ξ ↦ B (ph h x ξ) (δ h y ξ) := by
      funext x y ξ
      rfl
    refine ⟨C, hC, ?_⟩
    intro h x y hxy ξ
    rw [hmodel h]
    simpa only [amplitudeDerivative, zero_add, zero_sub, mul_one]
      using hCb h x ⟨(x, y), hxy, rfl⟩ y ⟨(x, y), hxy, rfl⟩ ξ
  let F : T → SymbolFunction n r q :=
    fun h ↦ amplitudeSymbol (β h) - symbolComp (ph h) (ah h)
  let G : T → SymbolFunction n r q := fun h ↦ amplitudeSymbol (θ h)
  have hFb : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (F h) i j x ξ‖ ≤
        C * h.val * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
    have hfixed : IsAmplitude 0 (leftRightAmplitude p a) := by
      simpa only [zero_add] using isAmplitude_leftRightAmplitude 0 0 p a hp ha
    have hcFixed := hasCompactSupport_leftRightAmplitude p a hpSupp haSupp
    have hscale (h : T) : frequencyScaleAmplitude h.val (leftRightAmplitude p a) =
        β h := rfl
    have hdiag (h : T) : (fun x ξ ↦ β h x x ξ) = symbolComp (ph h) (ah h) := rfl
    simpa only [F, hscale, hdiag] using
      scaledRemainder (leftRightAmplitude p a) hfixed hcFixed L hL i j
  have hGb : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (G h) i j x ξ‖ ≤
        C * h.val * (1 + ‖ξ‖) ^ (-(j : ℝ)) :=
    exists_weighted_amplitudeSymbol_bound θ hθ S hS hθsupp (fun h : T ↦ h.val)
      (fun h ↦ h.property.1.le) hθbound L hL i j
  -- Add the two actual symbol families after verifying the exact integral decomposition.
  have hFs (h : T) : ContDiff ℝ ∞ (Function.uncurry (F h)) := by
    have h1 := isSymbol_amplitudeSymbol 0 (β h) (hβ h) (hcβ h)
    have h2 := IsSymbol.symbolComp isOpen_univ (hph h) (hah h)
    have hs1 : ContDiff ℝ ∞ (Function.uncurry (amplitudeSymbol (β h))) := by
      simpa only [univ_prod_univ, contDiffOn_univ] using h1.1
    have hs2 : ContDiff ℝ ∞ (Function.uncurry (symbolComp (ph h) (ah h))) := by
      simpa only [univ_prod_univ, contDiffOn_univ] using h2.1
    exact hs1.sub hs2
  have hGs (h : T) : ContDiff ℝ ∞ (Function.uncurry (G h)) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using
      (isSymbol_amplitudeSymbol 0 (θ h) (hθ h) (hcθ h)).1
  have hsplit (h : T) :
      compositionSymbol χ (ph h) (ah h) - symbolComp (ph h) (ah h) = F h + G h := by
    have hAmp : leftRightAmplitude (ph h) (rSym h) = β h + θ h := by
      funext x y ξ
      simp only [β, θ, leftRightAmplitude, Pi.add_apply, δ, Pi.sub_apply,
        ContinuousLinearMap.comp_sub]
      abel
    have hactual : compositionSymbol χ (ph h) (ah h) =
        amplitudeSymbol (β h) + amplitudeSymbol (θ h) := by
      unfold compositionSymbol
      change amplitudeSymbol (leftRightAmplitude (ph h) (rSym h)) = _
      rw [hAmp, amplitudeSymbol_add (β h) (θ h) (hβ h) (hθ h) (hcβ h) (hcθ h)]
    rw [hactual]
    dsimp only [F, G]
    abel
  have htarget : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ L → ∀ ξ,
      ‖symbolDerivative (compositionSymbol χ (ph h) (ah h) -
          symbolComp (ph h) (ah h)) i j x ξ‖ ≤
        C * h.val * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
    simp_rw [hsplit]
    exact exists_weighted_symbol_add_bound F G hFs hGs (fun h : T ↦ h.val) L i j hFb hGb
  obtain ⟨C, hC, hCb⟩ := htarget
  exact ⟨C, hC, fun h hh hh₁ x hx ξ ↦ hCb ⟨h, hh, hh₁⟩ x hx ξ⟩

end AtiyahSinger
