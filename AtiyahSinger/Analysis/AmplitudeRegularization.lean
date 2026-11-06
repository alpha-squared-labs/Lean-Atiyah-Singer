/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Removing smooth frequency regularizations of compact amplitudes

Public module ID: M0076.

Spatially dependent invertible linear frequency substitutions preserve uniform derivative
bounds for a compact frequency cutoff. Fourier decay then provides a common integrable
majorant for the original iterated amplitude integrals. This permits removal of frequency
regularizations without assuming absolute integrability of the unregularized joint integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Filter Set
open scoped ContDiff FourierTransform SchwartzMap

set_option maxSynthPendingDepth 20

/-- A compact frequency cutoff has uniformly bounded spatial derivatives after an invertible
linear frequency substitution, including all constant frequency rescalings. -/
private theorem exists_uniform_bound_iteratedFDeriv_frequency_cutoff
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {n : ℕ} (τ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hτ : ContDiff ℝ ∞ τ) (hcτ : HasCompactSupport τ)
    (W : Set Z) (hW : IsOpen W)
    (Θ : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hΘ : ContDiffOn ℝ ∞ Θ W) (hinv : ∀ z ∈ W, (Θ z).IsInvertible)
    (K : Set Z) (hK : IsCompact K) (hKW : K ⊆ W) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ k (fun w ↦ τ (Θ w ξ)) z‖ ≤ C := by
  let X := EuclideanSpace ℝ (Fin n)
  have hτbound (a : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
      ‖iteratedFDeriv ℝ a τ y‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hτ.continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      (hcτ.iteratedFDeriv a)
    exact ⟨max B 0, le_max_right _ _, fun y ↦ (hB y).trans (le_max_left _ _)⟩
  have hΘbound (a : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K,
      ‖iteratedFDeriv ℝ a Θ z‖ ≤ B := by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      ((hΘ.continuousOn_iteratedFDerivWithin (m := a) (by simp) hW.uniqueDiffOn).mono hKW)
    refine ⟨max B 0, le_max_right _ _, fun z hz ↦ ?_⟩
    have h := hB z hz
    rw [iteratedFDerivWithin_of_isOpen _ hW (hKW hz)] at h
    exact h.trans (le_max_left _ _)
  have hInvCont : ContinuousOn (fun z ↦ (Θ z).inverse) K := by
    intro z hz
    exact (((hinv z (hKW hz)).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      ((hΘ.continuousOn.mono hKW) z hz))
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hInvCont
  obtain ⟨R₀, hR₀⟩ := hcτ.isBounded.exists_norm_le
  let B := max B₀ 0
  let R := max R₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hR : 0 ≤ R := le_max_right _ _
  choose A hA hτA using hτbound
  choose D hD hΘD using hΘbound
  let A' := ∑ a ∈ Finset.range (k + 1), A a
  have hA' : 0 ≤ A' := Finset.sum_nonneg (fun a _ ↦ hA a)
  have hAA' (a : ℕ) (ha : a ≤ k) : A a ≤ A' :=
    Finset.single_le_sum (fun b _ ↦ hA b) (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
  let D' := 1 + ∑ a ∈ Finset.range (k + 1), B * R * D a
  have hD' : 1 ≤ D' := le_add_of_nonneg_right (Finset.sum_nonneg
    (fun a _ ↦ mul_nonneg (mul_nonneg hB hR) (hD a)))
  have hDD' (a : ℕ) (ha : a ≤ k) : B * R * D a ≤ D' := by
    apply le_trans (Finset.single_le_sum
      (fun b _ ↦ mul_nonneg (mul_nonneg hB hR) (hD b))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ha)))
    exact le_add_of_nonneg_left zero_le_one
  let C : ℝ := k.factorial * A' * D' ^ k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun z hz ξ ↦ ?_⟩
  have hinner : ContDiffOn ℝ ∞ (fun w ↦ Θ w ξ) W := hΘ.clm_apply contDiffOn_const
  by_cases hmem : Θ z ξ ∈ tsupport τ
  · -- On the cutoff support, invertibility bounds the original frequency itself.
    have hξ : ‖ξ‖ ≤ B * R := by
      calc
        ‖ξ‖ = ‖(Θ z).inverse (Θ z ξ)‖ := by rw [(hinv z (hKW hz)).inverse_apply_self]
        _ ≤ ‖(Θ z).inverse‖ * ‖Θ z ξ‖ := (Θ z).inverse.le_opNorm _
        _ ≤ B * R := mul_le_mul ((hB₀ z hz).trans (le_max_left _ _))
          ((hR₀ _ hmem).trans (le_max_left _ _)) (norm_nonneg _) hB
    have hi (a : ℕ) (ha : 1 ≤ a) (hak : a ≤ k) :
        ‖iteratedFDerivWithin ℝ a (fun w ↦ Θ w ξ) W z‖ ≤ D' ^ a := by
      have h := norm_iteratedFDerivWithin_clm_apply_const
        (hΘ.contDiffWithinAt (hKW hz)) hW.uniqueDiffOn (hKW hz)
        (n := a) (c := ξ) (by simp)
      apply h.trans
      rw [iteratedFDerivWithin_of_isOpen _ hW (hKW hz)]
      apply (mul_le_mul hξ (hΘD a z hz) (norm_nonneg _) (mul_nonneg hB hR)).trans
      exact (hDD' a hak).trans (le_self_pow₀ hD' (by omega))
    have ho (a : ℕ) (ha : a ≤ k) :
        ‖iteratedFDerivWithin ℝ a τ Set.univ (Θ z ξ)‖ ≤ A' := by
      rw [iteratedFDerivWithin_univ]
      exact (hτA a _).trans (hAA' a ha)
    have h := norm_iteratedFDerivWithin_comp_le hτ.contDiffOn hinner (n := k) (by simp)
      uniqueDiffOn_univ hW.uniqueDiffOn (Set.mapsTo_univ _ _) (hKW hz) ho hi
    simpa only [C, Function.comp_def, iteratedFDerivWithin_of_isOpen _ hW (hKW hz)] using h
  · -- Outside the closed cutoff support the composite vanishes on a neighborhood.
    have hzτ : τ =ᶠ[nhds (Θ z ξ)] (fun _ ↦ 0) := by
      filter_upwards [(isClosed_tsupport τ).isOpen_compl.mem_nhds hmem] with η hη
      exact image_eq_zero_of_notMem_tsupport hη
    have hzero := hzτ.comp_tendsto (hinner.continuousOn.continuousAt (hW.mem_nhds (hKW hz)))
    have hd := (hzero.iteratedFDeriv ℝ k).eq_of_nhds
    simp only [Function.comp_def, iteratedFDeriv_fun_zero, Pi.zero_apply] at hd
    rw [hd, norm_zero]
    exact hC

/-- Uniform compact spatial support and polynomial bounds on all spatial derivatives make
frequency-diagonal oscillatory integrals stable under pointwise limits. -/
private theorem tendsto_oscillatory_integral_of_uniform_compact_bounds
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F)
    (hf : ∀ N ξ, ContDiff ℝ ∞ (f N ξ))
    (hc : ∀ N, Continuous (Function.uncurry (f N)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ N ξ, tsupport (f N ξ) ⊆ K) (d : ℕ)
    (hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N ξ y, y ∈ K →
      ‖iteratedFDeriv ℝ i (f N ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ d)
    (hlim : ∀ ξ y, Tendsto (fun N ↦ f N ξ y) atTop (nhds (g ξ y)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun N ↦ ∫ ξ, ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • f N ξ y) atTop
      (nhds (∫ ξ, ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • g ξ y)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc' : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  -- Fourier decay provides one integrable frequency bound for the entire family.
  obtain ⟨C, hC, hdecay⟩ := fourier_diagonal_decay_of_compact_support
    f hf K hK hsupp d hb c hc' (n + 1)
  have hid (N : ℕ) (ξ : X) : (∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • f N ξ y) =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • 𝓕 (f N ξ) (c • ξ) := by
    rw [Real.fourier_eq', ← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [smul_smul]
    congr 1
    rw [← Complex.exp_add, inner_sub_left, inner_smul_right]
    congr 1
    push_cast
    dsimp [c]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  have hcont (N : ℕ) : Continuous (fun z : X × X ↦
      Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ)) • f N z.1 z.2) := by
    have hphase : Continuous (fun z : X × X ↦
        Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ))) := by fun_prop
    exact hphase.smul (hc N)
  -- The inner integrals converge by ordinary dominated convergence on the fixed compact set.
  have hinner (ξ : X) : Tendsto (fun N ↦ ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • f N ξ y) atTop
      (nhds (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • g ξ y)) := by
    obtain ⟨B, hB, hbound⟩ := hb 0
    let b : X → ℝ := K.indicator (fun _ ↦ B * (1 + ‖ξ‖) ^ d)
    have hbi : Integrable b := by
      rw [show b = K.indicator (fun _ ↦ B * (1 + ‖ξ‖) ^ d) from rfl,
        integrable_indicator_iff hK.measurableSet]
      exact integrableOn_const hK.measure_lt_top.ne
    apply tendsto_integral_of_dominated_convergence b
      (fun N ↦ ((hcont N).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      hbi
    · intro N
      filter_upwards with y
      change ‖Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • f N ξ y‖ ≤ b y
      by_cases hy : y ∈ K
      · rw [show b y = K.indicator (fun _ ↦ B * (1 + ‖ξ‖) ^ d) y from rfl,
          Set.indicator_of_mem hy]
        have h := hbound N ξ y hy
        simpa only [norm_iteratedFDeriv_zero, norm_smul, Complex.norm_exp, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, mul_zero, sub_zero, Real.exp_zero, one_mul] using h
      · have hfy : f N ξ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hy (hsupp N ξ h))
        simp only [hfy, smul_zero, norm_zero, b, Set.indicator_of_notMem hy, le_refl]
    · filter_upwards with y
      exact tendsto_const_nhds.smul (hlim ξ y)
  -- Integrating in frequency is now legitimate with the same uniform Fourier majorant.
  have hi : Integrable (fun ξ : X ↦ (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by simp [X])
  apply tendsto_integral_of_dominated_convergence
    (fun ξ : X ↦ C * (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ)))
    (fun N ↦ (hcont N).stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
    (hi.const_mul C)
  · intro N
    filter_upwards with ξ
    rw [hid, norm_smul]
    simpa [Complex.norm_exp, Complex.mul_re] using hdecay N ξ
  · exact Eventually.of_forall hinner

/-- Frequency cutoffs through a smooth invertible linear family may be removed in the
original iterated amplitude integral, with no unregularized Fubini interchange. -/
theorem tendsto_amplitudeApply_frequency_regularization
    {n r q : ℕ} (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
    (hc : HasCompactSupport (Function.uncurry a))
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hKW : tsupport (Function.uncurry a) ⊆ W)
    (Θ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hΘ : ContDiffOn ℝ ∞ Θ W) (hinv : ∀ z ∈ W, (Θ z).IsInvertible)
    (τ : EuclideanSpace ℝ (Fin n) → ℝ) (hτ : ContDiff ℝ ∞ τ)
    (hcτ : HasCompactSupport τ) (hτzero : τ 0 = 1)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun N ↦ amplitudeApply
      (fun x y ξ ↦ τ (Θ (x, y) (ε N • ξ)) • a x y ξ) u x) atTop
      (nhds (amplitudeApply a u x)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let H := E →L[ℂ] F
  let K := tsupport (Function.uncurry a)
  let Kx : Set X := {y | (x, y) ∈ K}
  have hKx : IsCompact Kx := (hc.image continuous_snd).of_isClosed_subset
    ((isClosed_tsupport _).preimage (continuous_const.prodMk continuous_id))
    (fun y hy ↦ ⟨(x, y), hy, rfl⟩)
  let Wx : Set X := {y | (x, y) ∈ W}
  have hWx : IsOpen Wx := hW.preimage (continuous_const.prodMk continuous_id)
  have hKxW : Kx ⊆ Wx := fun y hy ↦ hKW hy
  have hΘx : ContDiffOn ℝ ∞ (fun y ↦ Θ (x, y)) Wx :=
    hΘ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy ↦ hy)
  let b : X → X → F := fun ξ y ↦ a x y ξ (u y)
  let f : ℕ → X → X → F := fun N ξ y ↦ τ (Θ (x, y) (ε N • ξ)) • b ξ y
  -- The original symbol bounds give one polynomial order for every spatial derivative.
  have hab (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Kx, ∀ ξ,
      ‖iteratedFDeriv ℝ j (fun y ↦ a x y ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := ha.2 ({x} ×ˢ Kx) (isCompact_singleton.prod hKx) 0 j 0
    refine ⟨C, hC, fun y hy ξ ↦ ?_⟩
    have hb := hbound x y ⟨Set.mem_singleton x, hy⟩ ξ
    have hzero : (fun w ↦ iteratedFDeriv ℝ 0 (a x w) ξ) =
        (continuousMultilinearCurryFin0 ℝ X H).symm ∘ (fun w ↦ a x w ξ) := by
      funext w
      exact congrFun iteratedFDeriv_zero_eq_comp ξ
    simp only [amplitudeDerivative, norm_iteratedFDeriv_zero, hzero,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.cast_zero, sub_zero] at hb
    calc
      _ ≤ C * (1 + ‖ξ‖) ^ m := hb
      _ ≤ C * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)) hC
      _ = _ := by rw [Real.rpow_natCast]
  let B : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
  have haSmooth (ξ : X) : ContDiff ℝ ∞ (fun y ↦ a x y ξ) :=
    ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hbSmooth (ξ : X) : ContDiff ℝ ∞ (b ξ) :=
    (B.contDiff.comp (haSmooth ξ)).clm_apply (u.smooth ⊤)
  choose C hC haC using hab
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ y, y ∈ Kx →
      ‖iteratedFDeriv ℝ j (b ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    let M := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * C i * SchwartzMap.seminorm ℂ 0 (j - i) u
    have hM : 0 ≤ M := by
      apply Finset.sum_nonneg
      intro i _
      have hiC := hC i
      positivity
    refine ⟨‖B‖ * M, by positivity, fun ξ y hy ↦ ?_⟩
    calc
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y ↦ a x y ξ) y‖ *
          ‖iteratedFDeriv ℝ (j - i) u y‖ :=
        B.norm_iteratedFDeriv_le_of_bilinear (haSmooth ξ) (u.smooth ⊤) y (by simp)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (C i * (1 + ‖ξ‖) ^ ⌈m⌉₊) * SchwartzMap.seminorm ℂ 0 (j - i) u := by
        apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul (mul_le_mul_of_nonneg_left (haC i y hy ξ) (Nat.cast_nonneg _))
          (u.norm_iteratedFDeriv_le_seminorm ℂ (j - i) y) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC i) (by positivity)))
      _ = (‖B‖ * M) * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
        dsimp [M]
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hcut (j : ℕ) := exists_uniform_bound_iteratedFDeriv_frequency_cutoff
    τ hτ hcτ Wx hWx (fun y ↦ Θ (x, y)) hΘx
    (fun y hy ↦ hinv (x, y) hy) Kx hKx hKxW j
  choose D hD hcutD using hcut
  choose G hG hbG using hb
  have hcoeff (N : ℕ) (ξ : X) :
      ContDiffOn ℝ ∞ (fun y ↦ τ (Θ (x, y) (ε N • ξ))) Wx :=
    hτ.comp_contDiffOn (hΘx.clm_apply contDiffOn_const)
  have hzero (y : X) (hy : y ∉ Kx) :
      ∀ᶠ w in nhds y, ∀ ξ, a x w ξ = 0 := by
    filter_upwards [hKx.isClosed.isOpen_compl.mem_nhds hy] with w hw
    have h := image_eq_zero_of_notMem_tsupport
      (show (x, w) ∉ tsupport (Function.uncurry a) from hw)
    exact fun ξ ↦ congrFun h ξ
  -- Every regularized family member is globally smooth despite arbitrary coefficients off W.
  have hf (N : ℕ) (ξ : X) : ContDiff ℝ ∞ (f N ξ) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Kx
    · exact ((hcoeff N ξ).contDiffAt (hWx.mem_nhds (hKxW hy))).smul
        (hbSmooth ξ).contDiffAt
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hzero y hy] with w hw
      simp only [f, b, hw ξ, zero_apply, smul_zero]
  have hfc (N : ℕ) : Continuous (Function.uncurry (f N)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.2 ∈ Kx
    · have hΘat := hΘx.contDiffAt (hWx.mem_nhds (hKxW hz))
      have hscalar := hτ.contDiffAt.comp z
        ((hΘat.comp z contDiffAt_snd).clm_apply
          ((contDiffAt_const (c := ε N)).smul contDiffAt_fst))
      have hval : ContDiffAt ℝ ∞ (fun z : X × X ↦ b z.1 z.2) z := by
        have hcoef : ContDiffAt ℝ ∞ (fun w : X × X ↦ a x w.2 w.1) z :=
          (ha.1.comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)).contDiffAt
        exact (B.contDiff.contDiffAt.comp z hcoef).clm_apply
          ((u.smooth ⊤).comp contDiff_snd).contDiffAt
      exact (hscalar.smul hval).continuousAt
    · apply (continuousAt_const : ContinuousAt (fun _ : X × X ↦ (0 : F)) z).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt (hzero z.2 hz)] with w hw
      simp only [Function.uncurry, f, b, hw w.1, zero_apply, smul_zero]
  have hfsupp (N : ℕ) (ξ : X) : tsupport (f N ξ) ⊆ Kx := by
    apply closure_minimal ?_ hKx.isClosed
    intro y hy
    by_contra hout
    have ha0 := (hzero y hout).self_of_nhds ξ
    exact hy (by simp only [f, b, ha0, zero_apply, smul_zero])
  have hfb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N ξ y, y ∈ Kx →
      ‖iteratedFDeriv ℝ j (f N ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    let C' := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D i * G (j - i)
    have hC' : 0 ≤ C' := Finset.sum_nonneg (fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD i)) (hG (j - i)))
    refine ⟨C', hC', fun N ξ y hy ↦ ?_⟩
    have hprod := norm_iteratedFDerivWithin_smul_le (hcoeff N ξ) (hbSmooth ξ).contDiffOn
      hWx.uniqueDiffOn (hKxW hy) (n := j) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hWx (hKxW hy)] at hprod
    apply hprod.trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ ≤ (j.choose i : ℝ) * D i *
          (G (j - i) * (1 + ‖ξ‖) ^ ⌈m⌉₊) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hcutD i y hy (ε N • ξ))
          (Nat.cast_nonneg _)) (hbG (j - i) ξ y hy) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (hD i))
      _ = _ := by ring
  have hflim (ξ y : X) : Tendsto (fun N ↦ f N ξ y) atTop (nhds (b ξ y)) := by
    have harg : Tendsto (fun N ↦ Θ (x, y) (ε N • ξ)) atTop (nhds 0) := by
      simpa only [Function.comp_def, zero_smul, map_zero] using
        (Θ (x, y)).continuous.continuousAt.tendsto.comp (hε.smul tendsto_const_nhds)
    have hscalar : Tendsto (fun N ↦ τ (Θ (x, y) (ε N • ξ))) atTop (nhds 1) := by
      simpa only [Function.comp_def, hτzero] using hτ.continuous.continuousAt.tendsto.comp harg
    simpa only [one_smul] using hscalar.smul (tendsto_const_nhds (x := b ξ y))
  have hlimit := tendsto_oscillatory_integral_of_uniform_compact_bounds
    f b hf hfc Kx hKx hfsupp ⌈m⌉₊ hfb hflim x
  exact tendsto_const_nhds.smul hlimit


/-- A compact frequency regularization makes a spatially compact, locally continuous
integrand absolutely integrable, also after a varying invertible frequency change. -/
theorem integrable_frequency_regularization
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W K : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → F)
    (hf : ContinuousOn f (W ×ˢ Set.univ))
    (hzero : ∀ y, y ∉ K → ∀ ξ, f (y, ξ) = 0)
    (Θ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hΘ : ContinuousOn Θ W) (hinv : ∀ y ∈ W, (Θ y).IsInvertible)
    (τ : EuclideanSpace ℝ (Fin n) → ℝ) (hτ : Continuous τ)
    (hcτ : HasCompactSupport τ) (ε : ℝ) (hε : ε ≠ 0) :
    Integrable (fun z ↦ τ (Θ z.1 (ε • z.2)) • f z) := by
  let X := EuclideanSpace ℝ (Fin n)
  let g : X × X → F := fun z ↦ τ (Θ z.1 (ε • z.2)) • f z
  have hInv : ContinuousOn (fun y ↦ (Θ y).inverse) K := by
    intro y hy
    exact ((hinv y (hKW hy)).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      ((hΘ.mono hKW) y hy)
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hInv
  obtain ⟨R₀, hR₀⟩ := hcτ.isBounded.exists_norm_le
  let B := max B₀ 0
  let R := max R₀ 0
  let C := (B * R) / ‖ε‖
  have hB : 0 ≤ B := le_max_right _ _
  have hR : 0 ≤ R := le_max_right _ _
  have hεpos : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  -- The local coefficient data are needed only on a neighborhood of the fixed spatial support.
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.1 ∈ K
    · have hzW : z ∈ W ×ˢ Set.univ := ⟨hKW hz, Set.mem_univ _⟩
      have hfz := hf.continuousAt ((hW.prod isOpen_univ).mem_nhds hzW)
      have hΘz := (hΘ.continuousAt (hW.mem_nhds (hKW hz))).comp continuous_fst.continuousAt
      change ContinuousAt (fun z ↦ τ (Θ z.1 (ε • z.2)) • f z) z
      exact (hτ.continuousAt.comp
        (hΘz.clm_apply ((continuous_const (y := ε)).smul continuous_snd).continuousAt)).smul hfz
    · apply (continuousAt_const : ContinuousAt (fun _ : X × X ↦ (0 : F)) z).congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt
        (hK.isClosed.isOpen_compl.mem_nhds hz)] with w hw
      change τ (Θ w.1 (ε • w.2)) • f (w.1, w.2) = 0
      rw [hzero w.1 hw w.2, smul_zero]
  -- Invertibility uniformly bounds the original frequency wherever the cutoff is nonzero.
  have hsupp : tsupport g ⊆ K ×ˢ Metric.closedBall (0 : X) C := by
    apply closure_minimal ?_ (hK.isClosed.prod Metric.isClosed_closedBall)
    intro z hz
    have hy : z.1 ∈ K := by
      by_contra hout
      apply hz
      change τ (Θ z.1 (ε • z.2)) • f (z.1, z.2) = 0
      rw [hzero z.1 hout z.2, smul_zero]
    have hτne : τ (Θ z.1 (ε • z.2)) ≠ 0 := by
      intro heq
      exact hz (by simp only [g, heq, zero_smul])
    have hτmem : Θ z.1 (ε • z.2) ∈ tsupport τ := subset_tsupport _ hτne
    have hfreq : ‖ε • z.2‖ ≤ B * R := by
      calc
        ‖ε • z.2‖ = ‖(Θ z.1).inverse (Θ z.1 (ε • z.2))‖ := by
          rw [(hinv z.1 (hKW hy)).inverse_apply_self]
        _ ≤ ‖(Θ z.1).inverse‖ * ‖Θ z.1 (ε • z.2)‖ := (Θ z.1).inverse.le_opNorm _
        _ ≤ B * R := mul_le_mul ((hB₀ z.1 hy).trans (le_max_left _ _))
          ((hR₀ _ hτmem).trans (le_max_left _ _)) (norm_nonneg _) hB
    refine ⟨hy, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (le_div_iff₀ hεpos).mpr
    simpa only [norm_smul, mul_comm] using hfreq
  exact hg.integrable_of_hasCompactSupport
    ((hK.prod (isCompact_closedBall (0 : X) C)).of_isClosed_subset (isClosed_tsupport _) hsupp)

/-- An actual spatial coordinate change and a parameter-dependent linear frequency
change preserve the double integral when both intermediate joint integrals are integrable. -/
theorem integral_spatial_frequency_substitution {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)))
    (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (Θ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → H)
    (hzero : ∀ η z, z ∉ e.source → f η z = 0)
    (hF : Integrable
      (fun z ↦ |(fderiv ℝ e.symm z.1).det| • f z.2 (e.symm z.1))
      ((volume.restrict e.target).prod volume))
    (hG : Integrable
      (fun z ↦ (|(fderiv ℝ e.symm z.1).det| * |(Θ z.1).toContinuousLinearMap.det|) •
        f (Θ z.1 z.2) (e.symm z.1)) ((volume.restrict e.target).prod volume)) :
    (∫ η, ∫ z, f η z) =
      ∫ ξ, ∫ y in e.target,
        (|(fderiv ℝ e.symm y).det| * |(Θ y).toContinuousLinearMap.det|) •
          f (Θ y ξ) (e.symm y) := by
  let X := EuclideanSpace ℝ (Fin n)
  -- First substitute the inverse spatial chart. The original integrand vanishes off
  -- its source, and the absolute Jacobian accommodates either orientation.
  have hspace (η : X) : (∫ z, f η z) =
      ∫ y in e.target, |(fderiv ℝ e.symm y).det| • f η (e.symm y) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hzero η)]
    exact integral_target_eq_integral_abs_det_fderiv_smul volume
      (f := e.symm) (fun y hy ↦
        ((hψ.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt)
      (f η)
  simp_rw [hspace]
  rw [← integral_integral_swap
    (f := fun y η ↦ |(fderiv ℝ e.symm y).det| • f η (e.symm y)) hF]
  -- The frequency substitution is allowed to depend on y. It is performed only
  -- after Fubini has made y the outer variable, retaining the same linear map.
  have hfrequency (y : X) :
      (∫ η, |(fderiv ℝ e.symm y).det| • f η (e.symm y)) =
        ∫ ξ, (|(fderiv ℝ e.symm y).det| * |(Θ y).toContinuousLinearMap.det|) •
          f (Θ y ξ) (e.symm y) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (f := Θ y) (f' := fun _ ↦ (Θ y).toContinuousLinearMap)
      (fun ξ _ ↦ (Θ y).hasFDerivAt.hasFDerivWithinAt)
      (Θ y).injective.injOn
      (fun η ↦ |(fderiv ℝ e.symm y).det| • f η (e.symm y))
    rw [Set.image_univ, (Θ y).surjective.range_eq, Measure.restrict_univ] at h
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall (fun ξ ↦ by
      dsimp only
      rw [smul_smul, mul_comm])))
  simp_rw [hfrequency]
  exact integral_integral_swap
    (f := fun y ξ ↦ (|(fderiv ℝ e.symm y).det| * |(Θ y).toContinuousLinearMap.det|) •
      f (Θ y ξ) (e.symm y)) hG

end AtiyahSinger
