/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude
public import AtiyahSinger.Analysis.CompactJetIntegral

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Compact integration of uniform amplitudes

Public module ID: M0345.

Continuous parameter dependence of all spatial and frequency jets, together
with uniform original amplitude estimates, permits compact integration before
reducing to a symbol. This avoids choosing a parameter-dependent reduced symbol
when constructing an averaged coordinate conjugate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
  {n r q : ℕ} {m : ℝ} (a : Y → AmplitudeFunction n r q)
  (ha : ∀ t, IsAmplitude m (a t))
  (hmixed : ∀ i j k : ℕ, Continuous
    (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin n)) ↦ amplitudeDerivative (a p.1) i j k p.2.1.1 p.2.1.2 p.2.2))

include ha hmixed

set_option maxSynthPendingDepth 25 in
set_option maxHeartbeats 800000 in

private theorem amplitudeDerivative_integral (i j k : ℕ)
    (x y ξ : EuclideanSpace ℝ (Fin n)) :
    amplitudeDerivative (fun x y ξ ↦ ∫ t, a t x y ξ ∂μ) i j k x y ξ =
      ∫ t, amplitudeDerivative (a t) i j k x y ξ ∂μ := by
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have parametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
      (f : P → Q → R) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (l : ℕ) :
      ContDiff ℝ ∞ (fun z : P × Q ↦ iteratedFDeriv ℝ l (f z.1) z.2) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have h : ContDiffAt ℝ ∞ (Function.uncurry f) z := hf.contDiffAt
    induction l with
    | zero =>
      exact h.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
    | succ l ih =>
      have hj : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × Q ↦ fun η : Q ↦ iteratedFDeriv ℝ l (f p.1) η))
          (z, z.2) := ih.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ l (f p.1)) p.2) z :=
        hj.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (l + 1) ↦ Q) R).symm :
          _ →L[ℝ] Q [×(l + 1)]→L[ℝ] R)
  have hspace (t : Y) (l : ℕ) : ContDiff ℝ ∞
      (fun z : X × X ↦ iteratedFDeriv ℝ l (a t z.1 z.2) ξ) :=
    (parametric (fun z : X × X ↦ a t z.1 z.2) (ha t).1 l).comp
      (contDiff_id.prodMk contDiff_const)
  have hpartial (t : Y) (b c : ℕ) : ContDiff ℝ ∞
      (fun z : X × X ↦ iteratedFDeriv ℝ b
        (fun y ↦ iteratedFDeriv ℝ c (a t z.1 y) ξ) z.2) :=
    parametric (fun x y ↦ iteratedFDeriv ℝ c (a t x y) ξ) (hspace t c) b
  -- Commute frequency derivatives first, then the input and output spatial derivatives.
  have hfrequency (z w : X) (η : X) :
      iteratedFDeriv ℝ k (fun η ↦ ∫ t, a t z w η ∂μ) η =
        ∫ t, iteratedFDeriv ℝ k (a t z w) η ∂μ := by
    apply iteratedFDeriv_integral_of_continuous_jets μ isOpen_univ
      (fun t ↦ ((ha t).1.comp ((contDiff_const (c := (z, w))).prodMk contDiff_id)).contDiffOn)
    · intro l
      have hc := ((continuousMultilinearCurryFin0 ℝ X (X [×l]→L[ℝ] H)).continuous.comp
        (continuousMultilinearCurryFin0 ℝ X (X [×0]→L[ℝ] (X [×l]→L[ℝ] H))).continuous).comp
          ((hmixed 0 0 l).comp
            (show Continuous (fun p : Y × X ↦ (p.1, ((z, w), p.2))) from by fun_prop))
      change Continuous (fun p : Y × X ↦
        ((amplitudeDerivative (a p.1) 0 0 l z w p.2).curry0).curry0) at hc
      simpa only [amplitudeDerivative, iteratedFDeriv_zero_apply,
        ContinuousMultilinearMap.curry0_apply, Function.comp_def, Function.uncurry, id_eq]
        using hc.continuousOn
    · exact mem_univ η
  have hinput (z : X) :
      iteratedFDeriv ℝ j (fun w ↦ ∫ t, iteratedFDeriv ℝ k (a t z w) ξ ∂μ) y =
        ∫ t, iteratedFDeriv ℝ j (fun w ↦ iteratedFDeriv ℝ k (a t z w) ξ) y ∂μ := by
    apply iteratedFDeriv_integral_of_continuous_jets μ isOpen_univ
      (fun t ↦ ((hspace t k).comp (contDiff_const.prodMk contDiff_id)).contDiffOn)
    · intro l
      have hc := (continuousMultilinearCurryFin0 ℝ X
        (X [×l]→L[ℝ] (X [×k]→L[ℝ] H))).continuous.comp ((hmixed 0 l k).comp
          (show Continuous (fun p : Y × X ↦ (p.1, ((z, p.2), ξ))) from by fun_prop))
      change Continuous (fun p : Y × X ↦
        (amplitudeDerivative (a p.1) 0 l k z p.2 ξ).curry0) at hc
      simpa only [amplitudeDerivative, iteratedFDeriv_zero_apply,
        ContinuousMultilinearMap.curry0_apply, Function.comp_def, Function.uncurry, id_eq]
        using hc.continuousOn
    · exact mem_univ y
  have houtput :
      iteratedFDeriv ℝ i (fun z ↦ ∫ t,
        iteratedFDeriv ℝ j (fun w ↦ iteratedFDeriv ℝ k (a t z w) ξ) y ∂μ) x =
        ∫ t, amplitudeDerivative (a t) i j k x y ξ ∂μ := by
    apply iteratedFDeriv_integral_of_continuous_jets μ isOpen_univ
      (fun t ↦ ((hpartial t j k).comp (contDiff_id.prodMk contDiff_const)).contDiffOn)
    · intro l
      exact ((hmixed l j k).comp
        (show Continuous (fun p : Y × X ↦ (p.1, ((p.2, y), ξ))) from by fun_prop)).continuousOn
    · exact mem_univ x
  unfold amplitudeDerivative
  simp_rw [hfrequency, hinput]
  exact houtput

set_option maxSynthPendingDepth 25 in
/-- A compact finite-measure integral preserves the order of a uniform amplitude family. -/
theorem isAmplitude_integral_of_continuous_jets
    (hjoint : ∀ l : ℕ, Continuous
      (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ l
          (fun z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
            EuclideanSpace ℝ (Fin n) ↦ a p.1 z.1.1 z.1.2 z.2) p.2))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsCompact K → ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y, (x, y) ∈ K → ∀ ξ,
        ‖amplitudeDerivative (a t) i j k x y ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (k : ℝ))) :
    IsAmplitude m (fun x y ξ ↦ ∫ t, a t x y ξ ∂μ) := by
  constructor
  · -- Continuous jets on the product model give smoothness of the same matrix integral.
    exact contDiffOn_univ.mp (contDiffOn_integral_of_continuous_jets μ isOpen_univ
      (fun t ↦ (ha t).1.contDiffOn) (fun l ↦ (hjoint l).continuousOn))
  · intro K hK i j k
    obtain ⟨C, hC, hbound⟩ := hbound K hK i j k
    refine ⟨μ.real univ * C, mul_nonneg measureReal_nonneg hC, fun x y hxy ξ ↦ ?_⟩
    rw [amplitudeDerivative_integral μ a ha hmixed]
    have hc : Continuous (fun t ↦ amplitudeDerivative (a t) i j k x y ξ) :=
      (hmixed i j k).comp (continuous_id.prodMk (continuous_const (y := ((x, y), ξ))))
    have hi := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ ∫ t, ‖amplitudeDerivative (a t) i j k x y ξ‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : Y, C * (1 + ‖ξ‖) ^ (m - (k : ℝ)) ∂μ :=
        integral_mono_ae hi.norm (integrable_const _)
          (Filter.Eventually.of_forall (fun t ↦ hbound t x y hxy ξ))
      _ = (C * (1 + ‖ξ‖) ^ (m - (k : ℝ))) * μ.real univ := by
        rw [integral_const, smul_eq_mul, mul_comm]
      _ = _ := by ring

omit hmixed in
set_option maxSynthPendingDepth 25 in
set_option maxHeartbeats 800000 in

/-- Compact parameter integration commutes with the original iterated amplitude action.
Uniform spatial derivative bounds are used before exchanging the outer Fourier integral. -/
theorem amplitudeApply_integral_of_uniform_bound
    (K₀ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hK₀ : IsCompact K₀) (hsupp : ∀ t, tsupport (Function.uncurry (a t)) ⊆ K₀)
    (hc : Continuous
      (fun p : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ a p.1 p.2.1.1 p.2.1.2 p.2.2))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsCompact K → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y, (x, y) ∈ K → ∀ ξ,
        ‖amplitudeDerivative (a t) 0 j 0 x y ξ‖ ≤ C * (1 + ‖ξ‖) ^ m)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    amplitudeApply (fun x y ξ ↦ ∫ t, a t x y ξ ∂μ) u x =
      ∫ t, amplitudeApply (a t) u x ∂μ := by
  -- Uniform integration by parts in the input variable gives one integrable Fourier bound.
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let H := E →L[ℂ] F
  let K : Set V := Prod.snd '' K₀
  have hK : IsCompact K := hK₀.image continuous_snd
  have hab (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, y ∈ K → ∀ ξ,
      ‖iteratedFDeriv ℝ j (fun y ↦ a t x y ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := hbound ({x} ×ˢ K) (isCompact_singleton.prod hK) j
    refine ⟨C, hC, ?_⟩
    intro t y hy ξ
    have hb := hbound t x y ⟨Set.mem_singleton x, hy⟩ ξ
    have hzero : (fun w ↦ iteratedFDeriv ℝ 0 (a t x w) ξ) =
        (continuousMultilinearCurryFin0 ℝ V H).symm ∘ (fun w ↦ a t x w ξ) := by
      funext w
      exact congrFun iteratedFDeriv_zero_eq_comp ξ
    simp only [amplitudeDerivative, norm_iteratedFDeriv_zero, hzero,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left] at hb
    calc
      _ ≤ C * (1 + ‖ξ‖) ^ m := hb
      _ ≤ C * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)) hC
      _ = _ := by rw [Real.rpow_natCast]
  let f (t : Y) (ξ y : V) : F := a t x y ξ (u y)
  let B : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
  have haSmooth (t : Y) (ξ : V) : ContDiff ℝ ∞ (fun y ↦ a t x y ξ) :=
    (ha t).1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hf (t : Y) (ξ : V) : ContDiff ℝ ∞ (f t ξ) :=
    (B.contDiff.comp (haSmooth t ξ)).clm_apply (u.smooth ⊤)
  have hsupport (t : Y) (ξ : V) : tsupport (f t ξ) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    have hz : Function.uncurry (a t) (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (show (x, y) ∉ tsupport (Function.uncurry (a t)) from fun h ↦ hyK ⟨(x, y), hsupp t h, rfl⟩)
    change a t x y = 0 at hz
    exact hy (by simp [f, hz])
  choose C hC hbound using hab
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ y, y ∈ K →
      ‖iteratedFDeriv ℝ j (f t ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    let M := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * C i * SchwartzMap.seminorm ℂ 0 (j - i) u
    have hM : 0 ≤ M := by
      apply Finset.sum_nonneg
      intro i _
      have hiC := hC i
      positivity
    refine ⟨‖B‖ * M, by positivity, ?_⟩
    intro t ξ y hy
    calc
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y ↦ a t x y ξ) y‖ *
          ‖iteratedFDeriv ℝ (j - i) u y‖ :=
        B.norm_iteratedFDeriv_le_of_bilinear (haSmooth t ξ) (u.smooth ⊤) y (by simp)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (C i * (1 + ‖ξ‖) ^ ⌈m⌉₊) * SchwartzMap.seminorm ℂ 0 (j - i) u := by
        apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro i _
        have hiC := hC i
        gcongr
        · exact hbound i t y hy ξ
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ u (j - i) y
      _ = (‖B‖ * M) * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
        dsimp [M]
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  -- Fourier decay controls the diagonal frequency, without joint absolute integrability.
  let c : ℝ := (2 * Real.pi)⁻¹
  have hcnz : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  obtain ⟨C, hC, hdecay⟩ := fourier_diagonal_decay_of_compact_support
    f hf K hK hsupport ⌈m⌉₊ hb c hcnz (n + 1)
  have hid (t : Y) (ξ : V) : (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
      a t x y ξ (u y)) =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • 𝓕 (f t ξ) (c • ξ) := by
    rw [Real.fourier_eq', ← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [f, smul_smul]
    congr 1
    rw [← Complex.exp_add, inner_sub_left, inner_smul_right]
    congr 1
    push_cast
    dsimp [c]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  let integrand (t : Y) (ξ y : V) : F :=
    Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a t x y ξ (u y)
  have hHc : Continuous (fun p : (Y × V) × V ↦ integrand p.1.1 p.1.2 p.2) := by
    have hphase : Continuous (fun p : (Y × V) × V ↦
        Complex.exp (Complex.I * (inner ℝ (x - p.2) p.1.2 : ℂ))) := by fun_prop
    exact hphase.smul ((hc.comp (continuous_fst.fst.prodMk
      ((continuous_const.prodMk continuous_snd).prodMk continuous_fst.snd))).clm_apply
        (u.continuous.comp continuous_snd))
  have hweight : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by simp [V])
  have hOuter : Integrable (fun p : Y × V ↦ ∫ y, integrand p.1 p.2 y) (μ.prod volume) := by
    apply ((integrable_const (1 : ℝ) : Integrable (fun _ : Y ↦ (1 : ℝ)) μ).mul_prod
      (hweight.const_mul C)).mono'
    · exact hHc.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    · filter_upwards [] with p
      change ‖∫ y, integrand p.1 p.2 y‖ ≤ 1 * (C * (1 + ‖p.2‖) ^ (-((n + 1 : ℕ) : ℝ)))
      rw [one_mul, show (∫ y, integrand p.1 p.2 y) =
        Complex.exp (Complex.I * (inner ℝ x p.2 : ℂ)) • 𝓕 (f p.1 p.2) (c • p.2)
          from hid p.1 p.2, norm_smul]
      simpa [Complex.norm_exp, Complex.mul_re] using hdecay p.1 p.2
  have hInner (ξ : V) : Integrable (fun p : Y × V ↦ integrand p.1 ξ p.2) (μ.prod volume) := by
    have hcontinuous := hHc.comp
      ((continuous_fst.prodMk (continuous_const (y := ξ))).prodMk continuous_snd)
    apply hcontinuous.integrable_of_hasCompactSupport
    apply (isCompact_univ.prod hK).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_univ.prod hK.isClosed)
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    by_contra hout
    have hz : Function.uncurry (a p.1) (x, p.2) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hout ⟨(x, p.2), hsupp p.1 h, rfl⟩)
    change a p.1 x p.2 = 0 at hz
    exact hp (by simp [integrand, hz])
  -- The compact spatial integral is exchanged first; the decay bound controls the outer exchange.
  unfold amplitudeApply
  rw [integral_smul]
  congr 1
  calc
    _ = ∫ ξ, ∫ y, ∫ t, integrand t ξ y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      apply integral_congr_ae
      filter_upwards [] with y
      have hi : Integrable (fun t ↦ a t x y ξ) μ :=
        (hc.comp (continuous_id.prodMk
          (continuous_const (y := ((x, y), ξ))))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      let T : H →L[ℂ] F :=
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • ContinuousLinearMap.apply ℂ F (u y)
      change T (∫ t, a t x y ξ ∂μ) = ∫ t, T (a t x y ξ) ∂μ
      exact (T.integral_comp_comm hi).symm
    _ = ∫ ξ, ∫ t, (∫ y, integrand t ξ y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact (integral_integral_swap (hInner ξ)).symm
    _ = ∫ t, (∫ ξ, ∫ y, integrand t ξ y) ∂μ := (integral_integral_swap hOuter).symm

end AtiyahSinger
