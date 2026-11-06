/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzJetIntegral
public import AtiyahSinger.Analysis.SchwartzKernelExistence

/-!
# Continuous window reconstruction in Schwartz space

Public module ID: M0954.

Translated and modulated compact windows give a continuous synthesis family
whose pointwise integral is the original test multiplied by the integral of
the window's square. Every continuous Schwartz seminorm of this family is
integrable, so continuous scalar functionals respect the same synthesis.
A nonzero square integral permits normalization for the kernel theorem;
the window formulas use no complex conjugation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option backward.isDefEq.respectTransparency false

attribute [local instance 2000] NormedField.toNormedCommRing Real.normedCommRing

open MeasureTheory Set
open scoped BoundedContinuousFunction ContDiff FourierTransform SchwartzMap

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The translated and modulated Schwartz window, with the positive Fourier phase. -/
def schwartzWindowAtom (g : 𝓢(V, ℂ)) (p : V × V) : 𝓢(V, ℂ) :=
  𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p.2
    (𝓕 (SchwartzMap.compSubConstCLM ℂ p.1 g)))

/-- The windowed Fourier coefficient without conjugation. For a real window this
is the usual short-time Fourier coefficient. -/
def schwartzWindowCoefficient (g f : 𝓢(V, ℂ)) (p : V × V) : ℂ :=
  (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
    (SchwartzMap.compSubConstCLM ℂ p.1 g)) : 𝓢(V, ℂ)) p.2

/-- Windowed Fourier coefficients vary continuously in position and frequency. -/
theorem continuous_schwartzWindowCoefficient (g f : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) : Continuous (schwartzWindowCoefficient g f) := by
  -- The previously proved Schwartz continuity controls the translated window.
  have htranslate : Continuous (fun a : V ↦ SchwartzMap.compSubConstCLM ℂ a g) := by
    have h := (continuous_schwartz_modulation_translation g hg).comp
      (continuous_id.prodMk (continuous_const (y := (0 : V))))
    change Continuous (fun a : V ↦ 𝓕⁻ (SchwartzMap.compSubConstCLM ℂ (0 : V)
      (𝓕 (SchwartzMap.compSubConstCLM ℂ a g)))) at h
    simpa only [SchwartzMap.compSubConstCLM_zero,
      ContinuousLinearMap.id_apply,
      FourierTransform.fourierInv_fourier_eq] using h
  let L : 𝓢(V, ℂ) →L[ℂ] V →ᵇ ℂ :=
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ).comp
      (FourierTransform.fourierCLM ℂ 𝓢(V, ℂ))
  have hfamily : Continuous (fun a : V ↦ L
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
        (SchwartzMap.compSubConstCLM ℂ a g))) :=
    L.continuous.comp ((SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f).continuous.comp
      htranslate)
  exact continuous_eval.comp ((hfamily.comp continuous_fst).prodMk continuous_snd)

/-- A continuous polynomial weight is integrable against the absolute windowed
Fourier coefficient, with a bound by one continuous input Schwartz seminorm. -/
theorem exists_schwartzWindowCoefficient_integral_bound (g : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) (w : V × V → ℝ) (hw : Continuous w)
    (hw₀ : ∀ p, 0 ≤ w p) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hweight : ∀ p, w p ≤ C * (1 + ‖p.1‖ + ‖p.2‖) ^ d) :
    ∃ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q ∧ ∀ f : 𝓢(V, ℂ),
      Integrable (fun p ↦ ‖schwartzWindowCoefficient g f p‖ * w p) ∧
      ∫ p, ‖schwartzWindowCoefficient g f p‖ * w p ≤ q f := by
  let μ : Measure (V × V) := volume
  let : μ.IsAddHaarMeasure := by
    change Measure.IsAddHaarMeasure ((volume : Measure V).prod volume)
    infer_instance
  let r := μ.integrablePower
  obtain ⟨q, hq, hdecay⟩ := exists_schwartz_window_fourier_bound g (d + r) (d + r)
  let D : ℝ := 2 ^ r * (∫ p : V × V, (1 + ‖p‖) ^ (-(r : ℝ))) * (2 * C)
  have hD : 0 ≤ D := by
    apply mul_nonneg
    · exact mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ by positivity))
    · positivity
  refine ⟨(Real.toNNReal D) • q, hq.const_smul (Real.toNNReal D), ?_⟩
  intro f
  let F : V × V → ℝ := fun p ↦ ‖schwartzWindowCoefficient g f p‖ * w p
  have hF : Continuous F := (continuous_schwartzWindowCoefficient g f hg).norm.mul hw
  have hF₀ (p : V × V) : 0 ≤ F p := mul_nonneg (norm_nonneg _) (hw₀ p)
  -- Joint rapid decay absorbs both the window growth and the integrable tail.
  have hbounds (p : V × V) : ‖F p‖ ≤ C * q f ∧ ‖p‖ ^ r * ‖F p‖ ≤ C * q f := by
    let B := (1 + ‖p.1‖) * (1 + ‖p.2‖)
    have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
      (by linarith [norm_nonneg p.1]) (by linarith [norm_nonneg p.2])
    have hsum : 1 + ‖p.1‖ + ‖p.2‖ ≤ B := by
      dsimp [B]
      nlinarith [mul_nonneg (norm_nonneg p.1) (norm_nonneg p.2)]
    have hnorm : ‖p‖ ≤ B := by
      rw [Prod.norm_def]
      exact (max_le (by linarith [norm_nonneg p.2])
        (by linarith [norm_nonneg p.1])).trans hsum
    have hcoeff : B ^ (d + r) * ‖schwartzWindowCoefficient g f p‖ ≤ q f := by
      simpa only [B, mul_pow, schwartzWindowCoefficient] using hdecay f p.1 p.2
    have hmajor : ‖F p‖ ≤ C * B ^ d * ‖schwartzWindowCoefficient g f p‖ := by
      rw [Real.norm_of_nonneg (hF₀ p)]
      calc
        _ ≤ ‖schwartzWindowCoefficient g f p‖ * (C * B ^ d) := by
          apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (hweight p).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hsum d) hC)
        _ = _ := by ring
    have hweighted : B ^ r * ‖F p‖ ≤ C * q f := by
      calc
        _ ≤ B ^ r * (C * B ^ d * ‖schwartzWindowCoefficient g f p‖) := by
          gcongr
        _ = C * (B ^ (d + r) * ‖schwartzWindowCoefficient g f p‖) := by
          rw [pow_add]
          ring
        _ ≤ C * q f := mul_le_mul_of_nonneg_left hcoeff hC
    constructor
    · exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hB)).trans hweighted
    · exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hnorm r) (norm_nonneg _)).trans hweighted
  have hI := integrable_of_le_of_pow_mul_le (μ := μ) (k := 0)
    (fun p ↦ (hbounds p).1) (by simpa only [zero_add] using fun p ↦ (hbounds p).2)
    hF.aestronglyMeasurable
  have hI' : Integrable F := by
    have hnorm : Integrable (fun p ↦ ‖F p‖) := by simpa only [pow_zero, one_mul] using hI
    exact (integrable_norm_iff hF.aestronglyMeasurable).mp hnorm
  refine ⟨hI', ?_⟩
  have hbound := integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 0)
    (fun p ↦ (hbounds p).1) (by simpa only [zero_add] using fun p ↦ (hbounds p).2)
  simp only [pow_zero, one_mul, Real.norm_of_nonneg (hF₀ _)] at hbound
  change ∫ p, F p ≤ _
  calc
    _ ≤ 2 ^ r * (∫ p : V × V, (1 + ‖p‖) ^ (-(r : ℝ))) * (C * q f + C * q f) := hbound
    _ = ((Real.toNNReal D) • q) f := by
      simp only [smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal D hD]
      dsimp [D]
      ring

/-- The continuous synthesis family associated to a window and a test. -/
def schwartzWindowSynthesis (g f : 𝓢(V, ℂ)) (p : V × V) : 𝓢(V, ℂ) :=
  schwartzWindowCoefficient g f p • schwartzWindowAtom g p

/-- Window synthesis varies continuously in the full Schwartz topology. -/
theorem continuous_schwartzWindowSynthesis (g f : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) : Continuous (schwartzWindowSynthesis g f) :=
  (continuous_schwartzWindowCoefficient g f hg).smul
    (continuous_schwartz_modulation_translation g hg)

/-- Every continuous Schwartz seminorm of the synthesis family is integrable.
This is the topology needed for distributional reconstruction. -/
theorem integrable_seminorm_schwartzWindowSynthesis (g f : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) (p : Seminorm ℂ 𝓢(V, ℂ)) (hp : Continuous p) :
    Integrable (fun z ↦ p (schwartzWindowSynthesis g f z)) := by
  obtain ⟨C, hC, d, hbound⟩ :=
    exists_schwartz_modulation_translation_seminorm_bound p hp g
  obtain ⟨_, _, hI⟩ := exists_schwartzWindowCoefficient_integral_bound g hg
    (fun z ↦ p (schwartzWindowAtom g z))
    (hp.comp (continuous_schwartz_modulation_translation g hg))
    (fun _ ↦ apply_nonneg _ _) C hC d (fun z ↦ hbound z.1 z.2)
  simpa only [schwartzWindowSynthesis, map_smul_eq_mul] using (hI f).1

/-- The continuous window synthesis reconstructs the original test, multiplied
by the integral of the square of the window. No conjugation is implicit. -/
theorem integral_schwartzWindowSynthesis (g f : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) (x : V) :
    ∫ p : V × V, schwartzWindowSynthesis g f p x = (∫ a : V, g a ^ 2) * f x := by
  let F := schwartzWindowSynthesis g f
  let e : 𝓢(V, ℂ) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)
  have hI : Integrable (fun p ↦ F p x) := by
    have hnorm := integrable_seminorm_schwartzWindowSynthesis g f hg
      (normSeminorm ℂ ℂ |>.comp e.toLinearMap) e.continuous.norm
    exact (integrable_norm_iff
      (e.continuous.comp (continuous_schwartzWindowSynthesis g f hg)).aestronglyMeasurable).mp
        hnorm
  -- Frequency integration is ordinary Fourier inversion of the windowed input.
  have hfrequency (a : V) : ∫ ξ : V, F (a, ξ) x = f x * g (x - a) ^ 2 := by
    let u := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
      (SchwartzMap.compSubConstCLM ℂ a g)
    have hInv : (∫ ξ : V,
        (Real.fourierChar (inner ℝ ξ x) : ℂ) * (𝓕 u : 𝓢(V, ℂ)) ξ) = u x := by
      have h := congrArg (fun v : 𝓢(V, ℂ) ↦ v x)
        (show (𝓕⁻ (𝓕 u) : 𝓢(V, ℂ)) = u from FourierTransform.fourierInv_fourier_eq u)
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
      exact h
    calc
      _ = ∫ ξ : V, ((Real.fourierChar (inner ℝ ξ x) : ℂ) *
          (𝓕 u : 𝓢(V, ℂ)) ξ) * g (x - a) := by
        apply integral_congr_ae
        filter_upwards with ξ
        change schwartzWindowCoefficient g f (a, ξ) * schwartzWindowAtom g (a, ξ) x = _
        rw [schwartzWindowAtom, fourierInv_compSubConstCLM_fourier_apply]
        change (𝓕 u : 𝓢(V, ℂ)) ξ *
          ((Real.fourierChar (inner ℝ ξ x) : ℂ) * g (x - a)) = _
        ring
      _ = (∫ ξ : V, (Real.fourierChar (inner ℝ ξ x) : ℂ) *
          (𝓕 u : 𝓢(V, ℂ)) ξ) * g (x - a) := integral_mul_const _ _
      _ = f x * g (x - a) ^ 2 := by rw [hInv]; change f x * g (x - a) * _ = _; ring
  -- Position integration is translation invariance of the square of the window.
  calc
    _ = ∫ a : V, ∫ ξ : V, F (a, ξ) x := integral_prod _ hI
    _ = ∫ a : V, f x * g (x - a) ^ 2 := by simp_rw [hfrequency]
    _ = f x * ∫ a : V, g (x - a) ^ 2 := integral_const_mul _ _
    _ = (∫ a : V, g a ^ 2) * f x := by
      rw [integral_sub_left_eq_self (fun a : V ↦ g a ^ 2) volume x]
      exact mul_comm _ _

/-- Every continuous scalar functional respects continuous window reconstruction.
The equality follows from integrability of all Schwartz seminorms, not from a
Banach-space interpretation of Schwartz space. -/
theorem integral_schwartzWindowSynthesis_apply (g f : 𝓢(V, ℂ))
    (hg : HasCompactSupport g) (L : 𝓢(V, ℂ) →L[ℂ] ℂ) :
    ∫ p : V × V, schwartzWindowCoefficient g f p * L (schwartzWindowAtom g p) =
      (∫ a : V, g a ^ 2) * L f := by
  let c : ℂ := ∫ a : V, g a ^ 2
  have h := schwartz_integral_apply volume (schwartzWindowSynthesis g f)
    (continuous_schwartzWindowSynthesis g f hg)
    (fun k j ↦ integrable_seminorm_schwartzWindowSynthesis g f hg _
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, j)))
    (c • f) (fun x ↦ (integral_schwartzWindowSynthesis g f hg x).symm) L
  simpa only [schwartzWindowSynthesis, map_smul, smul_eq_mul] using h.symm

/-- A continuous polynomially growing phase-space amplitude defines an actual
continuous Schwartz functional by windowed Fourier synthesis. The estimate is
uniform in the input test and hence proves continuity of the extension. -/
theorem exists_schwartzWindowFunctional (g : 𝓢(V, ℂ)) (hg : HasCompactSupport g)
    (H : V × V → ℂ) (hH : Continuous H) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hbound : ∀ z, ‖H z‖ ≤ C * (1 + ‖z.1‖ + ‖z.2‖) ^ d) :
    ∃ L : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f : 𝓢(V, ℂ),
      L f = ∫ z : V × V, schwartzWindowCoefficient g f z * H z := by
  obtain ⟨q, hq, hI⟩ := exists_schwartzWindowCoefficient_integral_bound g hg
    (fun z ↦ ‖H z‖) hH.norm (fun _ ↦ norm_nonneg _) C hC d hbound
  let A (f : 𝓢(V, ℂ)) := ∫ z : V × V, schwartzWindowCoefficient g f z * H z
  have hAf (f : 𝓢(V, ℂ)) : Integrable (fun z ↦ schwartzWindowCoefficient g f z * H z) := by
    apply (integrable_norm_iff
      ((continuous_schwartzWindowCoefficient g f hg).fun_mul hH).aestronglyMeasurable).mp
    simpa only [norm_mul] using (hI f).1
  have hadd (f h : 𝓢(V, ℂ)) : A (f + h) = A f + A h := by
    dsimp [A]
    rw [← integral_add (hAf f) (hAf h)]
    apply integral_congr_ae
    filter_upwards with z
    simp only [schwartzWindowCoefficient, map_add, add_apply,
      FourierTransform.fourier_add, add_mul]
  have hsmul (c : ℂ) (f : 𝓢(V, ℂ)) : A (c • f) = c • A f := by
    dsimp [A]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [schwartzWindowCoefficient, map_smul, smul_apply,
      FourierTransform.fourier_smul, smul_eq_mul, mul_assoc]
  -- A single finite family of original seminorms bounds the integral functional.
  obtain ⟨s, D, _, hD⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) q hq
  have hfinite : ∃ (s : Finset (ℕ × ℕ)) (D : ℝ), 0 ≤ D ∧ ∀ f : 𝓢(V, ℂ),
      ‖A f‖ ≤ D * (s.sup (schwartzSeminormFamily ℂ V ℂ)) f := by
    refine ⟨s, D, D.coe_nonneg, ?_⟩
    intro f
    calc
      _ ≤ ∫ z : V × V, ‖schwartzWindowCoefficient g f z * H z‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ z : V × V, ‖schwartzWindowCoefficient g f z‖ * ‖H z‖ := by
        simp only [norm_mul]
      _ ≤ q f := (hI f).2
      _ ≤ _ := Seminorm.le_def.mp hD f
  exact ⟨SchwartzMap.mkCLMtoNormedSpace A hadd hsmul hfinite, fun _ ↦ rfl⟩

/-- Two successive window reconstructions recover a jointly continuous bilinear
Schwartz pairing. Both integrations use the same fixed window and Fourier sign. -/
theorem integral_integral_schwartzWindow_bilinear (g φ ψ : 𝓢(V, ℂ))
    (hg : HasCompactSupport g)
    (b : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) →ₗ[ℂ] ℂ)
    (hb : Continuous (fun z : 𝓢(V, ℂ) × 𝓢(V, ℂ) ↦ b z.1 z.2)) :
    (∫ p : V × V, ∫ q : V × V,
      (schwartzWindowCoefficient g φ p * schwartzWindowCoefficient g ψ q) *
        b (schwartzWindowAtom g p) (schwartzWindowAtom g q)) =
      (∫ a : V, g a ^ 2) ^ 2 * b φ ψ := by
  let c : ℂ := ∫ a : V, g a ^ 2
  -- First reconstruct the second test against each fixed first atom.
  have hright (p : V × V) : (∫ q : V × V,
      (schwartzWindowCoefficient g φ p * schwartzWindowCoefficient g ψ q) *
        b (schwartzWindowAtom g p) (schwartzWindowAtom g q)) =
      schwartzWindowCoefficient g φ p * (c * b (schwartzWindowAtom g p) ψ) := by
    let R : 𝓢(V, ℂ) →L[ℂ] ℂ :=
      ⟨b (schwartzWindowAtom g p), hb.comp (continuous_const.prodMk continuous_id)⟩
    have h := integral_schwartzWindowSynthesis_apply g ψ hg R
    simp only [mul_assoc]
    rw [integral_const_mul]
    exact congrArg (fun z : ℂ ↦ schwartzWindowCoefficient g φ p * z) h
  simp_rw [hright]
  -- Then reconstruct the first test against the now fixed second test.
  let L : 𝓢(V, ℂ) →L[ℂ] ℂ :=
    ⟨b.flip ψ, hb.comp (continuous_id.prodMk continuous_const)⟩
  have h := integral_schwartzWindowSynthesis_apply g φ hg L
  calc
    (∫ p : V × V, schwartzWindowCoefficient g φ p *
        (c * b (schwartzWindowAtom g p) ψ)) =
        c * ∫ p : V × V, schwartzWindowCoefficient g φ p * L (schwartzWindowAtom g p) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      change _ = c * (schwartzWindowCoefficient g φ p * b (schwartzWindowAtom g p) ψ)
      ring
    _ = c ^ 2 * b φ ψ := by rw [h]; change c * (c * b φ ψ) = _; ring

end AtiyahSinger
