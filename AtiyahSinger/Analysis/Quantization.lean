/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EuclideanSobolev
public import AtiyahSinger.Analysis.Symbol
public import AtiyahSinger.Analysis.SymbolFourier
public import AtiyahSinger.Analysis.SchurKernel
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import AtiyahSinger.Analysis.SymbolQuotient

/-!
# Local Kohn-Nirenberg quantization

Public module ID: M0906.

D05 and the local parts of A02/A03/A05. The forward Fourier phase is exp(-i x·ξ),
and the inverse quantization phase is exp(i x·ξ). The transform is unnormalized,
with paired inverse factor (2π)^(-n). SG III.2 (2.2) uses the unitary (2π)^(-n/2)
transform; these paired conventions give the same Kohn-Nirenberg operator.
SG means Lawson and Michelsohn, Spin Geometry (Princeton University Press, 1989).
A compact support condition in the spatial variable is explicit in the Euclidean estimates.
Manifold localization, changes of chart and proper support are still separate obligations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped SchwartzMap ContDiff

variable {n r q : ℕ}

/-- The unnormalized angular-frequency Fourier transform, obtained by frequency rescaling.
It equals `(2π)^(n/2)` times SG III.2 (2.2); `quantize` uses its paired inverse factor. -/
def fourierSG (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (ξ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin r) :=
  (𝓕 u) ((2 * Real.pi)⁻¹ • ξ)

/-- The Kohn-Nirenberg formula on Schwartz inputs, using D_j = -i ∂_j. -/
def quantize
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin q) :=
  ((2 * Real.pi) ^ n)⁻¹ •
    ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • a x ξ (fourierSG u ξ)

/-- The L² Bessel coordinate of a Schwartz function, for the real order s. -/
def schwartzSobolevCoordinate (s : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (SchwartzMap.fourierMultiplierCLM (EuclideanSpace ℂ (Fin r))
    (fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)) u).toLp 2

/-- D04: the explicit Bessel coordinate realizes the original Schwartz distribution. -/
theorem besselRealization_schwartzSobolevCoordinate (s : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    besselRealization n r s (schwartzSobolevCoordinate s u) = (u : 𝓢'(_, _)) := by
  /- The coordinate is J^s u. Compatibility of Schwartz and distribution multipliers
  and the identity J^(-s) J^s = I recover the original distribution. -/
  change TemperedDistribution.besselPotential _ _ (-s)
    (schwartzSobolevCoordinate s u :
      𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) = _
  apply (TemperedDistribution.besselPotential_neg_apply_eq_iff s _ _).mpr
  -- Identify the Schwartz multiplier with the same operator on distributions.
  rw [schwartzSobolevCoordinate, TemperedDistribution.besselPotential,
    Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  exact SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)) u

/-- SR03, local form: opposite Sobolev weights give the original integral pairing. -/
theorem sobolev_pairing_schwartz (s : ℝ)
    (u v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    inner ℂ (schwartzSobolevCoordinate s u) (schwartzSobolevCoordinate (-s) v) =
      ∫ x, inner ℂ (u x) (v x) := by
  /- Plancherel moves the pairing to frequency space. The positive real weights
  (1+|ξ|²)^(s/2) and (1+|ξ|²)^(-s/2) multiply to one, giving the original
  integral pairing on Schwartz functions. Conjugate-linearity in the first slot
  identifies the conjugate-dual convention used in the subsequent Sobolev duality. -/
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let w (t : ℝ) : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (t / 2)
  have hw (t : ℝ) : (w t).HasTemperateGrowth := by
    dsimp [w]
    fun_prop
  have hweights (ξ : X) : w s ξ * w (-s) ξ = 1 := by
    dsimp [w]
    rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring]
    exact Real.rpow_zero _
  -- Plancherel turns the coordinate pairing into its frequency-space integral.
  change inner ℂ ((SchwartzMap.fourierMultiplierCLM V (w s) u).toLp 2)
    ((SchwartzMap.fourierMultiplierCLM V (w (-s)) v).toLp 2) = _
  rw [SchwartzMap.inner_toL2_toL2_eq _ _ (volume : Measure X),
    ← SchwartzMap.integral_inner_fourier_fourier]
  simp only [SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]
  calc
    _ = ∫ ξ, inner ℂ ((𝓕 u) ξ) ((𝓕 v) ξ) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      -- Real weights are unchanged by conjugation in the first inner-product slot.
      rw [SchwartzMap.smulLeftCLM_apply_apply (hw s),
        SchwartzMap.smulLeftCLM_apply_apply (hw (-s)), inner_smul_left_eq_smul,
        inner_smul_right_eq_smul, smul_smul, hweights, one_smul]
    _ = ∫ x, inner ℂ (u x) (v x) := SchwartzMap.integral_inner_fourier_fourier u v

set_option maxSynthPendingDepth 20 in
set_option maxSynthPendingDepth 20 in
/-- Every real polynomial weight, including a fixed frequency scaling, preserves Schwartz L¹. -/
private theorem weighted_schwartz_integrable {n r : ℕ} (c m : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    Integrable (fun η ↦ (1 + ‖c • η‖) ^ m * ‖u η‖) := by
  let X := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  -- Dominate the nonsmooth real weight by a smooth polynomial Bessel multiplier.
  let k : ℕ := ⌈m⌉₊
  let w : X → ℝ := fun η ↦ (1 + ‖c • η‖ ^ 2) ^ k
  have hw : w.HasTemperateGrowth := by
    have hn : (fun η : X ↦ ‖c • η‖ ^ 2).HasTemperateGrowth :=
      (Function.hasTemperateGrowth_norm_sq X).comp (by fun_prop)
    dsimp [w]
    fun_prop
  have hw0 (η : X) : 0 ≤ w η := by dsimp [w]; positivity
  have hi : Integrable (fun η ↦ w η * ‖u η‖) := by
    simpa only [SchwartzMap.smulLeftCLM_apply_apply hw, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (hw0 _)] using
      (SchwartzMap.smulLeftCLM E w u).integrable.norm
  apply (hi.const_mul (2 ^ k)).mono'
  · exact ((Continuous.rpow_const (by fun_prop) (fun η ↦ Or.inl (by positivity))).mul
      u.continuous.norm).aestronglyMeasurable
  · filter_upwards [] with η
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (1 + ‖c • η‖) ^ k * ‖u η‖ := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (c • η)])
          (Nat.le_ceil m)).trans_eq
          (Real.rpow_natCast _ _)
      _ ≤ (2 * (1 + ‖c • η‖ ^ 2)) ^ k * ‖u η‖ := by
        gcongr
        nlinarith [sq_nonneg (‖c • η‖ - 1)]
      _ = 2 ^ k * (w η * ‖u η‖) := by simp only [w, mul_pow]; ring

set_option maxSynthPendingDepth 20 in
/-- Rescaling SG frequency to mathlib frequency cancels the exact inverse Fourier factor. -/
theorem quantize_rescaled {n r q : ℕ}
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize a u x = ∫ η,
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x η : ℂ)) •
        a x ((2 * Real.pi) • η) ((𝓕 u) η) := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hchange := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • a x ξ (fourierSG u ξ))
    (2 * Real.pi) (hR := by positivity)
  simp only [finrank_euclideanSpace_fin] at hchange
  rw [quantize, ← hchange]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [fourierSG, inv_smul_smul₀ hc, inner_smul_right]
  congr 2
  push_cast
  ring

set_option maxSynthPendingDepth 20 in
/-- The original compactly supported quantization has the exact Fourier kernel weak pairing.
Both Fubini exchanges use absolute product integrability; the inner product is conjugate-linear
in the quantized input and linear in the testing function. -/
private theorem quantize_fourier_weak {n r q : ℕ} (m : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (ha : IsSymbol Set.univ m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ η, a x η = 0)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
    ∫ x, inner ℂ (quantize a u x) (v x) =
      ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        inner ℂ ((𝓕 (fun x ↦ a x ((2 * Real.pi) • z.2)) (z.1 - z.2)) ((𝓕 u) z.2))
          ((𝓕 v) z.1) := by
  -- Compute each modulated compact spatial slice with the original Fourier normalization.
  have quantize_modulation_fourier {n r q : ℕ}
      (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
      (ha : Continuous (Function.uncurry a))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hsupp : ∀ x, x ∉ K → ∀ η, a x η = 0)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (η ξ : EuclideanSpace ℝ (Fin n)) :
      𝓕 (fun x ↦ Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x η : ℂ)) •
        a x ((2 * Real.pi) • η) ((𝓕 u) η)) ξ =
        (𝓕 (fun x ↦ a x ((2 * Real.pi) • η)) (ξ - η)) ((𝓕 u) η) := by
    have hc : HasCompactSupport (fun x ↦
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x (ξ - η))) * Complex.I) •
          a x ((2 * Real.pi) • η)) := by
      apply hK.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hxK
      exact hx (by simp [hsupp x hxK])
    have hi : Integrable (fun x ↦
        Complex.exp ((↑(-2 * Real.pi * inner ℝ x (ξ - η))) * Complex.I) •
          a x ((2 * Real.pi) • η)) := by
      apply Continuous.integrable_of_hasCompactSupport _ hc
      have hca : Continuous (fun x ↦ a x ((2 * Real.pi) • η)) :=
        ha.comp (continuous_id.prodMk continuous_const)
      fun_prop
    rw [Real.fourier_eq', Real.fourier_eq', ContinuousLinearMap.integral_apply hi]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_apply, smul_smul, ← Complex.exp_add]
    congr 2
    simp only [inner_sub_right]
    push_cast
    ring
  let X := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin q)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] F
  let c : ℝ := 2 * Real.pi
  let w : X → ℝ := fun η ↦ (1 + ‖c • η‖) ^ m
  let p : X → X → ℂ := fun x η ↦
    Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x η : ℂ))
  let G : X → X → F := fun η x ↦ p x η • a x (c • η) ((𝓕 u) η)
  let B : X × X → H := fun z ↦ 𝓕 (fun x ↦ a x (c • z.2)) (z.1 - z.2)
  change (∫ x, inner ℂ (quantize a u x) (v x)) =
    ∫ z : X × X, inner ℂ (B z ((𝓕 u) z.2)) ((𝓕 v) z.1)
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  have hw0 (η : X) : 0 ≤ w η := by dsimp [w]; positivity
  have hp (x η : X) : ‖p x η‖ = 1 := by
    simp [p, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hGc : Continuous (fun z : X × X ↦ G z.2 z.1) := by
    have hac : Continuous (fun z : X × X ↦ a z.1 (c • z.2)) :=
      hsmooth.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul c))
    dsimp [G, p]
    fun_prop
  -- A global polynomial bound follows from the compact spatial support.
  obtain ⟨C, hC, hb⟩ := ha.2 K (Set.subset_univ _) hK 0 0
  have hbound (x η : X) : ‖a x (c • η)‖ ≤ C * w η := by
    by_cases hx : x ∈ K
    · simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
        using hb x hx (c • η)
    · rw [hsupp x hx, norm_zero]
      exact mul_nonneg hC (hw0 η)
  have hGbound (x η : X) : ‖G η x‖ ≤ C * w η * ‖(𝓕 u) η‖ := by
    dsimp only [G]
    rw [norm_smul, hp, one_mul]
    exact ((a x (c • η)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound x η) (norm_nonneg _))
  have hwi : Integrable (fun η ↦ w η * ‖(𝓕 u) η‖) :=
    weighted_schwartz_integrable c m (𝓕 u)
  have hGi (x : X) : Integrable (fun η ↦ G η x) := by
    apply (hwi.const_mul C).mono'
    · exact (hGc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [] with η
      simpa only [mul_assoc] using hGbound x η
  have hsp : Integrable (fun z : X × X ↦ inner ℂ (G z.2 z.1) (v z.1)) := by
    apply (v.integrable.norm.mul_prod (hwi.const_mul C)).mono'
    · exact (hGc.inner (v.continuous.comp continuous_fst)).aestronglyMeasurable
    · filter_upwards [] with z
      calc
        _ ≤ ‖G z.2 z.1‖ * ‖v z.1‖ := norm_inner_le_norm _ _
        _ ≤ (C * w z.2 * ‖(𝓕 u) z.2‖) * ‖v z.1‖ := by gcongr; exact hGbound _ _
        _ = _ := by ring
  -- Joint measurability follows directly from the parameterized Fourier integral.
  have hBm : StronglyMeasurable B := by
    have hac : Continuous (fun t : (X × X) × X ↦ a t.2 (c • t.1.2)) :=
      hsmooth.continuous.comp (continuous_snd.prodMk
        ((continuous_snd.comp continuous_fst).const_smul c))
    have hh : Continuous (fun t : (X × X) × X ↦
        Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I) •
          a t.2 (c • t.1.2)) := by fun_prop
    simpa only [B, Real.fourier_eq'] using hh.stronglyMeasurable.integral_prod_right'
  obtain ⟨D, hD, hDb⟩ := spatial_fourier_decay m a ha K hK hsupp 0
  have hBbound (z : X × X) : ‖B z‖ ≤ D * w z.2 := by
    simpa only [B, w, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
      using hDb (c • z.2) (z.1 - z.2)
  have hft : Integrable (fun z : X × X ↦
      inner ℂ (B z ((𝓕 u) z.2)) ((𝓕 v) z.1)) := by
    have hv : Integrable (fun ξ : X ↦ (𝓕 v) ξ) (volume : Measure X) := (𝓕 v).integrable
    apply (hv.norm.mul_prod (hwi.const_mul D)).mono'
    · have hm : StronglyMeasurable (fun z : X × X ↦ B z ((𝓕 u) z.2)) :=
        (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
          (hBm.prodMk ((𝓕 u).continuous.comp continuous_snd).stronglyMeasurable)
      exact (hm.inner
        ((𝓕 v).continuous.comp continuous_fst).stronglyMeasurable).aestronglyMeasurable
    · filter_upwards [] with z
      calc
        _ ≤ ‖B z ((𝓕 u) z.2)‖ * ‖(𝓕 v) z.1‖ := norm_inner_le_norm _ _
        _ ≤ (‖B z‖ * ‖(𝓕 u) z.2‖) * ‖(𝓕 v) z.1‖ := by
          gcongr
          exact (B z).le_opNorm _
        _ ≤ (D * w z.2 * ‖(𝓕 u) z.2‖) * ‖(𝓕 v) z.1‖ := by
          gcongr
          exact hBbound z
        _ = _ := by ring
  -- For fixed input frequency the modulated slice is compactly supported and smooth.
  have hGs (η : X) : HasCompactSupport (G η) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp [G, hsupp x hxK])
  have hGd (η : X) : ContDiff ℝ ∞ (G η) := by
    have had : ContDiff ℝ ∞ (fun x ↦ a x (c • η)) :=
      hsmooth.comp (contDiff_id.prodMk contDiff_const)
    have hip : ContDiff ℝ ∞ (fun x : X ↦ (inner ℝ x η : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((innerSL ℝ).flip η).contDiff
    have hval : ContDiff ℝ ∞ (fun x : X ↦ a x (c • η) ((𝓕 u) η)) := by
      let ev : H →L[ℝ] F :=
        (ContinuousLinearMap.apply ℂ F ((𝓕 u) η)).restrictScalars ℝ
      exact ev.contDiff.comp had
    dsimp [G, p]
    exact (contDiff_const.mul hip).cexp.smul hval
  let S (η : X) : 𝓢(X, F) := (hGs η).toSchwartzMap (hGd η)
  have hslice (η : X) :
      ∫ x, inner ℂ (G η x) (v x) =
        ∫ ξ, inner ℂ (B (ξ, η) ((𝓕 u) η)) ((𝓕 v) ξ) := by
    calc
      _ = ∫ ξ, inner ℂ ((𝓕 (S η)) ξ) ((𝓕 v) ξ) :=
        (SchwartzMap.integral_inner_fourier_fourier (S η) v).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        congr 1
        exact quantize_modulation_fourier a hsmooth.continuous K hK hsupp u η ξ
  -- Both Fubini exchanges are justified by the product L¹ bounds above.
  calc
    _ = ∫ x, ∫ η, inner ℂ (G η x) (v x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [quantize_rescaled]
      exact (ContinuousLinearMap.integral_comp_commSL (by simp)
        ((innerSL ℂ).flip (v x)) (hGi x)).symm
    _ = ∫ η, ∫ x, inner ℂ (G η x) (v x) := integral_integral_swap hsp
    _ = ∫ η, ∫ ξ, inner ℂ (B (ξ, η) ((𝓕 u) η)) ((𝓕 v) ξ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hslice
    _ = ∫ z : X × X, inner ℂ (B z ((𝓕 u) z.2)) ((𝓕 v) z.1) :=
      (integral_prod_symm _ hft).symm
  rfl

set_option maxSynthPendingDepth 20 in
/-- A02: a spatially compact symbol of order m acts boundedly H^s → H^(s-m). -/
theorem exists_quantize_sobolev_extension (m s : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (ha : IsSymbol Set.univ m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0) :
    ∃ P : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n q (s - m) (P (schwartzSobolevCoordinate s u)) φ =
            ∫ x, φ x • quantize a u x := by
  /- In Fourier Bessel coordinates, weight the spatial Fourier kernel of a by
  the output order s-m and the input order -s. Integration by parts and Peetre
  estimates give a Schur majorant. Construct its bounded L² operator and
  transport it back by unitary Fourier maps. The weak Fourier identity identifies
  the action on Schwartz inputs; density then gives the scalar distribution-test
  formula. Constants absorb the 2π change of Fourier convention. -/
  -- The Schur operator acts on Fourier transforms of the specified Bessel coordinates.
  have hpair :
      ∃ P : Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin q)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
          (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
          inner ℂ (P (schwartzSobolevCoordinate s u))
            (schwartzSobolevCoordinate (-(s - m)) v) =
              ∫ x, inner ℂ (quantize a u x) (v x) := by
    let X := EuclideanSpace ℝ (Fin n)
    let U := EuclideanSpace ℂ (Fin r)
    let V := EuclideanSpace ℂ (Fin q)
    let HU := Lp U 2 (volume : Measure X)
    let HV := Lp V 2 (volume : Measure X)
    let w (t : ℝ) (ξ : X) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (t / 2)
    have hw (t : ℝ) : (w t).HasTemperateGrowth := by dsimp [w]; fun_prop
    have hweights (t : ℝ) (ξ : X) : w t ξ * w (-t) ξ = 1 := by
      dsimp [w]
      rw [← Real.rpow_add (by positivity), show t / 2 + -t / 2 = 0 by ring,
        Real.rpow_zero]
    let B : X × X → U →L[ℂ] V := fun z ↦
      𝓕 (fun x ↦ a x ((2 * Real.pi) • z.2)) (z.1 - z.2)
    let H : X → X → U →L[ℂ] V := fun ξ η ↦
      (w (s - m) ξ * w (-s) η) • B (ξ, η)
    -- The original Fourier integral is jointly measurable in both frequencies.
    have hsmooth : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    have hBm : StronglyMeasurable B := by
      have hac : Continuous (fun t : (X × X) × X ↦ a t.2 ((2 * Real.pi) • t.1.2)) :=
        hsmooth.continuous.comp (continuous_snd.prodMk
          ((continuous_snd.comp continuous_fst).const_smul (2 * Real.pi)))
      have hh : Continuous (fun t : (X × X) × X ↦
          Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I) •
            a t.2 ((2 * Real.pi) • t.1.2)) := by fun_prop
      simpa only [B, Real.fourier_eq'] using
        hh.stronglyMeasurable.integral_prod_right'
    have hHm : StronglyMeasurable (Function.uncurry H) := by
      have hc : Continuous (fun z : X × X ↦ w (s - m) z.1 * w (-s) z.2) := by
        exact ((hw (s - m)).1.continuous.comp continuous_fst).mul
          ((hw (-s)).1.continuous.comp continuous_snd)
      exact hc.stronglyMeasurable.smul hBm
    -- Peetre's inequality preserves the real orders; Schur gives the frequency operator.
    obtain ⟨d, hd, hd0, hdi, hde, hbound⟩ :=
      weighted_spatial_fourier_kernel_bound m s a ha K hK hsupp
    obtain ⟨T, _, hT⟩ := exists_schur_kernel_operator H hHm d hd hd0 hdi hde hbound
    let P : HU →L[ℂ] HV := (fourierInvCLM ℂ HV).comp (T.comp (fourierCLM ℂ HU))
    refine ⟨P, ?_⟩
    intro u v
    let f : 𝓢(X, U) := SchwartzMap.smulLeftCLM U (w s) (𝓕 u)
    let g : 𝓢(X, V) := SchwartzMap.smulLeftCLM V (w (-(s - m))) (𝓕 v)
    have hin : 𝓕 (schwartzSobolevCoordinate s u) = f.toLp 2 volume := by
      rw [schwartzSobolevCoordinate, SchwartzMap.toLp_fourier_eq]
      congr 1
      simp only [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
      rfl
    have hout : 𝓕 (schwartzSobolevCoordinate (-(s - m)) v) = g.toLp 2 volume := by
      rw [schwartzSobolevCoordinate, SchwartzMap.toLp_fourier_eq]
      congr 1
      simp only [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
      rfl
    -- Unitary Fourier transport returns to the fixed spatial Bessel coordinates.
    calc
      _ = inner ℂ (𝓕 (P (schwartzSobolevCoordinate s u)))
          (𝓕 (schwartzSobolevCoordinate (-(s - m)) v)) := by
        symm
        exact Lp.inner_fourier_eq _ _
      _ = inner ℂ (T (f.toLp 2 volume)) (g.toLp 2 volume) := by
        change inner ℂ (𝓕 (𝓕⁻ (T (𝓕 (schwartzSobolevCoordinate s u))))) _ = _
        rw [fourier_fourierInv_eq, hin, hout]
      _ = ∫ z : X × X, inner ℂ (H z.1 z.2 (f z.2)) (g z.1) := hT f g
      _ = ∫ z : X × X, inner ℂ (B z ((𝓕 u) z.2)) ((𝓕 v) z.1) := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [H, f, g, SchwartzMap.smulLeftCLM_apply_apply (hw s),
          SchwartzMap.smulLeftCLM_apply_apply (hw (-(s - m))),
          smul_apply, ContinuousLinearMap.map_smul_of_tower,
          inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul]
        have hcancel : w (-(s - m)) z.1 * (w (s - m) z.1 * w (-s) z.2 * w s z.2) = 1 := by
          calc
            _ = (w (s - m) z.1 * w (-(s - m)) z.1) * (w s z.2 * w (-s) z.2) := by ring
            _ = 1 := by rw [hweights, hweights, mul_one]
        rw [hcancel, one_smul]
      _ = ∫ x, inner ℂ (quantize a u x) (v x) :=
        (quantize_fourier_weak m a ha K hK hsupp u v).symm
  -- Convert the bounded vector pairing to the original scalar distribution tests.
  have besselRealization_inner_test (t : ℝ)
      (f : Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (e : EuclideanSpace ℂ (Fin q))
      (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
      (hv : ∀ x, v x = star (φ x) • e) :
      inner ℂ (besselRealization n q t f φ) e =
        inner ℂ f (schwartzSobolevCoordinate (-t) v) := by
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin q)
    -- Opposite Bessel multipliers show that the coordinate image contains every Schwartz L² value.
    have hd : DenseRange (schwartzSobolevCoordinate (n := n) (r := q) t) := by
      let w (s : ℝ) : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
      have hw (s : ℝ) : (w s).HasTemperateGrowth := by dsimp [w]; fun_prop
      have hweights : w t * w (-t) = fun _ ↦ (1 : ℝ) := by
        funext ξ
        change (1 + ‖ξ‖ ^ 2) ^ (t / 2) * (1 + ‖ξ‖ ^ 2) ^ (-t / 2) = 1
        rw [← Real.rpow_add (by positivity), show t / 2 + -t / 2 = 0 by ring]
        exact Real.rpow_zero _
      have hinverse (u : 𝓢(X, V)) :
          SchwartzMap.fourierMultiplierCLM V (w t)
            (SchwartzMap.fourierMultiplierCLM V (w (-t)) u) = u := by
        rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (hw t) (hw (-t)),
          hweights, SchwartzMap.fourierMultiplierCLM_const]
        simp
      have hSchwartz : DenseRange (SchwartzMap.toLpCLM ℝ V 2 (volume : Measure X)) :=
        SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
      refine Dense.mono ?_ hSchwartz
      rintro _ ⟨u, rfl⟩
      refine ⟨SchwartzMap.fourierMultiplierCLM V (w (-t)) u, ?_⟩
      change (SchwartzMap.fourierMultiplierCLM V (w t)
        (SchwartzMap.fourierMultiplierCLM V (w (-t)) u)).toLp 2 = u.toLp 2
      rw [hinverse]
    -- The identity on Schwartz inputs follows from the original Sobolev pairing formula.
    have htest (u : 𝓢(X, V)) :
        inner ℂ (besselRealization n q t (schwartzSobolevCoordinate t u) φ) e =
          inner ℂ (schwartzSobolevCoordinate t u) (schwartzSobolevCoordinate (-t) v) := by
      rw [besselRealization_schwartzSobolevCoordinate, SchwartzMap.coe_apply,
        sobolev_pairing_schwartz]
      have hi : Integrable (fun x ↦ φ x • u x) :=
        (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) φ u).integrable
      calc
        _ = ∫ x, inner ℂ (φ x • u x) e :=
          (ContinuousLinearMap.integral_comp_commSL (by simp) ((innerSL ℂ).flip e) hi).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp [hv, inner_smul_left, inner_smul_right]
    -- Evaluation of the distribution and the L² inner product are continuous in the input.
    have hc : Continuous (fun g ↦ inner ℂ (besselRealization n q t g φ) e) :=
      ((continuous_eval_const φ).comp (besselRealization n q t).continuous).inner continuous_const
    exact congrFun (hd.equalizer hc (continuous_id.inner continuous_const) (funext htest)) f
  have integrable_schwartz_smul_quantize (m : ℝ)
      (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
      (ha : IsSymbol Set.univ m a)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hsupp : ∀ x, x ∉ K → ∀ η, a x η = 0)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      Integrable (fun x ↦ φ x • quantize a u x) := by
    let X := EuclideanSpace ℝ (Fin n)
    let F := EuclideanSpace ℂ (Fin q)
    let c : ℝ := 2 * Real.pi
    let w : X → ℝ := fun η ↦ (1 + ‖c • η‖) ^ m
    let G : X × X → F := fun z ↦
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ z.1 z.2 : ℂ)) •
        a z.1 (c • z.2) ((𝓕 u) z.2)
    have hsmooth : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    have hGc : Continuous G := by
      have hac : Continuous (fun z : X × X ↦ a z.1 (c • z.2)) :=
        hsmooth.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul c))
      dsimp [G]
      fun_prop
    obtain ⟨C, hC, hb⟩ := ha.2 K (Set.subset_univ _) hK 0 0
    have hbound (x η : X) : ‖a x (c • η)‖ ≤ C * w η := by
      by_cases hx : x ∈ K
      · simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
          using hb x hx (c • η)
      · rw [hsupp x hx, norm_zero]
        exact mul_nonneg hC (by dsimp [w]; positivity)
    have hGbound (x η : X) : ‖G (x, η)‖ ≤ C * (w η * ‖(𝓕 u) η‖) := by
      have hp : ‖Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x η : ℂ))‖ = 1 := by
        simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
      dsimp only [G]
      rw [norm_smul, hp, one_mul, ← mul_assoc]
      exact ((a x (c • η)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hbound x η) (norm_nonneg _))
    have hwi : Integrable (fun η ↦ C * (w η * ‖(𝓕 u) η‖)) :=
      (weighted_schwartz_integrable c m (𝓕 u)).const_mul C
    have hGi (x : X) : Integrable (fun η ↦ G (x, η)) := by
      apply hwi.mono'
      · exact (hGc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (hGbound x)
    have hQ (x : X) : quantize a u x = ∫ η, G (x, η) := quantize_rescaled a u x
    -- Parameterized integration gives measurability; the same L¹ majorant bounds every x.
    have hQm : StronglyMeasurable (quantize a u) := by
      rw [funext hQ]
      exact hGc.stronglyMeasurable.integral_prod_right'
    let M : ℝ := ∫ η, C * (w η * ‖(𝓕 u) η‖)
    have hQb (x : X) : ‖quantize a u x‖ ≤ M := by
      rw [hQ]
      exact (norm_integral_le_integral_norm _).trans
        (integral_mono (hGi x).norm hwi (hGbound x))
    apply (φ.integrable.norm.mul_const M).mono'
    · exact (φ.continuous.stronglyMeasurable.smul hQm).aestronglyMeasurable
    · filter_upwards [] with x
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hQb x) (norm_nonneg _)
  obtain ⟨P, hP⟩ := hpair
  refine ⟨P, ?_⟩
  intro u φ
  apply ext_inner_right ℂ
  intro e
  let L : ℂ →L[ℝ] EuclideanSpace ℂ (Fin q) :=
    ((ContinuousLinearMap.toSpanSingleton ℂ e).restrictScalars ℝ).comp
      Complex.conjCLE.toContinuousLinearMap
  let v := φ.postcompCLM L
  have hv (x) : v x = star (φ x) • e := rfl
  rw [besselRealization_inner_test (s - m) _ φ e v hv, hP u v]
  have hi := integrable_schwartz_smul_quantize m a ha K hK hsupp u φ
  calc
    _ = ∫ x, inner ℂ (φ x • quantize a u x) e := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [hv, inner_smul_left, inner_smul_right]
    _ = _ := ContinuousLinearMap.integral_comp_commSL (by simp) ((innerSL ℂ).flip e) hi

open scoped Topology in
set_option maxSynthPendingDepth 20 in
/-- A05, local form: spatially compact negative-order quantizations are compact on H^s. -/
theorem exists_compact_quantize_extension (m s : ℝ) (hm : m < 0)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (ha : IsSymbol Set.univ m a)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0) :
    ∃ P : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      IsCompactOperator P ∧
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n q s (P (schwartzSobolevCoordinate s u)) φ =
            ∫ x, φ x • quantize a u x := by
  /- The preceding extension maps bounded H^s sets into bounded H^(s-m) sets with
  distributional support in K. Since s-m > s, Rellich gives compact inclusion back
  into H^s. Compose the two operators and preserve the test-function identity. -/
  classical
  -- Bounded quantization improves the Sobolev order by the strictly positive amount -m.
  obtain ⟨P, hP⟩ := exists_quantize_sobolev_extension m s a ha K hK hsupp
  have horder : s < s - m := by linarith
  obtain ⟨J, _, hJ⟩ := exists_sobolev_inclusion n q (s - m) s horder.le
  -- Schwartz inputs are dense in the same original Bessel coordinates.
  have hdense : DenseRange (schwartzSobolevCoordinate (n := n) (r := r) s) := by
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let w (t : ℝ) : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (t / 2)
    have hw (t : ℝ) : (w t).HasTemperateGrowth := by
      dsimp [w]
      fun_prop
    -- Opposite Bessel weights cancel before applying the Schwartz multiplier.
    have hweights : w s * w (-s) = fun _ ↦ (1 : ℝ) := by
      funext ξ
      change (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) = 1
      rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring]
      exact Real.rpow_zero _
    have hinverse (u : 𝓢(X, V)) :
        SchwartzMap.fourierMultiplierCLM V (w s)
          (SchwartzMap.fourierMultiplierCLM V (w (-s)) u) = u := by
      rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (hw s) (hw (-s)),
        hweights, SchwartzMap.fourierMultiplierCLM_const]
      simp
    -- Every Schwartz L² value has an actual J^(-s) Schwartz preimage.
    have hdense : DenseRange (SchwartzMap.toLpCLM ℝ V 2 (volume : Measure X)) :=
      SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
    refine Dense.mono ?_ hdense
    rintro _ ⟨u, rfl⟩
    refine ⟨SchwartzMap.fourierMultiplierCLM V (w (-s)) u, ?_⟩
    change (SchwartzMap.fourierMultiplierCLM V (w s)
      (SchwartzMap.fourierMultiplierCLM V (w (-s)) u)).toLp 2 = u.toLp 2
    rw [hinverse]
  -- Spatial support is a closed fixed-test condition and therefore survives completion.
  have hsupport (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
      IsSupportedIn (besselRealization n q (s - m) (P f)) K := by
    apply (isSupportedIn_iff_compact_tests _ _ hK.isClosed).mpr
    intro φ _ hdisjoint
    let T := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) _ φ).comp
      ((besselRealization n q (s - m)).comp P)
    have hcont : Continuous (fun f ↦ besselRealization n q (s - m) (P f) φ) :=
      T.continuous
    refine hdense.induction_on f (isClosed_eq hcont continuous_const) ?_
    intro u
    rw [hP u φ]
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro x
    change φ x • quantize a u x = 0
    by_cases hx : x ∈ tsupport φ
    · have hxK : x ∉ K := fun h ↦ Set.disjoint_left.mp hdisjoint hx h
      have hzero : quantize a u x = 0 := by
        simp only [quantize, hsupp x hxK, zero_apply,
          smul_zero, integral_zero]
      rw [hzero, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  -- Rellich applies to precisely this supported range. A small input neighborhood maps
  -- into its unit ball, so its image under the specified inclusion has compact closure.
  have hcompact := rellich_compact_inclusion n q (s - m) s horder K hK J hJ
  refine ⟨J.comp P, ?_, ?_⟩
  · apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
    refine ⟨P ⁻¹' Metric.ball 0 1, ?_, _, hcompact, ?_⟩
    · exact (Metric.isOpen_ball.preimage P.continuous).mem_nhds (by simp)
    · rintro _ ⟨f, hf, rfl⟩
      apply subset_closure
      exact ⟨P f, ⟨(mem_ball_zero_iff.mp hf).le, hsupport f⟩, rfl⟩
  · intro u φ
    change besselRealization n q s (J (P (schwartzSobolevCoordinate s u))) φ = _
    rw [hJ]
    exact hP u φ

/-- A03, local form: a smooth homogeneous principal symbol has a symbol representative. -/
theorem exists_symbol_of_homogeneous (m : ℝ)
    (a₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry a₀)
      (Set.univ ×ˢ {ξ | ξ ≠ 0}))
    (hhom : IsHomogeneousSymbol Set.univ m a₀) :
    ∃ a, IsSymbol Set.univ m a ∧ ∀ x ξ, 1 ≤ ‖ξ‖ → a x ξ = a₀ x ξ := by
  /- Multiply a₀ by a smooth radial cutoff vanishing near ξ=0 and equal to one for
  |ξ|≥1. Homogeneity bounds each ξ-derivative on the unit sphere and gives the
  required decay after radial rescaling. Spatial derivatives are bounded on compact sets.
  This constructs a leading homogeneous representative, not a full polyhomogeneous series. -/
  obtain ⟨a, ha⟩ := exists_symbol_of_homogeneous_on isOpen_univ m a₀ hsmooth hhom
  exact ⟨a.val, a.property, fun x ξ hξ ↦ ha x (Set.mem_univ x) ξ hξ⟩

end AtiyahSinger
