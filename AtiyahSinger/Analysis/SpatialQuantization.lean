/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Pseudolocal

import all AtiyahSinger.Analysis.Quantization

/-!
# Quantization with only spatial derivative estimates

Public module ID: M1004.

Spatial compact support and uniform spatial derivative bounds give Fourier decay
without frequency differentiability. A measurable amplitude with smooth spatial
slices therefore has the same bounded Bessel realization whenever its actual
Fourier kernel has an integrable Schur majorant. This is used for the lifted
product symbol and its error, which need not be standard joint symbols.

The Fourier and distribution identities use the same normalization as Quantization;
the weaker hypotheses are explicit, and the Schur operator norm is retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped SchwartzMap ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ}

/-- A family of compact smooth spatial slices has Fourier decay at its given weight. -/
theorem spatial_fourier_decay_of_spatial_bounds {P : Type*}
    (a : EuclideanSpace ℝ (Fin n) → P →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hsmooth : ∀ η, ContDiff ℝ ∞ (fun x ↦ a x η))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ η, a x η = 0)
    (w : P → ℝ) (hw0 : ∀ η, 0 ≤ w η)
    (hderiv : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ η x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun y ↦ a y η) x‖ ≤ C * w η) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ζ,
      ‖𝓕 (fun x ↦ a x η) ζ‖ ≤ C * w η * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  have hw (η : P) : 0 ≤ w η := hw0 η
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have hs (η : P) : HasCompactSupport (fun x ↦ a x η) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hsupp x hxK η)
  have hsub (η : P) : tsupport (fun x ↦ a x η) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hsupp x hxK η)
  let S (η : P) : 𝓢(X, V) :=
    (hs η).toSchwartzMap (hsmooth η)
  have hseminorm (j i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η,
      SchwartzMap.seminorm ℂ j i (S η) ≤ C * w η := by
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨C, hC, hb⟩ := hderiv i
    refine ⟨(max R 0) ^ j * C, by positivity, ?_⟩
    intro η
    have hwη := hw η
    apply SchwartzMap.seminorm_le_bound ℂ j i (S η) (by positivity)
    intro x
    change ‖x‖ ^ j * ‖iteratedFDeriv ℝ i (fun x ↦ a x η) x‖ ≤ _
    by_cases hx : x ∈ K
    · calc
        _ ≤ (max R 0) ^ j * (C * w η) := by
          gcongr
          · exact (hR x hx).trans (le_max_left R 0)
          · exact hb η x hx
        _ = _ := by ring
    · have hz : iteratedFDeriv ℝ i (fun x ↦ a x η) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (hsub η (tsupport_iteratedFDeriv_subset i h)))
      rw [hz, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) hwη
  let T : 𝓢(X, V) →L[ℂ] 𝓢(X, V) := FourierTransform.fourierCLM ℂ _
  let p : Seminorm ℂ 𝓢(X, V) :=
    (Finset.Iic (N, 0)).sup (fun i ↦ SchwartzMap.seminorm ℂ i.1 i.2)
  have hp : Continuous p :=
    Seminorm.continuous_finsetSup (fun i _ ↦
      (schwartz_withSeminorms ℂ X V).continuous_seminorm i)
  obtain ⟨s, A, hA0, hA⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ X V) (p.comp T.toLinearMap) (hp.comp T.continuous)
  choose C hC hb using hseminorm
  let D := ∑ i ∈ s, C i.1 i.2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ ↦ hC i.1 i.2)
  refine ⟨2 ^ N * A * D, by positivity, ?_⟩
  intro η ζ
  have hwη := hw η
  have hsum : s.sup (schwartzSeminormFamily ℂ X V) (S η) ≤ D * w η := by
    apply Seminorm.finset_sup_apply_le
    · positivity
    · intro i hi
      exact (hb i.1 i.2 η).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ ↦ hC j.1 j.2) hi) (by positivity))
  have hweight : (1 + ‖ζ‖) ^ N * ‖T (S η) ζ‖ ≤
      (2 ^ N * A * D) * w η := by
    calc
      _ ≤ 2 ^ N * p (T (S η)) := by
        simpa only [p, schwartzSeminormFamily, iteratedFDeriv_zero_eq_comp,
          Function.comp_apply, LinearIsometryEquiv.norm_map] using
          SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
            (m := (N, 0)) (le_refl _) (le_refl _) (T (S η)) ζ
      _ ≤ 2 ^ N * (A * (s.sup (schwartzSeminormFamily ℂ X V) (S η))) :=
        mul_le_mul_of_nonneg_left (hA (S η)) (by positivity)
      _ ≤ 2 ^ N * (A * (D * w η)) := by gcongr
      _ = _ := by ring
  have hFourier : T (S η) ζ = 𝓕 (fun x ↦ a x η) ζ := rfl
  rw [hFourier] at hweight
  have hpos : 0 < 1 + ‖ζ‖ := by positivity
  calc
    _ ≤ ((2 ^ N * A * D) * w η) / (1 + ‖ζ‖) ^ N :=
      (le_div_iff₀ (pow_pos hpos N)).mpr (by simpa only [mul_comm] using hweight)
    _ = _ := by rw [Real.rpow_neg hpos.le, Real.rpow_natCast]; rfl

/-- The original compactly supported quantization has the exact Fourier kernel weak pairing.
Both Fubini exchanges use absolute product integrability; the inner product is conjugate-linear
in the quantized input and linear in the testing function. -/
private theorem quantize_fourier_weak_of_spatial_bounds {n r q : ℕ} (m : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (ham : StronglyMeasurable (Function.uncurry a))
    (has : ∀ η, ContDiff ℝ ∞ (fun x ↦ a x η))
    (hav : ∃ C : ℝ, 0 ≤ C ∧ ∀ x η, ‖a x η‖ ≤ C * (1 + ‖η‖) ^ m)
    (haf : ∃ D : ℝ, 0 ≤ D ∧ ∀ η ζ,
      ‖𝓕 (fun x ↦ a x η) ζ‖ ≤ D * (1 + ‖η‖) ^ m)
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
      (ha : ∀ η, Continuous (fun x ↦ a x η))
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
        ha _
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
  have hw0 (η : X) : 0 ≤ w η := by dsimp [w]; positivity
  have hp (x η : X) : ‖p x η‖ = 1 := by
    simp [p, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hGm : StronglyMeasurable (fun z : X × X ↦ G z.2 z.1) := by
    have hac : StronglyMeasurable (fun z : X × X ↦ a z.1 (c • z.2)) :=
      ham.comp_measurable (continuous_fst.prodMk (continuous_snd.const_smul c)).measurable
    have hev : StronglyMeasurable (fun z : X × X ↦ a z.1 (c • z.2) ((𝓕 u) z.2)) :=
      (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
        (hac.prodMk ((𝓕 u).continuous.comp continuous_snd).stronglyMeasurable)
    have he : Continuous (fun z : X × X ↦ p z.1 z.2) := by dsimp [p]; fun_prop
    exact he.stronglyMeasurable.smul hev
  -- The polynomial bound is supplied without any frequency derivatives.
  obtain ⟨C, hC, hb⟩ := hav
  have hbound (x η : X) : ‖a x (c • η)‖ ≤ C * w η := hb x (c • η)
  have hGbound (x η : X) : ‖G η x‖ ≤ C * w η * ‖(𝓕 u) η‖ := by
    dsimp only [G]
    rw [norm_smul, hp, one_mul]
    exact ((a x (c • η)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound x η) (norm_nonneg _))
  have hwi : Integrable (fun η ↦ w η * ‖(𝓕 u) η‖) :=
    weighted_schwartz_integrable c m (𝓕 u)
  have hGi (x : X) : Integrable (fun η ↦ G η x) := by
    apply (hwi.const_mul C).mono'
    · exact (hGm.comp_measurable
        (continuous_const.prodMk continuous_id).measurable).aestronglyMeasurable
    · filter_upwards [] with η
      simpa only [mul_assoc] using hGbound x η
  have hsp : Integrable (fun z : X × X ↦ inner ℂ (G z.2 z.1) (v z.1)) := by
    apply (v.integrable.norm.mul_prod (hwi.const_mul C)).mono'
    · exact (hGm.inner (v.continuous.comp continuous_fst).stronglyMeasurable).aestronglyMeasurable
    · filter_upwards [] with z
      calc
        _ ≤ ‖G z.2 z.1‖ * ‖v z.1‖ := norm_inner_le_norm _ _
        _ ≤ (C * w z.2 * ‖(𝓕 u) z.2‖) * ‖v z.1‖ := by gcongr; exact hGbound _ _
        _ = _ := by ring
  -- Joint measurability follows directly from the parameterized Fourier integral.
  have hBm : StronglyMeasurable B := by
    have hac : StronglyMeasurable (fun t : (X × X) × X ↦ a t.2 (c • t.1.2)) :=
      ham.comp_measurable (continuous_snd.prodMk
        ((continuous_snd.comp continuous_fst).const_smul c)).measurable
    have he : Continuous (fun t : (X × X) × X ↦
        Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I)) := by
      fun_prop
    have hh : StronglyMeasurable (fun t : (X × X) × X ↦
        Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I) •
          a t.2 (c • t.1.2)) := he.stronglyMeasurable.smul hac
    simpa only [B, Real.fourier_eq', Pi.smul_apply] using hh.integral_prod_right'
  obtain ⟨D, hD, hDb⟩ := haf
  have hBbound (z : X × X) : ‖B z‖ ≤ D * w z.2 := hDb (c • z.2) (z.1 - z.2)
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
      has _
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
        exact quantize_modulation_fourier a (fun η ↦ (has η).continuous) K hK hsupp u η ξ
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

set_option maxHeartbeats 800000 in
-- Fourier transport and the Schur estimate identify the original distribution tests.
/-- A measurable spatially smooth amplitude realizes its original integral, with a Schur bound. -/
theorem exists_quantize_sobolev_extension_of_spatial_bounds (m s : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (ham : StronglyMeasurable (Function.uncurry a))
    (has : ∀ η, ContDiff ℝ ∞ (fun x ↦ a x η))
    (hav : ∃ C : ℝ, 0 ≤ C ∧ ∀ x η, ‖a x η‖ ≤ C * (1 + ‖η‖) ^ m)
    (haf : ∃ D : ℝ, 0 ≤ D ∧ ∀ η ζ,
      ‖𝓕 (fun x ↦ a x η) ζ‖ ≤ D * (1 + ‖η‖) ^ m)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hdi : Integrable d) (hde : ∀ x, d (-x) = d x)
    (hbound : ∀ ξ η,
      ‖((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) •
        𝓕 (fun x ↦ a x ((2 * Real.pi) • η)) (ξ - η)‖ ≤ d (ξ - η)) :
    ∃ P : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖P‖ ≤ (∫ x, d x) ∧
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n q (s - m) (P (schwartzSobolevCoordinate s u)) φ =
            ∫ x, φ x • quantize a u x := by
  /- Only spatial regularity enters the Fourier computation. The supplied majorant
  handles the frequency variables, including symbols that fail joint symbol estimates. -/
  -- The Schur operator acts on Fourier transforms of the specified Bessel coordinates.
  have hpair :
      ∃ P : Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin q)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))),
        ‖P‖ ≤ (∫ x, d x) ∧
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
    have hBm : StronglyMeasurable B := by
      have hac : StronglyMeasurable (fun t : (X × X) × X ↦ a t.2 ((2 * Real.pi) • t.1.2)) :=
        ham.comp_measurable (continuous_snd.prodMk
          ((continuous_snd.comp continuous_fst).const_smul (2 * Real.pi))).measurable
      have he : Continuous (fun t : (X × X) × X ↦
          Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I)) := by
        fun_prop
      have hh : StronglyMeasurable (fun t : (X × X) × X ↦
          Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I) •
            a t.2 ((2 * Real.pi) • t.1.2)) := he.stronglyMeasurable.smul hac
      simpa only [B, Real.fourier_eq', Pi.smul_apply] using hh.integral_prod_right'
    have hHm : StronglyMeasurable (Function.uncurry H) := by
      have hc : Continuous (fun z : X × X ↦ w (s - m) z.1 * w (-s) z.2) := by
        exact ((hw (s - m)).1.continuous.comp continuous_fst).mul
          ((hw (-s)).1.continuous.comp continuous_snd)
      exact hc.stronglyMeasurable.smul hBm
    -- Schur's norm survives the unitary Fourier transport into Bessel coordinates.
    obtain ⟨T, hTnorm, hT⟩ := exists_schur_kernel_operator H hHm d hd hd0 hdi hde hbound
    let P : HU →L[ℂ] HV := (fourierInvCLM ℂ HV).comp (T.comp (fourierCLM ℂ HU))
    have hPnorm : ‖P‖ ≤ ∫ x, d x := by
      apply P.opNorm_le_bound (integral_nonneg hd0)
      intro u
      change ‖𝓕⁻ (T (𝓕 u))‖ ≤ _
      have hF : ‖𝓕⁻ (T (𝓕 u))‖ = ‖T (𝓕 u)‖ := by
        simpa only [fourier_fourierInv_eq] using
          (Lp.norm_fourier_eq (f := 𝓕⁻ (T (𝓕 u)))).symm
      rw [hF]
      apply (T.le_opNorm _).trans
      rw [Lp.norm_fourier_eq]
      exact mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _)
    refine ⟨P, hPnorm, ?_⟩
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
        (quantize_fourier_weak_of_spatial_bounds m a ham has hav haf K hK hsupp u v).symm
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
      (ham : StronglyMeasurable (Function.uncurry a))
      (hav : ∃ C : ℝ, 0 ≤ C ∧ ∀ x η, ‖a x η‖ ≤ C * (1 + ‖η‖) ^ m)
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
    have hGm : StronglyMeasurable G := by
      have hac : StronglyMeasurable (fun z : X × X ↦ a z.1 (c • z.2)) :=
        ham.comp_measurable (continuous_fst.prodMk (continuous_snd.const_smul c)).measurable
      have hev : StronglyMeasurable (fun z : X × X ↦ a z.1 (c • z.2) ((𝓕 u) z.2)) :=
        (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
          (hac.prodMk ((𝓕 u).continuous.comp continuous_snd).stronglyMeasurable)
      have he : Continuous (fun z : X × X ↦
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ z.1 z.2 : ℂ))) := by fun_prop
      exact he.stronglyMeasurable.smul hev
    obtain ⟨C, hC, hb⟩ := hav
    have hbound (x η : X) : ‖a x (c • η)‖ ≤ C * w η := hb x (c • η)
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
      · exact (hGm.comp_measurable
          (continuous_const.prodMk continuous_id).measurable).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (hGbound x)
    have hQ (x : X) : quantize a u x = ∫ η, G (x, η) := quantize_rescaled a u x
    -- Parameterized integration gives measurability; the same L¹ majorant bounds every x.
    have hQm : StronglyMeasurable (quantize a u) := by
      rw [funext hQ]
      exact hGm.integral_prod_right'
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
  obtain ⟨P, hPnorm, hP⟩ := hpair
  refine ⟨P, hPnorm, ?_⟩
  intro u φ
  apply ext_inner_right ℂ
  intro e
  let L : ℂ →L[ℝ] EuclideanSpace ℂ (Fin q) :=
    ((ContinuousLinearMap.toSpanSingleton ℂ e).restrictScalars ℝ).comp
      Complex.conjCLE.toContinuousLinearMap
  let v := φ.postcompCLM L
  have hv (x) : v x = star (φ x) • e := rfl
  rw [besselRealization_inner_test (s - m) _ φ e v hv, hP u v]
  have hi := integrable_schwartz_smul_quantize m a ham hav u φ
  calc
    _ = ∫ x, inner ℂ (φ x • quantize a u x) e := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [hv, inner_smul_left, inner_smul_right]
    _ = _ := ContinuousLinearMap.integral_comp_commSL (by simp) ((innerSL ℂ).flip e) hi

end AtiyahSinger
