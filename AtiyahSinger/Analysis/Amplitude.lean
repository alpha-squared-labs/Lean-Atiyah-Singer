/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Quantization
public import AtiyahSinger.Analysis.SymbolQuotient

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Group.Prod

/-!
# Compactly supported amplitudes and reduction to symbols

Public module ID: M0075.

D05/A02: SG Workhorse Theorem 3.5, (3.4)-(3.6), and Observation 3.6.
The compact support hypothesis is on (x,y) uniformly in frequency, expressed by
`HasCompactSupport (Function.uncurry a)`. It is not compact frequency support.
All integrals are actual iterated Bochner integrals, with y integrated first.
No interchange with a generally nonintegrable joint (y,ξ) integral is assumed.

The expansion uses ordinary real derivatives and the coefficient (-i)^j/j!.
Summing over ordered coordinate lists converts this to (-i)^|α|/α!, or to
SG's i^|α| D_ξ^α D_y^α/α! when D = -i∂. Differentiate before setting y = x.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap


set_option maxSynthPendingDepth 15

/-- Matrix-valued amplitudes, with output position x, input position y, and frequency ξ. -/
abbrev AmplitudeFunction (n r q : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))

variable {n r q : ℕ}

/-- The actual mixed derivative, taken in ξ, then y, then x. -/
def amplitudeDerivative (a : AmplitudeFunction n r q) (i j k : ℕ)
    (x y ξ : EuclideanSpace ℝ (Fin n)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin n))
      (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n))
        (ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))) :=
  iteratedFDeriv ℝ i
    (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ iteratedFDeriv ℝ k (a z w) ξ) y) x

/-- Standard type-(1,0) amplitude estimates, locally in the two spatial variables. -/
def IsAmplitude (m : ℝ) (a : AmplitudeFunction n r q) : Prop :=
  ContDiff ℝ ∞ (fun z :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) ↦
      a z.1.1 z.1.2 z.2) ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∀ i j k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
        ‖amplitudeDerivative a i j k x y ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (k : ℝ))

/-- SG (3.4): the iterated amplitude integral, with y integrated before ξ. -/
def amplitudeApply (a : AmplitudeFunction n r q)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin q) :=
  ((2 * Real.pi) ^ n)⁻¹ •
    ∫ ξ, ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y)

/-- The integral formula for the reduced Kohn-Nirenberg symbol, integrating in y first. -/
def amplitudeSymbol (a : AmplitudeFunction n r q) : SymbolFunction n r q :=
  fun x η ↦ ((2 * Real.pi) ^ n)⁻¹ •
    ∫ ζ, ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)

/-- The degree-j term of SG (3.5), with ordinary derivatives and ordered coordinate lists. -/
def amplitudeExpansionTerm (a : AmplitudeFunction n r q) (j : ℕ) : SymbolFunction n r q :=
  fun x ξ ↦ ((-Complex.I) ^ j / (j.factorial : ℂ)) •
    ∑ α : Fin j → Fin n,
      iteratedFDeriv ℝ j (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ a x y η) x) ξ
        (fun t ↦ EuclideanSpace.single (α t) 1)
        (fun t ↦ EuclideanSpace.single (α t) 1)

/-- Smoothness and uniform compact spatial support give integrability of the inner integral. -/
theorem integrable_amplitudeApply_inner (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
      a x y ξ (u y)) := by
  /- The y support lies in the compact second projection of the uniform spatial support.
  Joint smoothness of the amplitude and smoothness of u give continuity of the
  integrand. A continuous compactly supported function is Bochner integrable. -/
  -- Fixing output position and frequency gives a continuous matrix-valued function of y.
  have haCont : Continuous (fun y ↦ a x y ξ) :=
    ha.1.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hphase : Continuous (fun y : EuclideanSpace ℝ (Fin n) ↦
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ))) := by
    fun_prop
  have hcont := hphase.smul (haCont.clm_apply u.continuous)
  -- The compact second projection is uniform in both fixed parameters.
  have hK : IsCompact (Prod.snd '' tsupport (Function.uncurry a)) :=
    hsupp.image continuous_snd
  have hcompact : HasCompactSupport (fun y ↦
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y)) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    have hzero : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (show (x, y) ∉ tsupport (Function.uncurry a) from
        fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    change a x y = 0 at hzero
    apply hy
    simp [hzero]
  exact hcont.integrable_of_hasCompactSupport hcompact

open scoped FourierTransform in
/-- A uniformly compact smooth family with polynomial derivative growth has rapidly
  decaying Fourier transform along every nonzero scalar frequency diagonal. -/
theorem fourier_diagonal_decay_of_compact_support {ι : Type*} {n : ℕ} {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
    (hf : ∀ t ξ, ContDiff ℝ ∞ (f t ξ))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ t ξ, tsupport (f t ξ) ⊆ K) (d : ℕ)
    (hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ y, y ∈ K →
      ‖iteratedFDeriv ℝ i (f t ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ d)
    (c : ℝ) (hc : c ≠ 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ,
      ‖𝓕 (f t ξ) (c • ξ)‖ ≤ C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  have schwartz_decay {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (f : ι → EuclideanSpace ℝ (Fin n) → 𝓢(EuclideanSpace ℝ (Fin n), W))
      (d : ℕ)
      (hb : ∀ k i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ,
        SchwartzMap.seminorm ℂ k i (f t ξ) ≤ C * (1 + ‖ξ‖) ^ d)
      (c : ℝ) (hc : c ≠ 0) (k : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ,
        ‖𝓕 (f t ξ) (c • ξ)‖ ≤ C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    -- Rescaling the Fourier transform is a continuous operator on Schwartz space.
    let V := EuclideanSpace ℝ (Fin n)
    let e : V ≃L[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V c hc).toContinuousLinearEquiv
    let T : 𝓢(V, W) →L[ℂ] 𝓢(V, W) :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e).comp (FourierTransform.fourierCLM ℂ _)
    let p : Seminorm ℂ 𝓢(V, W) :=
      (Finset.Iic (d + k, 0)).sup (fun i ↦ SchwartzMap.seminorm ℂ i.1 i.2)
    let q : Seminorm ℂ 𝓢(V, W) := p.comp T.toLinearMap
    have hp : Continuous p :=
      Seminorm.continuous_finsetSup (fun i _ ↦ (schwartz_withSeminorms ℂ V W).continuous_seminorm i)
    obtain ⟨s, A, _, hA⟩ := Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℂ V W) q (hp.comp T.continuous)
    choose C hC hbound using hb
    let B := ∑ i ∈ s, C i.1 i.2
    have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ ↦ hC i.1 i.2)
    refine ⟨2 ^ (d + k) * A * B, by positivity, ?_⟩
    intro t ξ
    have hT : T (f t ξ) ξ = 𝓕 (f t ξ) (c • ξ) := rfl
    have hs : s.sup (schwartzSeminormFamily ℂ V W) (f t ξ) ≤ B * (1 + ‖ξ‖) ^ d := by
      apply Seminorm.finset_sup_apply_le
      · positivity
      · intro i hi
        exact (hbound i.1 i.2 t ξ).trans (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j _ ↦ hC j.1 j.2) hi) (by positivity))
    have hweight : (1 + ‖ξ‖) ^ (d + k) * ‖T (f t ξ) ξ‖ ≤
        (2 ^ (d + k) * A * B) * (1 + ‖ξ‖) ^ d := by
      calc
        _ ≤ 2 ^ (d + k) * p (T (f t ξ)) := by
          simpa only [p, schwartzSeminormFamily, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
            LinearIsometryEquiv.norm_map] using
            SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
              (m := (d + k, 0)) (le_refl _) (le_refl _) (T (f t ξ)) ξ
        _ ≤ 2 ^ (d + k) * (A * (s.sup (schwartzSeminormFamily ℂ V W) (f t ξ))) :=
          mul_le_mul_of_nonneg_left (hA (f t ξ)) (by positivity)
        _ ≤ 2 ^ (d + k) * (A * (B * (1 + ‖ξ‖) ^ d)) := by gcongr
        _ = _ := by ring
    have hpos : 0 < 1 + ‖ξ‖ := by positivity
    have hcancel : (1 + ‖ξ‖) ^ k * ‖T (f t ξ) ξ‖ ≤ 2 ^ (d + k) * A * B := by
      apply (mul_le_mul_iff_right₀ (pow_pos hpos d)).mp
      simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hweight
    calc
      _ ≤ (2 ^ (d + k) * A * B) / (1 + ‖ξ‖) ^ k :=
        (le_div_iff₀ (pow_pos hpos k)).mpr (by simpa only [hT, mul_comm] using hcancel)
      _ = _ := by rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_natCast]; rfl
  -- Uniform compact support turns the derivative estimates into Schwartz seminorm estimates.
  let S (t : ι) (ξ : EuclideanSpace ℝ (Fin n)) : 𝓢(EuclideanSpace ℝ (Fin n), W) :=
    (show HasCompactSupport (f t ξ) from
      hK.of_isClosed_subset (isClosed_tsupport _) (hsupp t ξ)).toSchwartzMap (hf t ξ)
  have hseminorm (j i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ,
      SchwartzMap.seminorm ℂ j i (S t ξ) ≤ C * (1 + ‖ξ‖) ^ d := by
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨C, hC, hbound⟩ := hb i
    refine ⟨(max R 0) ^ j * C, by positivity, ?_⟩
    intro t ξ
    apply SchwartzMap.seminorm_le_bound ℂ j i (S t ξ) (by positivity)
    intro y
    change ‖y‖ ^ j * ‖iteratedFDeriv ℝ i (f t ξ) y‖ ≤ _
    by_cases hy : y ∈ K
    · calc
        _ ≤ (max R 0) ^ j * (C * (1 + ‖ξ‖) ^ d) := by
          gcongr
          · exact (hR y hy).trans (le_max_left R 0)
          · exact hbound t ξ y hy
        _ = _ := by ring
    · have hz : iteratedFDeriv ℝ i (f t ξ) y = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hy (hsupp t ξ (tsupport_iteratedFDeriv_subset i h)))
      rw [hz, norm_zero, mul_zero]
      positivity
  obtain ⟨C, hC, hbound⟩ := schwartz_decay S d hseminorm c hc k
  exact ⟨C, hC, fun t ξ ↦ hbound t ξ⟩

open scoped FourierTransform in
/-- Under the amplitude estimates and uniform compact spatial support, the outer
frequency integral in (3.4) is integrable at every real order. -/
theorem integrable_amplitudeApply_outer (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ξ ↦ ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y)) := by
  /- The compact y support makes each fixed-frequency product a(x,y,ξ)u(y) a
  Schwartz function. Amplitude bounds give a common polynomial frequency bound for
  its y derivatives. The uniform Fourier-Schwartz estimate then gives decay of
  order -(n+1) on the scaled frequency diagonal, which is integrable. This does
  not require absolute integrability of the joint spatial-frequency integrand. -/

  -- The spatial derivative bounds have a common polynomial frequency order.
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let H := E →L[ℂ] F
  let K : Set V := Prod.snd '' tsupport (Function.uncurry a)
  have hK : IsCompact K := hsupp.image continuous_snd
  have hab (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, y ∈ K → ∀ ξ,
      ‖iteratedFDeriv ℝ j (fun y ↦ a x y ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := ha.2 ({x} ×ˢ K) (isCompact_singleton.prod hK) 0 j 0
    refine ⟨C, hC, ?_⟩
    intro y hy ξ
    have hb := hbound x y ⟨Set.mem_singleton x, hy⟩ ξ
    have hzero : (fun w ↦ iteratedFDeriv ℝ 0 (a x w) ξ) =
        (continuousMultilinearCurryFin0 ℝ V H).symm ∘ (fun w ↦ a x w ξ) := by
      funext w
      exact congrFun iteratedFDeriv_zero_eq_comp ξ
    simp only [amplitudeDerivative, norm_iteratedFDeriv_zero, hzero,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.cast_zero, sub_zero] at hb
    calc
      _ ≤ C * (1 + ‖ξ‖) ^ m := hb
      _ ≤ C * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)) hC
      _ = _ := by rw [Real.rpow_natCast]
  let f (_ : Unit) (ξ y : V) : F := a x y ξ (u y)
  let B : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
  have haSmooth (ξ : V) : ContDiff ℝ ∞ (fun y ↦ a x y ξ) :=
    ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hf (_ : Unit) (ξ : V) : ContDiff ℝ ∞ (f () ξ) :=
    (B.contDiff.comp (haSmooth ξ)).clm_apply (u.smooth ⊤)
  have hsupport (t : Unit) (ξ : V) : tsupport (f t ξ) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    have hz : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (show (x, y) ∉ tsupport (Function.uncurry a) from fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    change a x y = 0 at hz
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
          ‖iteratedFDeriv ℝ i (fun y ↦ a x y ξ) y‖ *
          ‖iteratedFDeriv ℝ (j - i) u y‖ :=
        B.norm_iteratedFDeriv_le_of_bilinear (haSmooth ξ) (u.smooth ⊤) y (by simp)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (C i * (1 + ‖ξ‖) ^ ⌈m⌉₊) * SchwartzMap.seminorm ℂ 0 (j - i) u := by
        apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro i _
        have hiC := hC i
        gcongr
        · exact hbound i y hy ξ
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
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  obtain ⟨C, hC, hdecay⟩ := fourier_diagonal_decay_of_compact_support
    f hf K hK hsupport ⌈m⌉₊ hb c hc (n + 1)
  have hid (ξ : V) : (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
      a x y ξ (u y)) =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • 𝓕 (f () ξ) (c • ξ) := by
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
  have hcont : Continuous (fun z : V × V ↦
      Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ)) • a x z.2 z.1 (u z.2)) := by
    have hphase : Continuous (fun z : V × V ↦
        Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ))) := by fun_prop
    exact hphase.smul ((ha.1.continuous.comp
      ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)).clm_apply
        (u.continuous.comp continuous_snd))
  have hi : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by simp [V])
  apply (hi.const_mul C).mono' hcont.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards with ξ
  rw [hid, norm_smul]
  simpa [Complex.norm_exp, Complex.mul_re] using hdecay () ξ

/-- The matrix-valued inner integral defining the reduced symbol is integrable. -/
theorem integrable_amplitudeSymbol_inner (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (x η ζ : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦
      Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)) := by
  /- Fix the two frequencies and x. The integrand is continuous and supported in
  the compact y projection of the spatial support. Its finite-dimensional matrix
  target is complete, so the standard compact-support integrability criterion applies. -/
  -- The translated frequency is fixed before applying continuity and compact support.
  have haCont : Continuous (fun y ↦ a x y (η + ζ)) :=
    ha.1.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hphase : Continuous (fun y : EuclideanSpace ℝ (Fin n) ↦
      Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ))) := by
    fun_prop
  have hK : IsCompact (Prod.snd '' tsupport (Function.uncurry a)) :=
    hsupp.image continuous_snd
  have hcompact : HasCompactSupport (fun y ↦
      Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    have hzero : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (show (x, y) ∉ tsupport (Function.uncurry a) from
        fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    change a x y = 0 at hzero
    apply hy
    simp [hzero]
  exact (hphase.smul haCont).integrable_of_hasCompactSupport hcompact

open scoped FourierTransform in
/-- The partial Fourier transform in y decays sufficiently in ζ to define the reduced symbol. -/
theorem integrable_amplitudeSymbol_outer (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (x η : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ζ ↦ ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)) := by
  /- With x and η fixed, the compact y family a(x,y,η+ζ) is smooth and its
  y derivatives have a common polynomial growth bound in ζ. The uniform
  Fourier-Schwartz estimate yields decay of order -(n+1) on the scaled ζ
  diagonal. That bound makes the outer integral integrable without requiring
  absolute integrability of the joint spatial-frequency integrand. -/

  -- The spatial derivative bounds have a common polynomial frequency order.
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let K : Set V := Prod.snd '' tsupport (Function.uncurry a)
  have hK : IsCompact K := hsupp.image continuous_snd
  have hab (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, y ∈ K → ∀ ξ,
      ‖iteratedFDeriv ℝ j (fun y ↦ a x y ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := ha.2 ({x} ×ˢ K) (isCompact_singleton.prod hK) 0 j 0
    refine ⟨C, hC, ?_⟩
    intro y hy ξ
    have hb := hbound x y ⟨Set.mem_singleton x, hy⟩ ξ
    have hzero : (fun w ↦ iteratedFDeriv ℝ 0 (a x w) ξ) =
        (continuousMultilinearCurryFin0 ℝ V H).symm ∘ (fun w ↦ a x w ξ) := by
      funext w
      exact congrFun iteratedFDeriv_zero_eq_comp ξ
    simp only [amplitudeDerivative, norm_iteratedFDeriv_zero, hzero,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.cast_zero, sub_zero] at hb
    calc
      _ ≤ C * (1 + ‖ξ‖) ^ m := hb
      _ ≤ C * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)) hC
      _ = _ := by rw [Real.rpow_natCast]
  let f (_ : Unit) (ξ y : V) : H := a x y (η + ξ)
  have hf (_ : Unit) (ξ : V) : ContDiff ℝ ∞ (f () ξ) :=
    ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hsupport (t : Unit) (ξ : V) : tsupport (f t ξ) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    have hz : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (show (x, y) ∉ tsupport (Function.uncurry a) from fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    change a x y = 0 at hz
    exact hy (by simp [f, hz])
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ y, y ∈ K →
      ‖iteratedFDeriv ℝ j (f t ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := hab j
    refine ⟨C * (1 + ‖η‖) ^ ⌈m⌉₊, by positivity, ?_⟩
    intro t ξ y hy
    have hadd : 1 + ‖η + ξ‖ ≤ (1 + ‖η‖) * (1 + ‖ξ‖) := by
      nlinarith [norm_add_le η ξ, norm_nonneg η, norm_nonneg ξ]
    calc
      _ ≤ C * (1 + ‖η + ξ‖) ^ ⌈m⌉₊ := hbound y hy (η + ξ)
      _ ≤ C * ((1 + ‖η‖) * (1 + ‖ξ‖)) ^ ⌈m⌉₊ := by gcongr
      _ = _ := by rw [mul_pow]; ring
  -- Fourier decay controls the diagonal frequency, without joint absolute integrability.
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  obtain ⟨C, hC, hdecay⟩ := fourier_diagonal_decay_of_compact_support
    f hf K hK hsupport ⌈m⌉₊ hb c hc (n + 1)
  have hid (ξ : V) : (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
      a x y (η + ξ)) =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • 𝓕 (f () ξ) (c • ξ) := by
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
  have hcont : Continuous (fun z : V × V ↦
      Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ)) • a x z.2 (η + z.1)) := by
    have hphase : Continuous (fun z : V × V ↦
        Complex.exp (Complex.I * (inner ℝ (x - z.2) z.1 : ℂ))) := by fun_prop
    exact hphase.smul (ha.1.continuous.comp
      ((continuous_const.prodMk continuous_snd).prodMk (continuous_const.add continuous_fst)))
  have hi : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by simp [V])
  apply (hi.const_mul C).mono' hcont.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards with ξ
  rw [hid, norm_smul]
  simpa [Complex.norm_exp, Complex.mul_re] using hdecay () ξ

/-- The leading term is the diagonal restriction of the amplitude. -/
theorem amplitudeExpansionTerm_zero (a : AmplitudeFunction n r q) :
    amplitudeExpansionTerm a 0 = fun x ξ ↦ a x x ξ := by
  /- There is exactly one coordinate list of length zero, and both zeroth iterated
  derivatives evaluate the original function. The factor (-i)^0/0! is one,
  leaving precisely the diagonal restriction with no extra Fourier normalization. -/
  -- The unique empty coordinate list leaves the same diagonal value.
  funext x ξ
  simp [amplitudeExpansionTerm, iteratedFDeriv_zero_apply]

set_option maxHeartbeats 2000000 in

/-- Each degree-j amplitude coefficient is a symbol of order m-j. -/
theorem isSymbol_amplitudeExpansionTerm (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (j : ℕ) :
    IsSymbol Set.univ (m - (j : ℝ)) (amplitudeExpansionTerm a j) := by
  /- Differentiate first and then restrict to y=x. Each spatial derivative of that
  restriction splits between x and y; these derivatives do not change the order.
  The built-in j frequency derivatives lower the order by j, and further frequency
  derivatives lower it again. Bound the finite coordinate contractions on the compact
  diagonal image of each compact x set. This statement needs no compact spatial support. -/
  -- Commute the actual partial derivatives through the symmetric full Hessian.
  have mixed_fderiv_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v := by
    let F := Function.uncurry f
    let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
    let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
    have hF : Differentiable ℝ F := hf.differentiable (by simp)
    have hDF : Differentiable ℝ (fderiv ℝ F) :=
      (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp)
    -- Each partial first derivative is the full derivative restricted to one factor.
    have hleft (a : X) (b : Y) :
        fderiv ℝ (fun t ↦ f t b) a = (fderiv ℝ F (a, b)).comp L := by
      exact ((hF (a, b)).hasFDerivAt.comp a
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)).fderiv
    have hright (a : X) (b : Y) :
        fderiv ℝ (f a) b = (fderiv ℝ F (a, b)).comp R :=
      ((hF (a, b)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right (𝕜 := ℝ) a b)).fderiv
    -- Differentiate those restrictions through fixed continuous linear composition maps.
    have hxy : fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fderiv ℝ F) (x, y) (0, v) (u, 0) := by
      simp_rw [hleft]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] X →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ X (X × Y) V).flip L
      have hd := (hDF (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp y hd
      exact congrArg (fun K : Y →L[ℝ] X →L[ℝ] V ↦ K v u) hc.fderiv
    have hyx : fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v =
        fderiv ℝ (fderiv ℝ F) (x, y) (u, 0) (0, v) := by
      simp_rw [hright]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] Y →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ Y (X × Y) V).flip R
      have hd := (hDF (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp x hd
      exact congrArg (fun K : X →L[ℝ] Y →L[ℝ] V ↦ K u v) hc.fderiv
    -- Symmetry applies on the full product, with the original two factor directions.
    rw [hxy, hyx]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (0, v) (u, 0)
  have mixed_fderiv_apply_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u := by
    have hl : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) := by
      have hh : ContDiff ℝ ∞ (Function.uncurry (fun z t ↦ f t z)) :=
        hf.comp (contDiff_snd.prodMk contDiff_fst)
      exact hh.fderiv contDiff_const (by simp)
    have hr : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (f t) y) :=
      hf.fderiv contDiff_const (by simp)
    rw [fderiv_clm_apply (hl.differentiable (by simp) y) (differentiableAt_const u),
      fderiv_clm_apply (hr.differentiable (by simp) x) (differentiableAt_const v)]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using mixed_fderiv_comm f hf x y u v
  have parametric {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  have iterated_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : X → Y → W) (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : X) (y : Y)
      (u : X) :
      iteratedFDeriv ℝ k (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y =
        fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) y) x u := by
    induction k generalizing y with
    | zero =>
      let J := (continuousMultilinearCurryFin0 ℝ Y V).symm.toContinuousLinearEquiv
      exact (congrArg (fun T : X →L[ℝ] Y [×0]→L[ℝ] V ↦ T u)
        (J.comp_fderiv (f := fun t ↦ f t y) (x := x))).symm
    | succ k ih =>
      ext v
      have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
        parametric f hf k
      rw [iteratedFDeriv_succ_apply_left]
      have hi : (fun z ↦ iteratedFDeriv ℝ k
          (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) =
          (fun z ↦ fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) z) x u) := by
        funext z
        exact ih z
      change ((fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k
        (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) y) (v 0)) (Fin.tail v) = _
      rw [hi]
      have hc := comm (fun t z ↦ iteratedFDeriv ℝ k (f t) z) hs x y u (v 0)
      rw [hc]
      have hd : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun t : X ↦ fun z : Y ↦ iteratedFDeriv ℝ k (f t) z)) := hs
        exact h.fderiv contDiff_const (by simp)
      have heq : (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y v) =
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0) (Fin.tail v)) := by
        funext t
        exact iteratedFDeriv_succ_apply_left v
      have hx : ContDiff ℝ ∞ (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y) :=
        (parametric f hf (k + 1)).comp (contDiff_id.prodMk contDiff_const)
      have ha : ContDiff ℝ ∞
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0)) :=
        hd.clm_apply contDiff_const
      rw [← fderiv_continuousMultilinear_apply_const_apply
        (hx.contDiffAt.differentiableAt (by simp)), heq,
        fderiv_continuousMultilinear_apply_const_apply (ha.contDiffAt.differentiableAt (by simp))]
  let mixed {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      P [×i]→L[ℝ] P [×j]→L[ℝ] V :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  have mixed_map_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (L : V →L[ℝ] W) (f : P → P → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ L (f y η)) i j x ξ‖ ≤ ‖L‖ * ‖mixed f i j x ξ‖ := by
    let T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ P) V W L
    have hT : ‖T‖ ≤ ‖L‖ := by
      apply T.opNorm_le_bound (norm_nonneg _)
      intro v
      exact L.norm_compContinuousMultilinearMap_le v
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ L (f y η)) ξ) =
        T ∘ (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) := by
      funext y
      exact L.iteratedFDeriv_comp_left
        ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt) (by simp)
    unfold mixed
    rw [heq]
    exact (T.norm_iteratedFDeriv_comp_left
      (((parametric f hf j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt)
        (by simp)).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have mixed_shift {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  -- Separated spatial derivatives control restriction to the same spatial diagonal.
  have mixed_left_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y u : P) :
      ‖mixed (fun a b ↦ fderiv ℝ (fun z ↦ f z b) a u) i j x y‖ ≤
        ‖u‖ * ‖mixed f (i + 1) j x y‖ := by
    have heq : (fun a ↦ iteratedFDeriv ℝ j
        (fun b ↦ fderiv ℝ (fun z ↦ f z b) a u) y) =
        (fun a ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j (f z) y) a u) := by
      funext a
      exact iterated_comm mixed_fderiv_apply_comm f hf j a y u
    unfold mixed
    rw [heq]
    have hs : ContDiff ℝ ∞ (fun a ↦ iteratedFDeriv ℝ j (f a) y) :=
      (parametric f hf j).comp (contDiff_id.prodMk contDiff_const)
    have hds : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y)) :=
      hs.fderiv_right (by simp)
    have h := norm_iteratedFDeriv_clm_apply_const hds.contDiffAt (x := x) (n := i)
      (c := u) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at h
    exact h
  have mixed_right_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y u : P) :
      ‖mixed (fun a b ↦ fderiv ℝ (f a) b u) i j x y‖ ≤
        ‖u‖ * ‖mixed f i (j + 1) x y‖ := by
    have hd : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (f z.1) z.2) := by
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : P × P ↦ fun b : P ↦ f z.1 b)) :=
        hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact h.fderiv contDiff_snd (by simp)
    let L : (P →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V u
    have hL : ‖L‖ ≤ ‖u‖ := by
      apply L.opNorm_le_bound (norm_nonneg _)
      intro T
      exact (T.le_opNorm u).trans_eq (mul_comm _ _)
    have h := mixed_map_bound L (fun a b ↦ fderiv ℝ (f a) b) hd i j x y
    rw [mixed_shift] at h
    exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have diagonal_bound {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      (i : ℕ) : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V), ContDiff ℝ ∞ (Function.uncurry f) →
      ∀ (x : P) (A : ℝ), 0 ≤ A →
      (∀ a ≤ i, ∀ b ≤ i, ‖mixed f a b x x‖ ≤ A) →
      ‖iteratedFDeriv ℝ i (fun z ↦ f z z) x‖ ≤ 2 ^ i * A := by
    induction i with
    | zero =>
      intro V _ _ f hf x A hA hbound
      simpa only [mixed, norm_iteratedFDeriv_zero, pow_zero, one_mul] using
        hbound 0 le_rfl 0 le_rfl
    | succ i ih =>
      intro V _ _ f hf x A hA hbound
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro v
      let u := v (Fin.last i)
      let fl (a b : P) : V := fderiv ℝ (fun z ↦ f z b) a u
      let fr (a b : P) : V := fderiv ℝ (f a) b u
      have hfl : ContDiff ℝ ∞ (Function.uncurry fl) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun a : P ↦ f a z.2)) :=
          hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
        exact (h.fderiv contDiff_fst (by simp)).clm_apply contDiff_const
      have hfr : ContDiff ℝ ∞ (Function.uncurry fr) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun b : P ↦ f z.1 b)) :=
          hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact (h.fderiv contDiff_snd (by simp)).clm_apply contDiff_const
      have hleft : ‖iteratedFDeriv ℝ i (fun z ↦ fl z z) x‖ ≤ 2 ^ i * (‖u‖ * A) := by
        apply ih fl hfl x (‖u‖ * A) (mul_nonneg (norm_nonneg _) hA)
        intro a ha b hb
        exact (mixed_left_bound f hf a b x x u).trans
          (mul_le_mul_of_nonneg_left
            (hbound (a + 1) (Nat.add_le_add_right ha 1) b (Nat.le.step hb)) (norm_nonneg _))
      have hright : ‖iteratedFDeriv ℝ i (fun z ↦ fr z z) x‖ ≤ 2 ^ i * (‖u‖ * A) := by
        apply ih fr hfr x (‖u‖ * A) (mul_nonneg (norm_nonneg _) hA)
        intro a ha b hb
        exact (mixed_right_bound f hf a b x x u).trans
          (mul_le_mul_of_nonneg_left
            (hbound a (Nat.le.step ha) (b + 1) (Nat.add_le_add_right hb 1)) (norm_nonneg _))
      have hdiag : (fun z ↦ fderiv ℝ (fun t ↦ f t t) z u) =
          (fun z ↦ fl z z) + (fun z ↦ fr z z) := by
        funext z
        have hF : HasFDerivAt (Function.uncurry f)
            (fderiv ℝ (Function.uncurry f) (z, z)) (z, z) :=
          (hf.differentiable (by simp) (z, z)).hasFDerivAt
        have hd := hF.comp (f := fun t : P ↦ (t, t)) z
          ((hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
        have hl := hF.comp (f := fun t : P ↦ (t, z)) z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z z)
        have hr := hF.comp (f := fun t : P ↦ (z, t)) z (hasFDerivAt_prodMk_right (𝕜 := ℝ) z z)
        change fderiv ℝ (fun t ↦ f t t) z u =
          fderiv ℝ (fun t ↦ f t z) z u + fderiv ℝ (f z) z u
        simp only [Function.comp_def, Function.uncurry_def] at hd hl hr
        rw [hd.fderiv, hl.fderiv, hr.fderiv]
        change fderiv ℝ (Function.uncurry f) (z, z) (u, u) =
          fderiv ℝ (Function.uncurry f) (z, z) (u, 0) +
            fderiv ℝ (Function.uncurry f) (z, z) (0, u)
        rw [← map_add]
        simp
      have hd : ContDiff ℝ ∞ (fderiv ℝ (fun z ↦ f z z)) :=
        (hf.comp (contDiff_id.prodMk contDiff_id)).fderiv_right (by simp)
      rw [iteratedFDeriv_succ_apply_right,
        ← iteratedFDeriv_clm_apply_const_apply hd (by simp), hdiag,
        iteratedFDeriv_add_apply (f := fun z ↦ fl z z) (g := fun z ↦ fr z z)
          ((hfl.comp (contDiff_id.prodMk contDiff_id)).contDiffAt.of_le (by simp))
          ((hfr.comp (contDiff_id.prodMk contDiff_id)).contDiffAt.of_le (by simp))]
      apply (norm_add_le _ _).trans
      have hl := (iteratedFDeriv ℝ i (fun z ↦ fl z z) x).le_opNorm (Fin.init v)
      have hr := (iteratedFDeriv ℝ i (fun z ↦ fr z z) x).le_opNorm (Fin.init v)
      apply (add_le_add (hl.trans (mul_le_mul_of_nonneg_right hleft (by positivity)))
        (hr.trans (mul_le_mul_of_nonneg_right hright (by positivity)))).trans_eq
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.init, u, pow_succ]
      ring
  -- Input derivatives preserve amplitude order before taking the diagonal.
  have input_amplitude {n r q : ℕ}
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
        (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x y u v : EuclideanSpace ℝ (Fin n)),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
      (u : EuclideanSpace ℝ (Fin n)) :
      IsAmplitude m (fun x y ξ ↦ fderiv ℝ (fun z ↦ a x z ξ) y u) := by
    let P := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    have hd : ContDiff ℝ ∞
        (fun z : (P × P) × P ↦ fderiv ℝ (fun w ↦ a z.1.1 w z.2) z.1.2) := by
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : (P × P) × P ↦ fun w : P ↦ a z.1.1 w z.2)) :=
        ha.1.comp ((contDiff_fst.fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
      exact h.fderiv contDiff_fst.snd (by simp)
    refine ⟨hd.clm_apply contDiff_const, ?_⟩
    intro K hK i j k
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK i (j + 1) k
    let L : (P →L[ℝ] P [×k]→L[ℝ] V) →L[ℝ] P [×k]→L[ℝ] V :=
      ContinuousLinearMap.apply ℝ (P [×k]→L[ℝ] V) u
    refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x y hxy ξ
    let g (z w : P) := iteratedFDeriv ℝ k (a z w) ξ
    have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
      (parametric (Function.uncurry a) ha.1 k).comp (contDiff_id.prodMk contDiff_const)
    have hdg : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (g z.1) z.2) := by
      have h : ContDiff ℝ ∞ (Function.uncurry (fun z : P × P ↦ fun w : P ↦ g z.1 w)) :=
        hg.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact h.fderiv contDiff_snd (by simp)
    have heq (z w : P) : iteratedFDeriv ℝ k
        (fun η ↦ fderiv ℝ (fun t ↦ a z t η) w u) ξ = fderiv ℝ (g z) w u := by
      apply iterated_comm comm
      exact ha.1.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    have hh : amplitudeDerivative (fun x y ξ ↦ fderiv ℝ (fun z ↦ a x z ξ) y u)
        i j k x y ξ = mixed (fun z w ↦ L (fderiv ℝ (g z) w)) i j x y := by
      unfold amplitudeDerivative mixed
      simp_rw [heq]
      rfl
    rw [hh]
    have h := mixed_map_bound L (fun z w ↦ fderiv ℝ (g z) w) hdg i j x y
    rw [mixed_shift] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hbound x y hxy ξ) (norm_nonneg _)).trans_eq
      (by ring))
  have input_iterated_amplitude {n r q : ℕ}
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
        (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x y u v : EuclideanSpace ℝ (Fin n)),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
      (j : ℕ) (v : Fin j → EuclideanSpace ℝ (Fin n)) :
      IsAmplitude m (fun x y ξ ↦ iteratedFDeriv ℝ j (fun z ↦ a x z ξ) y v) := by
    induction j with
    | zero => simpa only [iteratedFDeriv_zero_apply] using ha
    | succ j ih =>
      have hh := input_amplitude comm m
        (fun x y ξ ↦ iteratedFDeriv ℝ j (fun z ↦ a x z ξ) y (Fin.tail v))
        (ih (Fin.tail v)) (v 0)
      have heq : (fun x y ξ ↦ fderiv ℝ
          (fun w ↦ iteratedFDeriv ℝ j (fun z ↦ a x z ξ) w (Fin.tail v)) y (v 0)) =
          (fun x y ξ ↦ iteratedFDeriv ℝ (j + 1) (fun z ↦ a x z ξ) y v) := by
        funext x y ξ
        have hs : ContDiff ℝ ∞ (fun z ↦ a x z ξ) :=
          ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun z ↦ a x z ξ)) y :=
          hs.contDiffAt.differentiableAt_iteratedFDeriv (m := j)
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
        exact hd.iteratedFDeriv_succ_apply_left'.symm
      rwa [heq] at hh
  -- Frequency contractions of the resulting symbol have the exact expected order.
  have frequency_symbol {n r q : ℕ}
      (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
      (u : EuclideanSpace ℝ (Fin n)) :
      IsSymbol Set.univ (m - 1) (fun x ξ ↦ fderiv ℝ (a x) ξ u) := by
    let P := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    have hf : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    have hd : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (a z.1) z.2) := by
      have h : ContDiff ℝ ∞ (Function.uncurry (fun z : P × P ↦ fun η : P ↦ a z.1 η)) :=
        hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact h.fderiv contDiff_snd (by simp)
    refine ⟨?_, ?_⟩
    · rw [Set.univ_prod_univ]
      exact hd.contDiffOn.clm_apply contDiffOn_const
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i (j + 1)
    let L : (P →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V u
    refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x hx ξ
    have h := mixed_map_bound L (fun y η ↦ fderiv ℝ (a y) η) hd i j x ξ
    rw [mixed_shift] at h
    have hc := hbound x hx ξ
    have he : m - ((j + 1 : ℕ) : ℝ) = m - 1 - (j : ℝ) := by push_cast; ring
    rw [he] at hc
    exact h.trans ((mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans_eq (by ring))
  have frequency_iterated_symbol {n r q : ℕ}
      (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ m a)
      (j : ℕ) (v : Fin j → EuclideanSpace ℝ (Fin n)) :
      IsSymbol Set.univ (m - (j : ℝ)) (fun x ξ ↦ iteratedFDeriv ℝ j (a x) ξ v) := by
    have hf : ContDiff ℝ ∞ (Function.uncurry a) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
    induction j with
    | zero => simpa only [iteratedFDeriv_zero_apply, Nat.cast_zero, sub_zero] using ha
    | succ j ih =>
      have hh := frequency_symbol (m - (j : ℝ))
        (fun x ξ ↦ iteratedFDeriv ℝ j (a x) ξ (Fin.tail v)) (ih (Fin.tail v)) (v 0)
      have heq : (fun x ξ ↦ fderiv ℝ
          (fun η ↦ iteratedFDeriv ℝ j (a x) η (Fin.tail v)) ξ (v 0)) =
          (fun x ξ ↦ iteratedFDeriv ℝ (j + 1) (a x) ξ v) := by
        funext x ξ
        have hs : ContDiff ℝ ∞ (a x) := hf.comp (contDiff_const.prodMk contDiff_id)
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j (a x)) ξ :=
          hs.contDiffAt.differentiableAt_iteratedFDeriv (m := j)
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
        exact hd.iteratedFDeriv_succ_apply_left'.symm
      have he : m - (j : ℝ) - 1 = m - ((j + 1 : ℕ) : ℝ) := by push_cast; ring
      rwa [he, heq] at hh
  have diagonal_symbol {n r q : ℕ} (m : ℝ) (a : AmplitudeFunction n r q)
      (ha : IsAmplitude m a) : IsSymbol Set.univ m (fun x ξ ↦ a x x ξ) := by
    classical
    let P := EuclideanSpace ℝ (Fin n)
    refine ⟨?_, ?_⟩
    · rw [Set.univ_prod_univ]
      exact (ha.1.comp ((contDiff_fst.prodMk contDiff_fst).prodMk contDiff_snd)).contDiffOn
    intro K _ hK i k
    have hdiagonal : IsCompact ((fun x : P ↦ (x, x)) '' K) :=
      hK.image (continuous_id.prodMk continuous_id)
    choose C hC hbound using fun s t ↦ ha.2 _ hdiagonal s t k
    let D : ℝ := ∑ s ∈ Finset.range (i + 1), ∑ t ∈ Finset.range (i + 1), C s t
    have hD : 0 ≤ D :=
      Finset.sum_nonneg (fun s _ ↦ Finset.sum_nonneg (fun t _ ↦ hC s t))
    have hCD (s t : ℕ) (hs : s ≤ i) (ht : t ≤ i) : C s t ≤ D := by
      apply (Finset.single_le_sum (fun b _ ↦ hC s b)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))).trans
      exact Finset.single_le_sum (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ hC b c))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
    refine ⟨2 ^ i * D, mul_nonneg (by positivity) hD, ?_⟩
    intro x hx ξ
    let f (z w : P) := iteratedFDeriv ℝ k (a z w) ξ
    have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
      (parametric (Function.uncurry a) ha.1 k).comp (contDiff_id.prodMk contDiff_const)
    have h := diagonal_bound i f hf x (D * (1 + ‖ξ‖) ^ (m - (k : ℝ)))
      (mul_nonneg hD (Real.rpow_nonneg (by positivity) _))
    have hd : ‖iteratedFDeriv ℝ i (fun z ↦ f z z) x‖ ≤
        2 ^ i * (D * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
      apply h
      intro s hs t ht
      exact (hbound s t x x ⟨x, hx, rfl⟩ ξ).trans
        (mul_le_mul_of_nonneg_right (hCD s t hs ht) (Real.rpow_nonneg (by positivity) _))
    exact hd.trans_eq (by ring)
  -- Each original coefficient differentiates in the input variable before restriction.
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let c := (-Complex.I) ^ j / (j.factorial : ℂ)
  let dirs (α : Fin j → Fin n) (t : Fin j) : P := EuclideanSpace.single (α t) 1
  let terms (α : Fin j → Fin n) : SymbolFunction n r q := fun x ξ ↦
    iteratedFDeriv ℝ j
      (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ a x y η) x (dirs α)) ξ (dirs α)
  have ht (α : Fin j → Fin n) : IsSymbol Set.univ (m - (j : ℝ)) (terms α) := by
    have hb := input_iterated_amplitude mixed_fderiv_apply_comm m a ha j (dirs α)
    have hs := diagonal_symbol m _ hb
    exact frequency_iterated_symbol m _ hs j (dirs α)
  have hs : IsSymbol Set.univ (m - (j : ℝ)) (∑ α, terms α) :=
    (symbolSpace Set.univ isOpen_univ (m - (j : ℝ)) r q).sum_mem (fun α _ ↦ ht α)
  have heq : amplitudeExpansionTerm a j = c • ∑ α, terms α := by
    funext x ξ
    simp only [amplitudeExpansionTerm, c, Pi.smul_apply, Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro α _
    let L : (P [×j]→L[ℝ] V) →L[ℝ] V :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ P) V (dirs α)
    have hparam : ContDiff ℝ ∞
        (Function.uncurry (fun η : P ↦ fun y : P ↦ a x y η)) :=
      ha.1.comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)
    have hfull : ContDiff ℝ ∞ (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ a x y η) x) :=
      (parametric _ hparam j).comp (contDiff_id.prodMk contDiff_const)
    have h := L.iteratedFDeriv_comp_left hfull.contDiffAt (i := j) (x := ξ) (by simp)
    exact (congrArg (fun T : P [×j]→L[ℝ] V ↦ T (dirs α)) h).symm
  rw [heq]
  exact hs.smul isOpen_univ c

set_option maxHeartbeats 2000000 in

open scoped FourierTransform in
/-- Common integral estimates, retaining the derivative formula for Taylor remainders. -/
private theorem amplitude_reduction_estimates (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a)) :
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let R : V → V → V → H := fun x η ζ ↦
      ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)
    IsSymbol Set.univ m (amplitudeSymbol a) ∧
      ContDiff ℝ ∞ (fun z : (V × V) × V ↦ R z.1.1 z.1.2 z.2) ∧
      (∀ (L : Set V), IsCompact L → ∀ i k N : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
          ‖iteratedFDeriv ℝ i
            (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x‖ ≤
            C * (1 + ‖η‖) ^ (m - (k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))) ∧
      (∀ k x η ζ, iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η =
        Complex.exp (Complex.I * (inner ℝ x ζ : ℂ)) •
          𝓕 (fun y ↦ iteratedFDeriv ℝ k (a x y) (η + ζ))
            ((2 * Real.pi)⁻¹ • ζ)) ∧
      (∀ i k x η, symbolDerivative (amplitudeSymbol a) i k x η =
        ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x) := by
  /- Uniform Schwartz seminorm bounds for the compact y family give arbitrary
  Fourier decay. Peetre inequalities compare the shifted frequency η+ζ with η
  and absorb the extra ζ weight into that decay. The bounds remain of order m-k
  after k η derivatives, locally uniformly in x. Dominated derivative towers
  justify differentiation through both integrals and yield the symbol estimates. -/
  -- Mixed derivatives commute and control all derivatives on the full parameter product.
  have mixed_fderiv_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v := by
    let F := Function.uncurry f
    let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
    let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
    have hF : Differentiable ℝ F := hf.differentiable (by simp)
    have hDF : Differentiable ℝ (fderiv ℝ F) :=
      (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp)
    -- Each partial first derivative is the full derivative restricted to one factor.
    have hleft (a : X) (b : Y) :
        fderiv ℝ (fun t ↦ f t b) a = (fderiv ℝ F (a, b)).comp L := by
      exact ((hF (a, b)).hasFDerivAt.comp a
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)).fderiv
    have hright (a : X) (b : Y) :
        fderiv ℝ (f a) b = (fderiv ℝ F (a, b)).comp R :=
      ((hF (a, b)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right (𝕜 := ℝ) a b)).fderiv
    -- Differentiate those restrictions through fixed continuous linear composition maps.
    have hxy : fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fderiv ℝ F) (x, y) (0, v) (u, 0) := by
      simp_rw [hleft]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] X →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ X (X × Y) V).flip L
      have hd := (hDF (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp y hd
      exact congrArg (fun K : Y →L[ℝ] X →L[ℝ] V ↦ K v u) hc.fderiv
    have hyx : fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v =
        fderiv ℝ (fderiv ℝ F) (x, y) (u, 0) (0, v) := by
      simp_rw [hright]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] Y →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ Y (X × Y) V).flip R
      have hd := (hDF (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp x hd
      exact congrArg (fun K : X →L[ℝ] Y →L[ℝ] V ↦ K u v) hc.fderiv
    -- Symmetry applies on the full product, with the original two factor directions.
    rw [hxy, hyx]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (0, v) (u, 0)
  have mixed_fderiv_apply_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u := by
    have hl : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) := by
      have hh : ContDiff ℝ ∞ (Function.uncurry (fun z t ↦ f t z)) :=
        hf.comp (contDiff_snd.prodMk contDiff_fst)
      exact hh.fderiv contDiff_const (by simp)
    have hr : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (f t) y) :=
      hf.fderiv contDiff_const (by simp)
    rw [fderiv_clm_apply (hl.differentiable (by simp) y) (differentiableAt_const u),
      fderiv_clm_apply (hr.differentiable (by simp) x) (differentiableAt_const v)]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using mixed_fderiv_comm f hf x y u v
  have parametric {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  have iterated_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : X → Y → W) (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : X) (y : Y)
      (u : X) :
      iteratedFDeriv ℝ k (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y =
        fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) y) x u := by
    induction k generalizing y with
    | zero =>
      let J := (continuousMultilinearCurryFin0 ℝ Y V).symm.toContinuousLinearEquiv
      exact (congrArg (fun T : X →L[ℝ] Y [×0]→L[ℝ] V ↦ T u)
        (J.comp_fderiv (f := fun t ↦ f t y) (x := x))).symm
    | succ k ih =>
      ext v
      have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
        parametric f hf k
      rw [iteratedFDeriv_succ_apply_left]
      have hi : (fun z ↦ iteratedFDeriv ℝ k
          (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) =
          (fun z ↦ fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) z) x u) := by
        funext z
        exact ih z
      change ((fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k
        (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) y) (v 0)) (Fin.tail v) = _
      rw [hi]
      have hc := comm (fun t z ↦ iteratedFDeriv ℝ k (f t) z) hs x y u (v 0)
      rw [hc]
      have hd : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun t : X ↦ fun z : Y ↦ iteratedFDeriv ℝ k (f t) z)) := hs
        exact h.fderiv contDiff_const (by simp)
      have heq : (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y v) =
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0) (Fin.tail v)) := by
        funext t
        exact iteratedFDeriv_succ_apply_left v
      have hx : ContDiff ℝ ∞ (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y) :=
        (parametric f hf (k + 1)).comp (contDiff_id.prodMk contDiff_const)
      have ha : ContDiff ℝ ∞
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0)) :=
        hd.clm_apply contDiff_const
      rw [← fderiv_continuousMultilinear_apply_const_apply
        (hx.contDiffAt.differentiableAt (by simp)), heq,
        fderiv_continuousMultilinear_apply_const_apply (ha.contDiffAt.differentiableAt (by simp))]
  let mixed {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      P [×i]→L[ℝ] P [×j]→L[ℝ] V :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  have mixed_map_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (L : V →L[ℝ] W) (f : P → P → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ L (f y η)) i j x ξ‖ ≤ ‖L‖ * ‖mixed f i j x ξ‖ := by
    let T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ P) V W L
    have hT : ‖T‖ ≤ ‖L‖ := by
      apply T.opNorm_le_bound (norm_nonneg _)
      intro v
      exact L.norm_compContinuousMultilinearMap_le v
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ L (f y η)) ξ) =
        T ∘ (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) := by
      funext y
      exact L.iteratedFDeriv_comp_left
        ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt) (by simp)
    unfold mixed
    rw [heq]
    exact (T.norm_iteratedFDeriv_comp_left
      (((parametric f hf j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt)
        (by simp)).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have mixed_shift {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  -- Separated spatial derivatives control restriction to the same spatial diagonal.
  have mixed_left_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y u : P) :
      ‖mixed (fun a b ↦ fderiv ℝ (fun z ↦ f z b) a u) i j x y‖ ≤
        ‖u‖ * ‖mixed f (i + 1) j x y‖ := by
    have heq : (fun a ↦ iteratedFDeriv ℝ j
        (fun b ↦ fderiv ℝ (fun z ↦ f z b) a u) y) =
        (fun a ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j (f z) y) a u) := by
      funext a
      exact iterated_comm mixed_fderiv_apply_comm f hf j a y u
    unfold mixed
    rw [heq]
    have hs : ContDiff ℝ ∞ (fun a ↦ iteratedFDeriv ℝ j (f a) y) :=
      (parametric f hf j).comp (contDiff_id.prodMk contDiff_const)
    have hds : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y)) :=
      hs.fderiv_right (by simp)
    have h := norm_iteratedFDeriv_clm_apply_const hds.contDiffAt (x := x) (n := i)
      (c := u) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at h
    exact h
  have mixed_right_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y u : P) :
      ‖mixed (fun a b ↦ fderiv ℝ (f a) b u) i j x y‖ ≤
        ‖u‖ * ‖mixed f i (j + 1) x y‖ := by
    have hd : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (f z.1) z.2) := by
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : P × P ↦ fun b : P ↦ f z.1 b)) :=
        hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact h.fderiv contDiff_snd (by simp)
    let L : (P →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V u
    have hL : ‖L‖ ≤ ‖u‖ := by
      apply L.opNorm_le_bound (norm_nonneg _)
      intro T
      exact (T.le_opNorm u).trans_eq (mul_comm _ _)
    have h := mixed_map_bound L (fun a b ↦ fderiv ℝ (f a) b) hd i j x y
    rw [mixed_shift] at h
    exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have joint_bound {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      (i : ℕ) : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V), ContDiff ℝ ∞ (Function.uncurry f) →
      ∀ (x y : P) (A : ℝ), 0 ≤ A →
      (∀ a ≤ i, ∀ b ≤ i, ‖mixed f a b x y‖ ≤ A) →
      ‖iteratedFDeriv ℝ i (Function.uncurry f) (x, y)‖ ≤ 2 ^ i * A := by
    induction i with
    | zero =>
      intro V _ _ f hf x y A hA hbound
      simpa only [mixed, norm_iteratedFDeriv_zero, pow_zero, one_mul,
        Function.uncurry_apply_pair] using hbound 0 le_rfl 0 le_rfl
    | succ i ih =>
      intro V _ _ f hf x y A hA hbound
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro v
      let u := v (Fin.last i)
      let fl (a b : P) : V := fderiv ℝ (fun z ↦ f z b) a u.1
      let fr (a b : P) : V := fderiv ℝ (f a) b u.2
      have hfl : ContDiff ℝ ∞ (Function.uncurry fl) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun a : P ↦ f a z.2)) :=
          hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
        exact (h.fderiv contDiff_fst (by simp)).clm_apply contDiff_const
      have hfr : ContDiff ℝ ∞ (Function.uncurry fr) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun b : P ↦ f z.1 b)) :=
          hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact (h.fderiv contDiff_snd (by simp)).clm_apply contDiff_const
      have hleft : ‖iteratedFDeriv ℝ i (Function.uncurry fl) (x, y)‖ ≤
          2 ^ i * (‖u‖ * A) := by
        apply ih fl hfl x y (‖u‖ * A) (mul_nonneg (norm_nonneg _) hA)
        intro a ha b hb
        calc
          _ ≤ ‖u.1‖ * ‖mixed f (a + 1) b x y‖ := mixed_left_bound f hf a b x y u.1
          _ ≤ ‖u‖ * A := mul_le_mul (norm_fst_le u)
            (hbound (a + 1) (Nat.add_le_add_right ha 1) b (Nat.le.step hb))
            (norm_nonneg _) (norm_nonneg _)
      have hright : ‖iteratedFDeriv ℝ i (Function.uncurry fr) (x, y)‖ ≤
          2 ^ i * (‖u‖ * A) := by
        apply ih fr hfr x y (‖u‖ * A) (mul_nonneg (norm_nonneg _) hA)
        intro a ha b hb
        calc
          _ ≤ ‖u.2‖ * ‖mixed f a (b + 1) x y‖ := mixed_right_bound f hf a b x y u.2
          _ ≤ ‖u‖ * A := mul_le_mul (norm_snd_le u)
            (hbound a (Nat.le.step ha) (b + 1) (Nat.add_le_add_right hb 1))
            (norm_nonneg _) (norm_nonneg _)
      -- Split each full derivative into its two product directions.
      have hsplit : (fun z ↦ fderiv ℝ (Function.uncurry f) z u) =
          Function.uncurry fl + Function.uncurry fr := by
        funext z
        have hF := (hf.differentiable (by simp) z).hasFDerivAt
        have hl := hF.comp (f := fun t : P ↦ (t, z.2)) z.1
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
        have hr := hF.comp (f := fun t : P ↦ (z.1, t)) z.2
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
        change fderiv ℝ (Function.uncurry f) z u =
          fderiv ℝ (fun t ↦ f t z.2) z.1 u.1 + fderiv ℝ (f z.1) z.2 u.2
        simp only [Function.comp_def, Function.uncurry_def] at hl hr
        rw [hl.fderiv, hr.fderiv]
        change fderiv ℝ (Function.uncurry f) z u =
          fderiv ℝ (Function.uncurry f) z (u.1, 0) +
            fderiv ℝ (Function.uncurry f) z (0, u.2)
        rw [← map_add]
        simp
      have hd : ContDiff ℝ ∞ (fderiv ℝ (Function.uncurry f)) := hf.fderiv_right (by simp)
      rw [iteratedFDeriv_succ_apply_right,
        ← iteratedFDeriv_clm_apply_const_apply hd (by simp), hsplit,
        iteratedFDeriv_add_apply (f := Function.uncurry fl) (g := Function.uncurry fr)
          (hfl.contDiffAt.of_le (by simp)) (hfr.contDiffAt.of_le (by simp))]
      apply (norm_add_le _ _).trans
      have hl := (iteratedFDeriv ℝ i (Function.uncurry fl) (x, y)).le_opNorm (Fin.init v)
      have hr := (iteratedFDeriv ℝ i (Function.uncurry fr) (x, y)).le_opNorm (Fin.init v)
      apply (add_le_add (hl.trans (mul_le_mul_of_nonneg_right hleft (by positivity)))
        (hr.trans (mul_le_mul_of_nonneg_right hright (by positivity)))).trans_eq
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.init, u, pow_succ]
      ring
  -- A locally dominated derivative tower justifies smooth parameter integration at every order.
  have integrate {n : ℕ} {X W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
      [CompleteSpace W]
      (f : X → EuclideanSpace ℝ (Fin n) → W)
      (hf : ∀ ξ, ContDiff ℝ ∞ (fun x ↦ f x ξ))
      (hmeas : ∀ k x, AEStronglyMeasurable
        (fun ξ ↦ iteratedFDeriv ℝ k (fun x ↦ f x ξ) x))
      (hbound : ∀ (k : ℕ) (x₀ : X), ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
        Integrable b ∧ ∀ x ∈ Metric.closedBall x₀ 1, ∀ ξ,
          ‖iteratedFDeriv ℝ k (fun x ↦ f x ξ) x‖ ≤ b ξ) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f x ξ) ∧
        ∀ k x, iteratedFDeriv ℝ k (fun x ↦ ∫ ξ, f x ξ) x =
          ∫ ξ, iteratedFDeriv ℝ k (fun x ↦ f x ξ) x := by
    let V := EuclideanSpace ℝ (Fin n)
    let D (k : ℕ) (x : X) (ξ : V) := iteratedFDeriv ℝ k (fun x ↦ f x ξ) x
    have hi (k : ℕ) (x : X) : Integrable (D k x) := by
      obtain ⟨b, hb, hbk⟩ := hbound k x
      exact hb.mono' (hmeas k x)
          (Filter.Eventually.of_forall (hbk x (Metric.mem_closedBall_self (by norm_num))))
    have hd (k : ℕ) (x : X) :
        HasFDerivAt (fun x ↦ ∫ ξ, D k x ξ)
          ((∫ ξ, D (k + 1) x ξ).curryLeft) x := by
      obtain ⟨b, hb, hbk⟩ := hbound (k + 1) x
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) W
      have heq (z : X) (ξ : V) : fderiv ℝ (fun z ↦ D k z ξ) z = L (D (k + 1) z ξ) := by
        dsimp only [D]
        rw [iteratedFDeriv_succ_eq_comp_left]
        exact (L.apply_symm_apply _).symm
      have hdiff (ξ : V) (z : X) : HasFDerivAt (fun z ↦ D k z ξ) (L (D (k + 1) z ξ)) z := by
        rw [← heq]
        exact ((hf ξ).differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) z).hasFDerivAt
      have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := D k) (F' := fun z ξ ↦ L (D (k + 1) z ξ)) (s := Metric.ball x 1)
        (bound := b) (x₀ := x) (Metric.ball_mem_nhds x (by norm_num))
        (Filter.Eventually.of_forall (fun z ↦ (hi k z).1)) (hi k x)
        ((L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hi (k + 1) x)).1)
        (Filter.Eventually.of_forall (fun ξ z hz ↦ by
          simpa using hbk z (Metric.ball_subset_closedBall hz) ξ))
        hb (Filter.Eventually.of_forall (fun ξ z _ ↦ hdiff ξ z))
      have hL : (∫ ξ, L (D (k + 1) x ξ)) = L (∫ ξ, D (k + 1) x ξ) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi (k + 1) x)
      rw [hL] at h
      exact h
    have hTaylor : HasFTaylorSeriesUpTo (∞ : ℕ∞ω) (fun x ↦ ∫ ξ, f x ξ)
        (fun x k ↦ ∫ ξ, D k x ξ) := by
      constructor
      · intro x
        let L := continuousMultilinearCurryFin0 ℝ X W
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
    exact ⟨hTaylor.contDiff, fun k x ↦ (hTaylor.eq_iteratedFDeriv (by simp) x).symm⟩
  -- The inner spatial integral has fixed compact support; compact parameter balls give domination.
  have compact_integrate {n : ℕ} {X W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (f : X → EuclideanSpace ℝ (Fin n) → W)
      (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hzero : ∀ x y, y ∉ K → f x y = 0) :
      ContDiff ℝ ∞ (fun x ↦ ∫ y, f x y) ∧
        ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ y, f x y) x =
          ∫ y, iteratedFDeriv ℝ i (fun x ↦ f x y) x := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let D (i : ℕ) (x : X) (y : V) := iteratedFDeriv ℝ i (fun x ↦ f x y) x
    have hD (i : ℕ) : ContDiff ℝ ∞ (Function.uncurry (D i)) :=
      (parametric (fun y x ↦ f x y) (hf.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
        (contDiff_snd.prodMk contDiff_fst)
    have hDzero (i : ℕ) (x : X) (y : V) (hy : y ∉ K) : D i x y = 0 := by
      have hz : (fun x ↦ f x y) = 0 := funext (fun x ↦ hzero x y hy)
      simp [D, hz]
    apply integrate f
      (fun y ↦ hf.comp (contDiff_id.prodMk contDiff_const))
      (fun i x ↦ ((hD i).continuous.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    intro i x₀
    let L := Metric.closedBall x₀ 1
    have hL : IsCompact L := isCompact_closedBall x₀ 1
    obtain ⟨R, hR⟩ := ((hL.prod hK).image (hD i).continuous).isBounded.exists_norm_le
    refine ⟨K.indicator (fun _ ↦ max R 0),
      (integrable_indicator_iff hK.measurableSet).mpr
        (integrableOn_const (μ := volume) (C := max R 0) hK.measure_lt_top.ne), ?_⟩
    intro x hx y
    change ‖D i x y‖ ≤ _
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact (hR (D i x y) ⟨(x, y), ⟨hx, hy⟩, rfl⟩).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hy, hDzero i x y hy, norm_zero]
  -- Swapping the two derivative blocks preserves their multilinear operator norm.
  have mixed_norm {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y : P) :
      ‖iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y‖ =
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x‖ := by
    have apply_deriv {X Y W : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup W] [NormedSpace ℝ W]
        (k l : ℕ) (g : X → Y [×l]→L[ℝ] W) (hg : ContDiff ℝ ∞ g)
        (x : X) (v : Fin k → X) (w : Fin l → Y) :
        iteratedFDeriv ℝ k (fun x ↦ g x w) x v = iteratedFDeriv ℝ k g x v w := by
      let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin l ↦ Y) W w
      exact congrArg (fun T : X [×k]→L[ℝ] W ↦ T v)
        (L.iteratedFDeriv_comp_left hg.contDiffAt (by simp))
    have swap (i j : ℕ) : ∀ (f : P → P → V),
        ContDiff ℝ ∞ (Function.uncurry f) → ∀ (x y : P) (v : Fin i → P) (w : Fin j → P),
        iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y w v =
          iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x v w := by
      induction i with
      | zero =>
        intro f hf x y v w
        have hs : ContDiff ℝ ∞ (fun b ↦ iteratedFDeriv ℝ 0 (fun a ↦ f a b) x) :=
          ((parametric (fun y x ↦ f x y)
          (hf.comp (contDiff_snd.prodMk contDiff_fst)) 0).comp
            (contDiff_id.prodMk contDiff_const))
        rw [← apply_deriv j 0 _ hs y w v]
        simp only [iteratedFDeriv_zero_apply]
      | succ i ih =>
        intro f hf x y v w
        let u := v (Fin.last i)
        let g (a b : P) : V := fderiv ℝ (fun t ↦ f t b) a u
        have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
          have hh : ContDiff ℝ ∞
              (Function.uncurry (fun z : P × P ↦ fun a : P ↦ f a z.2)) :=
            hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
          exact (hh.fderiv contDiff_fst (by simp)).clm_apply contDiff_const
        have hs (k : ℕ) : ContDiff ℝ ∞
            (fun b ↦ iteratedFDeriv ℝ k (fun a ↦ f a b) x) :=
          (parametric (fun b a ↦ f a b) (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
            (contDiff_id.prodMk contDiff_const)
        have hgs : ContDiff ℝ ∞
            (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x) :=
          (parametric (fun b a ↦ g a b) (hg.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
            (contDiff_id.prodMk contDiff_const)
        have hsx : ContDiff ℝ ∞ (fun a ↦ iteratedFDeriv ℝ j (f a) y) :=
          (parametric f hf j).comp (contDiff_id.prodMk contDiff_const)
        have hvalue (b : P) :
            iteratedFDeriv ℝ (i + 1) (fun a ↦ f a b) x v =
              iteratedFDeriv ℝ i (fun a ↦ g a b) x (Fin.init v) := by
          rw [iteratedFDeriv_succ_apply_right]
          have hd : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ f a b)) :=
            (hf.comp (contDiff_id.prodMk contDiff_const)).fderiv_right (by simp)
          exact (iteratedFDeriv_clm_apply_const_apply hd (by simp)).symm
        calc
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ (i + 1) (fun a ↦ f a b) x v) y w :=
            (apply_deriv j (i + 1) _ (hs (i + 1)) y w v).symm
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x (Fin.init v)) y w := by
            simp_rw [hvalue]
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x) y w (Fin.init v) :=
            apply_deriv j i _ hgs y w (Fin.init v)
          _ = iteratedFDeriv ℝ i
              (fun a ↦ iteratedFDeriv ℝ j (g a) y) x (Fin.init v) w := ih g hg x y _ w
          _ = iteratedFDeriv ℝ i
              (fun a ↦ fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y) a u)
                x (Fin.init v) w := by
            have heq (a : P) : iteratedFDeriv ℝ j (g a) y =
                fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y) a u :=
              iterated_comm mixed_fderiv_apply_comm f hf j a y u
            simp_rw [heq]
          _ = iteratedFDeriv ℝ (i + 1)
              (fun a ↦ iteratedFDeriv ℝ j (f a) y) x v w := by
            rw [iteratedFDeriv_succ_apply_right]
            have hd : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y)) :=
              hsx.fderiv_right (by simp)
            exact congrArg (fun T : P [×j]→L[ℝ] V ↦ T w)
              (iteratedFDeriv_clm_apply_const_apply hd (by simp))
    -- A permutation of the two blocks of directions preserves the multilinear operator norm.
    let T := iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x
    let S := iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y
    apply le_antisymm
    · apply S.opNorm_le_bound (norm_nonneg T)
      intro w
      apply (S w).opNorm_le_bound (by positivity)
      intro v
      rw [show S w v = T v w from swap i j f hf x y v w]
      calc
        _ ≤ (‖T‖ * ∏ t, ‖v t‖) * ∏ t, ‖w t‖ :=
          (T v).le_of_opNorm_le (T.le_opNorm v) w
        _ = _ := by ring
    · apply T.opNorm_le_bound (norm_nonneg S)
      intro v
      apply (T v).opNorm_le_bound (by positivity)
      intro w
      rw [show T v w = S w v from (swap i j f hf x y v w).symm]
      calc
        _ ≤ (‖S‖ * ∏ t, ‖w t‖) * ∏ t, ‖v t‖ :=
          (S w).le_of_opNorm_le (S.le_opNorm w) v
        _ = _ := by ring
  -- Peetre estimates retain the external order while arbitrary Fourier decay absorbs the shift.
  have weighted_fourier {ι : Type} {n : ℕ} {W : Type}
      [NormedAddCommGroup W] [NormedSpace ℂ W]
      (f : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) → W)
      (hf : ∀ t η ζ, ContDiff ℝ ∞ (f t η ζ))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hsupp : ∀ t η ζ, tsupport (f t η ζ) ⊆ K) (s : ℝ)
      (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t η ζ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (f t η ζ) y‖ ≤ C * (1 + ‖η + ζ‖) ^ s)
      (c : ℝ) (hc : c ≠ 0) (N : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t η ζ,
        ‖𝓕 (f t η ζ) (c • ζ)‖ ≤
          C * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
    let V := EuclideanSpace ℝ (Fin n)
    -- Peetre's inequality uses the reverse triangle inequality for negative orders.
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
    -- Normalize only in the external parameter, preserving all integration-variable derivatives.
    let g (p : ι × V) (ζ y : V) : W := ((1 + ‖p.2‖) ^ s)⁻¹ • f p.1 p.2 ζ y
    have hg (p : ι × V) (ζ : V) : ContDiff ℝ ∞ (g p ζ) :=
      (hf p.1 p.2 ζ).const_smul _
    have hgsupp (p : ι × V) (ζ : V) : tsupport (g p ζ) ⊆ K :=
      (tsupport_smul_subset_right (fun _ ↦ ((1 + ‖p.2‖) ^ s)⁻¹) _).trans (hsupp p.1 p.2 ζ)
    have hgb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ζ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (g p ζ) y‖ ≤ C * (1 + ‖ζ‖) ^ ⌈|s|⌉₊ := by
      obtain ⟨C, hC, hbound⟩ := hb j
      refine ⟨C, hC, ?_⟩
      intro p ζ y hy
      have hp : 0 < (1 + ‖p.2‖) ^ s := Real.rpow_pos_of_pos (by positivity) s
      have hz : (1 + ‖ζ‖) ^ |s| ≤ (1 + ‖ζ‖) ^ ⌈|s|⌉₊ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le
          (by have := norm_nonneg ζ; linarith) (Nat.le_ceil |s|)
      change ‖iteratedFDeriv ℝ j (fun y ↦ _ • f p.1 p.2 ζ y) y‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply' ((hf p.1 p.2 ζ).of_le (by simp)).contDiffAt,
        norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
      calc
        _ ≤ ((1 + ‖p.2‖) ^ s)⁻¹ * (C * (1 + ‖p.2 + ζ‖) ^ s) := by
          gcongr
          exact hbound p.1 p.2 ζ y hy
        _ ≤ ((1 + ‖p.2‖) ^ s)⁻¹ *
            (C * ((1 + ‖p.2‖) ^ s * (1 + ‖ζ‖) ^ |s|)) := by
          gcongr
          exact hweight p.2 ζ
        _ = C * (1 + ‖ζ‖) ^ |s| := by field_simp
        _ ≤ C * (1 + ‖ζ‖) ^ ⌈|s|⌉₊ := mul_le_mul_of_nonneg_left hz hC
    obtain ⟨C, hC, hdecay⟩ :=
      fourier_diagonal_decay_of_compact_support g hg K hK hgsupp ⌈|s|⌉₊ hgb c hc N
    refine ⟨C, hC, ?_⟩
    intro t η ζ
    have hp : 0 < (1 + ‖η‖) ^ s := Real.rpow_pos_of_pos (by positivity) s
    have h := hdecay (t, η) ζ
    change ‖𝓕 (((1 + ‖η‖) ^ s)⁻¹ • f t η ζ) (c • ζ)‖ ≤ _ at h
    have hscale : 𝓕 (((1 + ‖η‖) ^ s)⁻¹ • f t η ζ) (c • ζ) =
        ((1 + ‖η‖) ^ s)⁻¹ • 𝓕 (f t η ζ) (c • ζ) := by
      simp only [Real.fourier_eq, Pi.smul_apply, smul_comm _ ((1 + ‖η‖) ^ s)⁻¹,
        integral_smul]
    rw [hscale, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)] at h
    have h' := mul_le_mul_of_nonneg_left h hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul,
      mul_comm ((1 + ‖η‖) ^ s) C] using h'
  -- Match the exact inner integral with the Fourier convention before differentiating it.
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let K : Set V := Prod.snd '' tsupport (Function.uncurry a)
  have hK : IsCompact K := hsupp.image continuous_snd
  have hazero (x y : V) (hy : y ∉ K) : a x y = 0 := by
    exact image_eq_zero_of_notMem_tsupport (f := Function.uncurry a)
      (fun h ↦ hy ⟨(x, y), h, rfl⟩)
  let D (k : ℕ) (x η ζ y : V) : V [×k]→L[ℝ] H := iteratedFDeriv ℝ k (a x y) (η + ζ)
  have hDs (k : ℕ) : ContDiff ℝ ∞
      (fun z : ((V × V) × V) × V ↦ D k z.1.1.1 z.1.1.2 z.1.2 z.2) := by
    exact (parametric (Function.uncurry a) ha.1 k).comp
      ((contDiff_fst.fst.fst.prodMk contDiff_snd).prodMk
        (contDiff_fst.fst.snd.add contDiff_fst.snd))
  have hDzero (k : ℕ) (x η ζ y : V) (hy : y ∉ K) : D k x η ζ y = 0 := by
    simp [D, hazero x y hy]
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let phase (x ζ : V) : ℂ := Complex.exp (Complex.I * (inner ℝ x ζ : ℂ))
  have hphase (ζ : V) : ContDiff ℝ ∞ (fun x ↦ phase x ζ) := by
    simpa [phase, Function.comp_def, real_inner_comm, mul_comm] using
      Complex.hasTemperateGrowth_exp_mul_I.1.comp (innerSL ℝ ζ).contDiff
  have hpNorm (x ζ : V) : ‖phase x ζ‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  let F (k : ℕ) (x η ζ : V) : V [×k]→L[ℝ] H := 𝓕 (D k x η ζ) (c • ζ)
  have hFint (k : ℕ) (x η ζ : V) : F k x η ζ =
      ∫ y, phase (-y) ζ • D k x η ζ y := by
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
  have hFs (k : ℕ) (ζ : V) : ContDiff ℝ ∞ (fun z : V × V ↦ F k z.1 z.2 ζ) := by
    have hker : ContDiff ℝ ∞ (Function.uncurry
        (fun z : V × V ↦ fun y : V ↦ phase (-y) ζ • D k z.1 z.2 ζ y)) :=
      ((hphase ζ).comp contDiff_snd.neg).smul
        ((hDs k).comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    have h := (compact_integrate _ hker K hK
      (fun z y hy ↦ by simp [hDzero k z.1 z.2 ζ y hy])).1
    have heq : (fun z : V × V ↦ F k z.1 z.2 ζ) =
        fun z ↦ ∫ y, phase (-y) ζ • D k z.1 z.2 ζ y :=
      funext (fun z ↦ hFint k z.1 z.2 ζ)
    rw [heq]
    exact h
  have hFderiv (i k : ℕ) (x η ζ : V) :
      iteratedFDeriv ℝ i (fun x ↦ F k x η ζ) x =
        𝓕 (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ D k x η ζ y) x) (c • ζ) := by
    have hD : ContDiff ℝ ∞ (Function.uncurry (fun x y : V ↦ D k x η ζ y)) :=
      (hDs k).comp (((contDiff_fst.prodMk contDiff_const).prodMk contDiff_const).prodMk
        contDiff_snd)
    have hker : ContDiff ℝ ∞ (Function.uncurry
        (fun x y : V ↦ phase (-y) ζ • D k x η ζ y)) :=
      ((hphase ζ).comp contDiff_snd.neg).smul hD
    have h := (compact_integrate _ hker K hK
      (fun x y hy ↦ by simp [hDzero k x η ζ y hy])).2 i x
    have heq : (fun x ↦ F k x η ζ) = fun x ↦ ∫ y, phase (-y) ζ • D k x η ζ y :=
      funext (fun x ↦ hFint k x η ζ)
    rw [heq, h, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    have hxy : ContDiff ℝ ∞ (fun x : V ↦ D k x η ζ y) :=
      hD.comp (contDiff_id.prodMk contDiff_const)
    rw [iteratedFDeriv_const_smul_apply' (hxy.contDiffAt.of_le (by simp))]
    congr 1
    simp only [phase, inner_neg_left, inner_smul_right]
    congr 1
    push_cast
    dsimp [c]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  let R (x η ζ : V) : H := ∫ y, phase (x - y) ζ • a x y (η + ζ)
  have hphaseJoint : ContDiff ℝ ∞ (Function.uncurry phase) := by
    simpa [phase, Function.comp_def, Function.uncurry_def, mul_comm] using!
      Complex.hasTemperateGrowth_exp_mul_I.1.comp (contDiff_inner (𝕜 := ℝ))
  have hRsJoint : ContDiff ℝ ∞ (fun z : (V × V) × V ↦ R z.1.1 z.1.2 z.2) := by
    have hker : ContDiff ℝ ∞ (Function.uncurry
        (fun z : (V × V) × V ↦ fun y : V ↦
          phase (z.1.1 - y) z.2 • a z.1.1 y (z.1.2 + z.2))) :=
      (hphaseJoint.comp
        ((contDiff_fst.fst.fst.sub contDiff_snd).prodMk contDiff_fst.snd)).smul
        (ha.1.comp ((contDiff_fst.fst.fst.prodMk contDiff_snd).prodMk
          (contDiff_fst.fst.snd.add contDiff_fst.snd)))
    exact (compact_integrate _ hker K hK
      (fun z y hy ↦ by simp [hazero z.1.1 y hy])).1
  have hRs (ζ : V) : ContDiff ℝ ∞ (fun z : V × V ↦ R z.1 z.2 ζ) := by
    have hmap : ContDiff ℝ ∞ (fun z : V × V ↦ (z, ζ)) :=
      contDiff_id.prodMk contDiff_const
    exact ContDiff.comp (f := fun z : V × V ↦ (z, ζ))
      (g := fun z : (V × V) × V ↦ R z.1.1 z.1.2 z.2) hRsJoint hmap
  have hReta (k : ℕ) (x η ζ : V) :
      iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η = phase x ζ • F k x η ζ := by
    have hker : ContDiff ℝ ∞ (Function.uncurry
        (fun η y : V ↦ phase (x - y) ζ • a x y (η + ζ))) :=
      ((hphase ζ).comp (contDiff_const.sub contDiff_snd)).smul
        (ha.1.comp ((contDiff_const.prodMk contDiff_snd).prodMk
          (contDiff_fst.add contDiff_const)))
    have h := (compact_integrate _ hker K hK
      (fun η y hy ↦ by simp [hazero x y hy])).2 k η
    change iteratedFDeriv ℝ k (fun η ↦ ∫ y, phase (x - y) ζ • a x y (η + ζ)) η = _
    rw [h, hFint, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    have hay : ContDiff ℝ ∞ (fun η : V ↦ a x y (η + ζ)) :=
      ha.1.comp ((contDiff_const.prodMk contDiff_const).prodMk
        (contDiff_id.add contDiff_const))
    rw [iteratedFDeriv_const_smul_apply' (hay.contDiffAt.of_le (by simp)),
      iteratedFDeriv_comp_add_right]
    dsimp only [D]
    rw [smul_smul]
    congr 1
    simp only [phase, ← Complex.exp_add, inner_sub_left, inner_neg_left]
    congr 1
    push_cast
    ring
  have hFbound (L : Set V) (hL : IsCompact L) (i k N : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
        ‖iteratedFDeriv ℝ i (fun x ↦ F k x η ζ) x‖ ≤
          C * (1 + ‖η‖) ^ (m - (k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
    let f (x : L) (η ζ y : V) := iteratedFDeriv ℝ i (fun x ↦ D k x η ζ y) x.val
    have hDj (η ζ : V) : ContDiff ℝ ∞ (Function.uncurry (fun x y : V ↦ D k x η ζ y)) :=
      (hDs k).comp (((contDiff_fst.prodMk contDiff_const).prodMk contDiff_const).prodMk
        contDiff_snd)
    have hder (η ζ : V) : ContDiff ℝ ∞
        (fun z : V × V ↦ iteratedFDeriv ℝ i (fun x ↦ D k x η ζ z.2) z.1) :=
      (parametric (fun y x : V ↦ D k x η ζ y)
        ((hDj η ζ).comp (contDiff_snd.prodMk contDiff_fst)) i).comp
          (contDiff_snd.prodMk contDiff_fst)
    have hf (x : L) (η ζ : V) : ContDiff ℝ ∞ (f x η ζ) :=
      (hder η ζ).comp (contDiff_const.prodMk contDiff_id)
    have hs (x : L) (η ζ : V) : tsupport (f x η ζ) ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      have hz : (fun x ↦ D k x η ζ y) = 0 :=
        funext (fun x ↦ hDzero k x η ζ y hyK)
      exact hy (by simp [f, hz])
    have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : L) η ζ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (f x η ζ) y‖ ≤ C * (1 + ‖η + ζ‖) ^ (m - (k : ℝ)) := by
      obtain ⟨C, hC, hb⟩ := ha.2 (L ×ˢ K) (hL.prod hK) i j k
      refine ⟨C, hC, ?_⟩
      intro x η ζ y hy
      dsimp only [f]
      rw [mixed_norm (fun x y ↦ D k x η ζ y) (hDj η ζ) i j x.val y]
      exact hb x.val y ⟨x.property, hy⟩ (η + ζ)
    obtain ⟨C, hC, hb⟩ := weighted_fourier f hf K hK hs (m - (k : ℝ)) hb c hc N
    refine ⟨C, hC, ?_⟩
    intro x hx η ζ
    rw [hFderiv]
    exact hb ⟨x, hx⟩ η ζ
  have phase_bounds {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (k : ℕ) :
      ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ i
          (fun x ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) x‖ ≤ C * (1 + ‖ξ‖) ^ d := by
    let V := EuclideanSpace ℝ (Fin n)
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨d, C, hC, hder⟩ := Complex.hasTemperateGrowth_exp_mul_I.norm_iteratedFDeriv_le_uniform k
    refine ⟨d + k, C * (1 + max R 0) ^ d, by positivity, ?_⟩
    intro i hi x hx ξ
    let L : V →L[ℝ] ℝ := innerSL ℝ ξ
    let e : ℝ → ℂ := fun t ↦ Complex.exp (t * Complex.I)
    have he : ContDiff ℝ ∞ e := Complex.hasTemperateGrowth_exp_mul_I.1
    have hfun : (fun x : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) = e ∘ L := by
      funext x
      simp [e, L, real_inner_comm, mul_comm]
    rw [hfun, L.iteratedFDeriv_comp_right he x (by simp)]
    have hbase : 1 + ‖L x‖ ≤ (1 + max R 0) * (1 + ‖ξ‖) := by
      have hnorm : ‖L x‖ ≤ ‖ξ‖ * max R 0 :=
        (norm_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_left
          ((hR x hx).trans (le_max_left _ _)) (norm_nonneg _))
      nlinarith [norm_nonneg ξ, le_max_right R 0]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i e (L x)‖ * ‖L‖ ^ i := by
        simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ i e (L x)) (fun _ ↦ L)
      _ ≤ (C * (1 + ‖L x‖) ^ d) * ‖L‖ ^ i := by
        gcongr
        exact hder i hi (L x)
      _ ≤ (C * ((1 + max R 0) * (1 + ‖ξ‖)) ^ d) * (1 + ‖ξ‖) ^ k := by
        gcongr
        calc
          ‖L‖ ^ i = ‖ξ‖ ^ i := by rw [innerSL_apply_norm]
          _ ≤ (1 + ‖ξ‖) ^ i := by gcongr; linarith [norm_nonneg ξ]
          _ ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hi
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hRbound (L : Set V) (hL : IsCompact L) (i k N : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x‖ ≤
          C * (1 + ‖η‖) ^ (m - (k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
    obtain ⟨d, A, hA, hp⟩ := phase_bounds L hL i
    choose C hC hb using fun l ↦ hFbound L hL (i - l) k (N + d)
    let B : ℝ := ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * A * C l
    have hB : 0 ≤ B := Finset.sum_nonneg
      (fun l _ ↦ mul_nonneg (mul_nonneg (by positivity) hA) (hC l))
    refine ⟨B, hB, ?_⟩
    intro x hx η ζ
    have heq : (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) =
        fun x ↦ phase x ζ • F k x η ζ := funext (fun x ↦ hReta k x η ζ)
    rw [heq]
    calc
      _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
          ‖iteratedFDeriv ℝ l (fun x ↦ phase x ζ) x‖ *
            ‖iteratedFDeriv ℝ (i - l) (fun x ↦ F k x η ζ) x‖ :=
        norm_iteratedFDeriv_smul_le (hphase ζ)
          ((hFs k ζ).comp (f := fun x : V ↦ (x, η))
            (contDiff_id.prodMk contDiff_const)) x (by simp)
      _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
          (A * (1 + ‖ζ‖) ^ d) *
            (C l * (1 + ‖η‖) ^ (m - (k : ℝ)) * (1 + ‖ζ‖) ^ (-((N + d : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum
        intro l hl
        have hCl := hC l
        gcongr
        · exact hp l (by simpa using hl) x hx ζ
        · exact hb l x hx η ζ
      _ = B * (1 + ‖η‖) ^ (m - (k : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
        dsimp [B]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        have hp : 0 < 1 + ‖ζ‖ := by positivity
        have he : (1 + ‖ζ‖) ^ d * (1 + ‖ζ‖) ^ (-((N + d : ℕ) : ℝ)) =
            (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hp]
          congr 1
          push_cast
          ring
        calc
          _ = ((i.choose l : ℝ) * A * C l) * (1 + ‖η‖) ^ (m - (k : ℝ)) *
              ((1 + ‖ζ‖) ^ d * (1 + ‖ζ‖) ^ (-((N + d : ℕ) : ℝ))) := by ring
          _ = _ := by rw [he]
  -- The compact spatial integral is smooth jointly in both parameters and frequency.
  have hRetaJoint (k : ℕ) : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
      iteratedFDeriv ℝ k (fun η ↦ R z.1.1 η z.2) z.1.2) := by
    have h : ContDiff ℝ ∞ (Function.uncurry
        (fun p : V × V ↦ fun η : V ↦ R p.1 η p.2)) :=
      hRsJoint.comp (f := fun z : (V × V) × V ↦ ((z.1.1, z.2), z.1.2))
        ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
    exact (parametric _ h k).comp
      (f := fun z : (V × V) × V ↦ ((z.1.1, z.2), z.1.2))
      ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
  have hRmixJoint (i k : ℕ) : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
      iteratedFDeriv ℝ i
        (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η z.2) z.1.2) z.1.1) := by
    have h : ContDiff ℝ ∞ (Function.uncurry
        (fun p : V × V ↦ fun x : V ↦
          iteratedFDeriv ℝ k (fun η ↦ R x η p.2) p.1)) :=
      (hRetaJoint k).comp (f := fun z : (V × V) × V ↦ ((z.2, z.1.1), z.1.2))
        ((contDiff_snd.prodMk contDiff_fst.fst).prodMk contDiff_fst.snd)
    exact (parametric _ h i).comp
      (f := fun z : (V × V) × V ↦ ((z.1.2, z.2), z.1.1))
      ((contDiff_fst.snd.prodMk contDiff_snd).prodMk contDiff_fst.fst)
  have weight_bound (L : Set V) (hL : IsCompact L) (s : ℝ) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ η ∈ L, (1 + ‖η‖) ^ s ≤ M := by
    have hbase : Continuous (fun η : V ↦ (1 : ℝ) + ‖η‖) :=
      continuous_const.add continuous_norm
    have hw : Continuous (fun η : V ↦ (1 + ‖η‖) ^ s) :=
      hbase.rpow_const (fun η ↦ Or.inl (by positivity))
    obtain ⟨M, hM⟩ := (hL.image hw).isBounded.exists_norm_le
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    intro η hη
    have h := hM ((1 + ‖η‖) ^ s) ⟨η, hη, rfl⟩
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h
    exact h.trans (le_max_left _ _)
  let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [V])
  have hdecay_nonneg (ζ : V) : 0 ≤ decay ζ := Real.rpow_nonneg (by positivity) _
  -- Exact frequency derivatives can now pass through the outer integral locally uniformly.
  have hEtaInt (x : V) : ContDiff ℝ ∞ (fun η ↦ ∫ ζ, R x η ζ) ∧
      ∀ k η, iteratedFDeriv ℝ k (fun η ↦ ∫ ζ, R x η ζ) η =
        ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η := by
    refine integrate (fun η ζ ↦ R x η ζ)
      (fun ζ ↦ (hRs ζ).comp (f := fun η : V ↦ (x, η))
        (contDiff_const.prodMk contDiff_id)) ?_ ?_
    · intro k η
      let : SecondCountableTopologyEither V (V [×k]→L[ℝ] H) :=
        secondCountableTopologyEither_of_left _ _
      exact ((hRetaJoint k).continuous.comp (f := fun ζ : V ↦ ((x, η), ζ))
        ((continuous_const.prodMk continuous_const).prodMk continuous_id)).aestronglyMeasurable
    intro k η₀
    obtain ⟨C, hC, hb⟩ := hRbound {x} isCompact_singleton 0 k (n + 1)
    obtain ⟨M, hM, hw⟩ := weight_bound (Metric.closedBall η₀ 1)
      (isCompact_closedBall η₀ 1) (m - (k : ℝ))
    refine ⟨fun ζ ↦ C * M * decay ζ, hdecay.const_mul _, ?_⟩
    intro η hη ζ
    have h := hb x (Set.mem_singleton x) η ζ
    simp only [norm_iteratedFDeriv_zero] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hw η hη) hC) (hdecay_nonneg ζ)
  -- Output derivatives retain the same order after frequency differentiation.
  have hXInt (k : ℕ) (η : V) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) ∧
      ∀ i x, iteratedFDeriv ℝ i
        (fun x ↦ ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x =
        ∫ ζ, iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x := by
    refine integrate (fun x ζ ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η)
      (fun ζ ↦ (hRetaJoint k).comp (f := fun x : V ↦ ((x, η), ζ))
        ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)) ?_ ?_
    · intro i x
      let : SecondCountableTopologyEither V (V [×i]→L[ℝ] V [×k]→L[ℝ] H) :=
        secondCountableTopologyEither_of_left _ _
      exact ((hRmixJoint i k).continuous.comp (f := fun ζ : V ↦ ((x, η), ζ))
        ((continuous_const.prodMk continuous_const).prodMk continuous_id)).aestronglyMeasurable
    intro i x₀
    obtain ⟨C, _, hb⟩ := hRbound (Metric.closedBall x₀ 1)
      (isCompact_closedBall x₀ 1) i k (n + 1)
    refine ⟨fun ζ ↦ C * (1 + ‖η‖) ^ (m - (k : ℝ)) * decay ζ,
      hdecay.const_mul _, ?_⟩
    exact fun x hx ζ ↦ hb x hx η ζ
  -- Mixed estimates give a locally uniform bound for every full parameter derivative.
  have hJointInt : ContDiff ℝ ∞ (fun z : V × V ↦ ∫ ζ, R z.1 z.2 ζ) := by
    apply (integrate (fun z : V × V ↦ fun ζ ↦ R z.1 z.2 ζ) hRs ?_ ?_).1
    · intro i z
      let : SecondCountableTopologyEither V ((V × V) [×i]→L[ℝ] H) :=
        secondCountableTopologyEither_of_left _ _
      have h : ContDiff ℝ ∞ (Function.uncurry
          (fun ζ : V ↦ fun z : V × V ↦ R z.1 z.2 ζ)) :=
        hRsJoint.comp (f := fun z : V × (V × V) ↦ (z.2, z.1))
          (contDiff_snd.prodMk contDiff_fst)
      exact ((parametric _ h i).continuous.comp (f := fun ζ : V ↦ (ζ, z))
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    intro i z₀
    let L := Metric.closedBall z₀ 1
    let Lx : Set V := Prod.fst '' L
    let Lη : Set V := Prod.snd '' L
    have hL : IsCompact L := isCompact_closedBall z₀ 1
    have hLx : IsCompact Lx := hL.image continuous_fst
    have hLη : IsCompact Lη := hL.image continuous_snd
    choose C hC hb using fun a b ↦ hRbound Lx hLx a b (n + 1)
    choose M hM hw using fun b : ℕ ↦ weight_bound Lη hLη (m - (b : ℝ))
    let B : ℝ := ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (i + 1), C a b * M b
    have hB : 0 ≤ B := Finset.sum_nonneg
      (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ mul_nonneg (hC a b) (hM b)))
    have hCM (a b : ℕ) (ha : a ≤ i) (hb : b ≤ i) : C a b * M b ≤ B := by
      have hrow : C a b * M b ≤ ∑ b ∈ Finset.range (i + 1), C a b * M b :=
        Finset.single_le_sum (fun b _ ↦ mul_nonneg (hC a b) (hM b))
          (show b ∈ Finset.range (i + 1) from Finset.mem_range.mpr (by omega))
      exact hrow.trans (Finset.single_le_sum
        (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ mul_nonneg (hC a b) (hM b)))
        (show a ∈ Finset.range (i + 1) from Finset.mem_range.mpr (by omega)))
    refine ⟨fun ζ ↦ (2 ^ i * B) * decay ζ, hdecay.const_mul _, ?_⟩
    intro z hz ζ
    have hx : z.1 ∈ Lx := ⟨z, hz, rfl⟩
    have hη : z.2 ∈ Lη := ⟨z, hz, rfl⟩
    have h := joint_bound i (fun x η ↦ R x η ζ) (hRs ζ) z.1 z.2
      (B * decay ζ) (mul_nonneg hB (hdecay_nonneg ζ))
    apply (h ?_).trans_eq (by ring)
    intro a ha b hb'
    change ‖iteratedFDeriv ℝ a (fun x ↦ iteratedFDeriv ℝ b (fun η ↦ R x η ζ) z.2) z.1‖ ≤ _
    calc
      _ ≤ C a b * (1 + ‖z.2‖) ^ (m - (b : ℝ)) * decay ζ := hb a b z.1 hx z.2 ζ
      _ ≤ (C a b * M b) * decay ζ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hw b z.2 hη) (hC a b)) (hdecay_nonneg ζ)
      _ ≤ B * decay ζ := mul_le_mul_of_nonneg_right (hCM a b ha hb') (hdecay_nonneg ζ)
  let c₀ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hsymbolEta (k : ℕ) (x η : V) :
      iteratedFDeriv ℝ k (amplitudeSymbol a x) η =
        c₀ • ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η := by
    change iteratedFDeriv ℝ k (fun η ↦ c₀ • ∫ ζ, R x η ζ) η = _
    rw [iteratedFDeriv_const_smul_apply' ((hEtaInt x).1.contDiffAt.of_le (by simp)),
      (hEtaInt x).2 k η]
  have hsymbolMixed (i k : ℕ) (x η : V) :
      symbolDerivative (amplitudeSymbol a) i k x η =
        c₀ • ∫ ζ, iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x := by
    have heq : (fun x ↦ iteratedFDeriv ℝ k (amplitudeSymbol a x) η) =
        fun x ↦ c₀ • ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η :=
      funext (fun x ↦ hsymbolEta k x η)
    change iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ k (amplitudeSymbol a x) η) x = _
    rw [heq, iteratedFDeriv_const_smul_apply' ((hXInt k η).1.contDiffAt.of_le (by simp)),
      (hXInt k η).2 i x]
  refine ⟨?_, hRsJoint, hRbound, hReta, hsymbolMixed⟩
  refine ⟨?_, ?_⟩
  · rw [Set.univ_prod_univ, contDiffOn_univ]
    exact hJointInt.const_smul c₀
  intro L _ hL i k
  obtain ⟨C, hC, hb⟩ := hRbound L hL i k (n + 1)
  have hI : 0 ≤ ∫ ζ, decay ζ := integral_nonneg hdecay_nonneg
  refine ⟨‖c₀‖ * C * (∫ ζ, decay ζ), by positivity, ?_⟩
  intro x hx η
  rw [hsymbolMixed, norm_smul]
  have hbound : ‖∫ ζ, iteratedFDeriv ℝ i
      (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x‖ ≤
      C * (1 + ‖η‖) ^ (m - (k : ℝ)) * (∫ ζ, decay ζ) := by
    calc
      _ ≤ ∫ ζ, C * (1 + ‖η‖) ^ (m - (k : ℝ)) * decay ζ :=
        norm_integral_le_of_norm_le (hdecay.const_mul _)
          (Filter.Eventually.of_forall (hb x hx η))
      _ = _ := integral_const_mul _ _
  exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)).trans_eq (by ring)

/-- SG 3.5: the exact reduced function satisfies the order-m symbol estimates. -/
theorem isSymbol_amplitudeSymbol (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a)) :
    IsSymbol Set.univ m (amplitudeSymbol a) := by
  -- The same integral estimates also retain the derivative formulas used below.
  exact (amplitude_reduction_estimates m a ha hsupp).1

/-- The reduced symbol retains compact support in the output position, uniformly in frequency. -/
theorem hasCompactSupport_amplitudeSymbol (a : AmplitudeFunction n r q)
    (hsupp : HasCompactSupport (Function.uncurry a)) :
    HasCompactSupport (amplitudeSymbol a) := by
  /- Outside the compact first projection of the spatial support, a(x,y,ξ) vanishes
  for every y and ξ. Both integrals then vanish for every η. The support of the
  reduced function, as a function of x valued in frequency functions, lies in that projection. -/
  have hK : IsCompact (Prod.fst '' tsupport (Function.uncurry a)) :=
    hsupp.image continuous_fst
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  by_contra hxK
  -- Outside this projection the original amplitude is identically zero before either integral.
  have hzero (y : EuclideanSpace ℝ (Fin n)) : Function.uncurry a (x, y) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (show (x, y) ∉ tsupport (Function.uncurry a) from
        fun h ↦ hxK ⟨(x, y), h, rfl⟩)
  change ∀ y, a x y = 0 at hzero
  apply hx
  funext η
  simp [amplitudeSymbol, hzero]

set_option maxHeartbeats 4000000 in

open scoped FourierTransform in
/-- SG 3.5: the reduced symbol quantizes to the original amplitude integral, exactly. -/
theorem quantize_amplitudeSymbol (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    quantize (amplitudeSymbol a) u = amplitudeApply a u := by
  /- Use Fourier inversion for u inside the y integral. The partial Fourier transform
  of a in y has arbitrary decay in ξ-η, while the Fourier transform of u decays in η.
  These bounds justify the frequency interchange after the y integration. Set ζ=ξ-η
  to obtain the displayed reduced symbol. Both sides have the same unnormalized forward
  Fourier convention and the inverse factor (2π)^(-n); no constants are suppressed. -/
  classical
  -- Normalize all three Fourier integrals with the same scalar change of variables.
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let H := E →L[ℂ] F
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  let phase (y ξ : V) := Complex.exp (Complex.I * (inner ℝ y (c • ξ) : ℂ))
  have hpNorm (y ξ : V) : ‖phase y ξ‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  let fu : 𝓢(V, E) := 𝓕 u
  have hnormalize (p : SymbolFunction n r q) (x : V) :
      quantize p u x = ∫ η, phase x η • p x (c • η) (fu η) := by
    let g (ζ : V) := Complex.exp (Complex.I * (inner ℝ x ζ : ℂ)) •
      p x ζ (fourierSG u ζ)
    have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure V) g c (hR := hc.le)
    calc
      _ = ∫ η : V, g (c • η) := by
        simpa only [V, finrank_euclideanSpace_fin, quantize, g, c] using hscale.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with η
        have hfu : fourierSG u (c • η) = fu η := by
          change 𝓕 u (c⁻¹ • (c • η)) = _
          rw [inv_smul_smul₀ hc.ne']
        simp only [g, hfu, phase]
  have hinv (y : V) : (∫ η, phase y η • fu η) = u y := by
    have h := congrArg (fun v : 𝓢(V, E) ↦ v y)
      (show (𝓕⁻ (𝓕 u : 𝓢(V, E)) : 𝓢(V, E)) = u from
        FourierTransform.fourierInv_fourier_eq u)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
    convert h using 1
    congr 1
    funext η
    simp only [phase, inner_smul_right, Complex.ofReal_mul, c]
    congr 2
    rw [real_inner_comm η y]
    ring
  funext x
  -- Compact input support makes each fixed-frequency amplitude a Schwartz function.
  let Ky : Set V := Prod.snd '' tsupport (Function.uncurry a)
  have hKy : IsCompact Ky := hsupp.image continuous_snd
  have haSmooth (ξ : V) : ContDiff ℝ ∞ (fun y ↦ a x y ξ) :=
    ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hsupport (ξ : V) : tsupport (fun y ↦ a x y ξ) ⊆ Ky := by
    apply closure_minimal ?_ hKy.isClosed
    intro y hy
    by_contra hyK
    have hz : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hyK ⟨(x, y), h, rfl⟩)
    exact hy (congrFun hz ξ)
  have hacomp (ξ : V) : HasCompactSupport (fun y ↦ a x y ξ) :=
    hKy.of_isClosed_subset (isClosed_tsupport _) (hsupport ξ)
  let A (ξ : V) : 𝓢(V, H) := (hacomp (c • ξ)).toSchwartzMap (haSmooth (c • ξ))
  let B (ξ η : V) : H := 𝓕 (A ξ) (ξ - η)
  let G (ξ η : V) : F := phase x ξ • B ξ η (fu η)
  have hB (ξ η : V) : B ξ η = ∫ y, phase (-y) (ξ - η) • a x y (c • ξ) := by
    dsimp only [B]
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    simp only [phase, inner_neg_left, inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg, c]
    congr 1
    ring
  have hBCont : Continuous (Function.uncurry B) := by
    change Continuous (fun z : V × V ↦ B z.1 z.2)
    simp_rw [hB]
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support hKy
      (f := fun z : V × V ↦ fun y ↦ phase (-y) (z.1 - z.2) • a x y (c • z.1))
    · have hp : Continuous (fun z : (V × V) × V ↦ phase (-z.2) (z.1.1 - z.1.2)) := by
        dsimp [phase]
        fun_prop
      exact (hp.smul (ha.1.continuous.comp
        ((continuous_const.prodMk continuous_snd).prodMk
          (continuous_fst.fst.const_smul c)))).continuousOn
    · intro z y _ hy
      have hz : a x y (c • z.1) = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y ↦ a x y (c • z.1))
        (fun h ↦ hy (hsupport (c • z.1) h))
      simp [hz]
  have hGCont : Continuous (Function.uncurry G) := by
    have hp : Continuous (fun z : V × V ↦ phase x z.1) := by dsimp [phase]; fun_prop
    exact hp.smul (hBCont.clm_apply (fu.continuous.comp continuous_snd))
  -- The spatial Fourier transform decays uniformly after a polynomial parameter weight.
  let d : ℕ := ⌈m⌉₊
  have hab (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Ky, ∀ ξ : V,
      ‖iteratedFDeriv ℝ j (fun y ↦ a x y ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ d := by
    obtain ⟨C, hC, hb⟩ := ha.2 ({x} ×ˢ Ky) (isCompact_singleton.prod hKy) 0 j 0
    refine ⟨C, hC, ?_⟩
    intro y hy ξ
    have h := hb x y ⟨Set.mem_singleton x, hy⟩ ξ
    have hzero : (fun w ↦ iteratedFDeriv ℝ 0 (a x w) ξ) =
        (continuousMultilinearCurryFin0 ℝ V H).symm ∘ (fun w ↦ a x w ξ) := by
      funext w
      exact congrFun iteratedFDeriv_zero_eq_comp ξ
    simp only [amplitudeDerivative, norm_iteratedFDeriv_zero, hzero,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.cast_zero, sub_zero] at h
    exact h.trans (by
      rw [← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)) hC)
  let weight (η : V) : ℝ := (1 + ‖η‖ ^ 2) ^ d
  have hwpos (η : V) : 0 < weight η := by dsimp [weight]; positivity
  let f (η ζ y : V) : H := (weight η)⁻¹ • a x y (c • (η + ζ))
  have hf (η ζ : V) : ContDiff ℝ ∞ (f η ζ) := (haSmooth _).const_smul _
  have hfs (η ζ : V) : tsupport (f η ζ) ⊆ Ky :=
    (tsupport_smul_subset_right _ _).trans (hsupport _)
  have hfb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η ζ y, y ∈ Ky →
      ‖iteratedFDeriv ℝ j (f η ζ) y‖ ≤ C * (1 + ‖ζ‖) ^ d := by
    obtain ⟨C, hC, hb⟩ := hab j
    refine ⟨C * ((1 + c) * 2) ^ d, by positivity, ?_⟩
    intro η ζ y hy
    have hbase : 1 + ‖c • (η + ζ)‖ ≤
        ((1 + c) * 2) * (1 + ‖η‖ ^ 2) * (1 + ‖ζ‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      have hadd := norm_add_le η ζ
      have hη : ‖η‖ ≤ 1 + ‖η‖ ^ 2 := by nlinarith [sq_nonneg (‖η‖ - 1)]
      nlinarith [norm_nonneg η, norm_nonneg ζ, mul_nonneg hc.le (norm_nonneg η),
        mul_nonneg hc.le (norm_nonneg ζ), mul_nonneg (sq_nonneg ‖η‖) (norm_nonneg ζ),
        mul_nonneg hc.le (mul_nonneg (sq_nonneg ‖η‖) (norm_nonneg ζ))]
    have hbound : ‖iteratedFDeriv ℝ j (fun y ↦ a x y (c • (η + ζ))) y‖ ≤
        (C * ((1 + c) * 2) ^ d * (1 + ‖ζ‖) ^ d) * weight η := by
      calc
        _ ≤ C * (1 + ‖c • (η + ζ)‖) ^ d := hb y hy _
        _ ≤ C * (((1 + c) * 2) * (1 + ‖η‖ ^ 2) * (1 + ‖ζ‖)) ^ d := by gcongr
        _ = _ := by simp only [mul_pow, weight]; ring
    dsimp only [f]
    rw [iteratedFDeriv_const_smul_apply' ((haSmooth _).contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hwpos η))]
    exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (hwpos η).le)).trans_eq
      (by field_simp [(hwpos η).ne'])
  obtain ⟨C, hC, hdecay⟩ := fourier_diagonal_decay_of_compact_support
    f hf Ky hKy hfs d hfb 1 one_ne_zero (n + 1)
  have hBbound (η ζ : V) : ‖B (η + ζ) η‖ ≤
      C * weight η * (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ)) := by
    have h := hdecay η ζ
    have heq : 𝓕 (f η ζ) ((1 : ℝ) • ζ) = (weight η)⁻¹ • B (η + ζ) η := by
      simp only [one_smul]
      dsimp only [f, B]
      rw [SchwartzMap.fourier_coe]
      simp only [add_sub_cancel_left]
      simp only [Real.fourier_eq', A]
      simp_rw [smul_comm _ ((weight η)⁻¹), integral_smul]
      rfl
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hwpos η))] at h
    have h' := mul_le_mul_of_nonneg_left h (hwpos η).le
    simpa [mul_assoc, (hwpos η).ne', mul_left_comm, mul_comm] using h'
  let wu : 𝓢(V, E) := SchwartzMap.smulLeftCLM E (fun η ↦ (weight η : ℂ)) fu
  have hwgrowth : (fun η ↦ (weight η : ℂ)).HasTemperateGrowth := by
    dsimp [weight]
    fun_prop
  have hwu (η : V) : ‖wu η‖ = weight η * ‖fu η‖ := by
    rw [show wu η = (weight η : ℂ) • fu η from
      SchwartzMap.smulLeftCLM_apply_apply hwgrowth _ _, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg (hwpos η).le]
  let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecayi : Integrable decay := integrable_one_add_norm (by simp [V])
  have hshift : Integrable (fun z : V × V ↦ G (z.1 + z.2) z.1)
      (volume.prod volume) := by
    apply ((wu.integrable.norm.mul_prod hdecayi).const_mul C).mono'
      (hGCont.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)).aestronglyMeasurable
    filter_upwards with z
    change ‖phase x (z.1 + z.2) • B (z.1 + z.2) z.1 (fu z.1)‖ ≤ _
    rw [norm_smul, hpNorm, one_mul]
    calc
      _ ≤ ‖B (z.1 + z.2) z.1‖ * ‖fu z.1‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * weight z.1 * decay z.2) * ‖fu z.1‖ := by
        gcongr
        exact hBbound z.1 z.2
      _ = C * (‖wu z.1‖ * decay z.2) := by rw [hwu]; ring
  -- The shear preserves product measure, so the frequency kernel is jointly integrable.
  have hGint : Integrable (Function.uncurry G) (volume.prod volume) := by
    change Integrable (fun z : V × V ↦ G z.1 z.2) (volume.prod volume)
    have hm := measurePreserving_prod_neg_add_swap (volume : Measure V) (volume : Measure V)
    have h := hm.integrable_comp_of_integrable hshift
    simpa only [Function.comp_def, Function.uncurry, add_neg_cancel_left] using h
  have hBInt (ξ η : V) : Integrable (fun y ↦ phase (-y) (ξ - η) • a x y (c • ξ)) := by
    apply (A ξ).integrable.norm.mono'
    · have hp : Continuous (fun y ↦ phase (-y) (ξ - η)) := by dsimp [phase]; fun_prop
      exact (hp.smul (haSmooth _).continuous).aestronglyMeasurable
    filter_upwards with y
    rw [norm_smul, hpNorm, one_mul]
    rfl
  -- Fourier inversion is used only inside a genuinely integrable spatial-frequency product.
  have hpoint (ξ : V) : (∫ η, G ξ η) =
      ∫ y, phase (x - y) ξ • a x y (c • ξ) (u y) := by
    let J (y η : V) : F := phase x ξ •
      (phase (-y) (ξ - η) • a x y (c • ξ)) (fu η)
    have hJ : Integrable (Function.uncurry J) (volume.prod volume) := by
      apply ((A ξ).integrable.norm.mul_prod fu.integrable.norm).mono'
      · have hp : Continuous (fun z : V × V ↦ phase (-z.1) (ξ - z.2)) := by
          dsimp [phase]
          fun_prop
        exact (continuous_const (y := phase x ξ) |>.smul
          ((hp.smul ((haSmooth (c • ξ)).continuous.comp continuous_fst)).clm_apply
            (fu.continuous.comp continuous_snd))).aestronglyMeasurable
      filter_upwards with z
      change ‖phase x ξ • (phase (-z.1) (ξ - z.2) • a x z.1 (c • ξ)) (fu z.2)‖ ≤ _
      rw [norm_smul, hpNorm, one_mul, smul_apply,
        norm_smul, hpNorm, one_mul]
      exact ContinuousLinearMap.le_opNorm _ _
    have hJG (η : V) : G ξ η = ∫ y, J y η := by
      dsimp only [G]
      rw [hB, ContinuousLinearMap.integral_apply (hBInt ξ η), ← integral_smul]
    simp_rw [hJG]
    rw [← integral_integral_swap hJ]
    apply integral_congr_ae
    filter_upwards with y
    have hfactor (η : V) : J y η =
        phase (x - y) ξ • a x y (c • ξ) (phase y η • fu η) := by
      dsimp only [J]
      simp only [smul_apply, map_smul, smul_smul]
      congr 1
      simp only [phase, ← Complex.exp_add, inner_sub_left, inner_neg_left,
        inner_sub_right, inner_smul_right]
      congr 1
      push_cast
      ring
    simp_rw [hfactor, integral_smul]
    congr 1
    have hi : Integrable (fun η ↦ phase y η • fu η) := by
      apply fu.integrable.norm.mono'
      · have hp : Continuous (fun η ↦ phase y η) := by dsimp [phase]; fun_prop
        exact (hp.smul fu.continuous).aestronglyMeasurable
      filter_upwards with η
      rw [norm_smul, hpNorm, one_mul]
    rw [(a x y (c • ξ)).integral_comp_comm hi, hinv]
  -- The frequency translation is performed after the compact spatial integral.
  have hsymbol (η : V) : amplitudeSymbol a x (c • η) =
      ∫ ζ, phase x ζ • B (η + ζ) η := by
    let g (ζ : V) : H := ∫ y,
      Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (c • η + ζ)
    have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure V) g c (hR := hc.le)
    calc
      _ = ∫ ζ : V, g (c • ζ) := by
        simpa only [V, finrank_euclideanSpace_fin, amplitudeSymbol, g, c] using hscale.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ζ
        rw [hB, ← integral_smul]
        apply integral_congr_ae
        filter_upwards with y
        simp only [add_sub_cancel_left, smul_add, smul_smul]
        congr 1
        simp only [phase, ← Complex.exp_add, inner_sub_left, inner_neg_left]
        congr 1
        push_cast
        ring
  have hsymbolInt (η : V) : Integrable (fun ζ ↦ phase x ζ • B (η + ζ) η) := by
    have hi := integrable_amplitudeSymbol_outer m a ha hsupp x (c • η)
    have his := hi.comp_smul hc.ne'
    convert his using 1
    funext ζ
    rw [hB, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [phase, add_sub_cancel_left, smul_add, smul_smul, ← Complex.exp_add,
      inner_sub_left, inner_neg_left]
    congr 1
    push_cast
    ring
  have hq (η : V) : phase x η • amplitudeSymbol a x (c • η) (fu η) =
      ∫ ξ, G ξ η := by
    rw [hsymbol, ContinuousLinearMap.integral_apply (hsymbolInt η), ← integral_smul]
    have heq : (fun ζ ↦ phase x η • (phase x ζ • B (η + ζ) η) (fu η)) =
        fun ζ ↦ G (η + ζ) η := by
      funext ζ
      dsimp only [G]
      rw [smul_apply, smul_smul]
      congr 1
      simp only [phase, smul_add, inner_add_right, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [heq]
    exact integral_add_left_eq_self (fun ξ : V ↦ G ξ η) η
  rw [hnormalize]
  simp_rw [hq]
  rw [← integral_integral_swap hGint]
  simp_rw [hpoint]
  let g (ξ : V) := ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y)
  have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure V) g c (hR := hc.le)
  simpa only [g, phase, V, finrank_euclideanSpace_fin, amplitudeApply, c] using hscale

set_option maxHeartbeats 8000000 in

open FourierTransform LineDeriv in
/-- SG (3.5): all finite Taylor remainders have the next symbol order. -/
theorem hasSymbolExpansion_amplitudeSymbol (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a)) :
    HasSymbolExpansion Set.univ (fun j ↦ m - (j : ℝ))
      (amplitudeSymbol a) (amplitudeExpansionTerm a) := by
  /- Fourier moments identify each actual Taylor coefficient. The integral Taylor
  remainder supplies the missing frequency order; arbitrary Fourier decay controls
  every mixed derivative. All exchange-of-derivative and integration calculations
  below remain local to this proof and retain the original oscillatory integral. -/
  classical
  -- Identify the Fourier transform of each iterated directional derivative.
  have fourier_iterated_lineDeriv {V H : Type}
      [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup H] [NormedSpace ℂ H]
      (j : ℕ) (f : 𝓢(V, H)) (v : Fin j → V) (ζ : V) :
      𝓕 (∂^{v} f) ζ = ((2 * Real.pi * Complex.I) ^ j) •
        ((∏ t, inner ℝ ζ (v t)) • 𝓕 f ζ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iteratedLineDerivOp_succ_left, SchwartzMap.fourier_lineDerivOp_eq]
      have hg : (fun x : V ↦ inner ℝ x (v 0)).HasTemperateGrowth := by fun_prop
      rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
      rw [ih, pow_succ, Fin.prod_univ_succ]
      rw [smul_comm (inner ℝ ζ (v 0)) ((2 * Real.pi * Complex.I) ^ j)]
      rw [smul_smul, smul_smul, mul_comm (2 * Real.pi * Complex.I)]
      rfl
  have integral_fourier_moment {V H : Type}
      [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
      (j : ℕ) (f : 𝓢(V, H)) (v : Fin j → V) (x : V) :
      (∫ ζ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ζ x : ℂ)) •
        ((∏ t, inner ℝ ζ (v t)) • 𝓕 f ζ)) =
          ((2 * Real.pi * Complex.I) ^ j)⁻¹ • iteratedFDeriv ℝ j f x v := by
    -- Invert the Fourier transform of the actual iterated directional derivative.
    have h := congrArg (fun g : 𝓢(V, H) ↦ g x)
      (show (𝓕⁻ (𝓕 (∂^{v} f) : 𝓢(V, H)) : 𝓢(V, H)) = ∂^{v} f from
        FourierTransform.fourierInv_fourier_eq _)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
    simp_rw [SchwartzMap.fourier_coe] at h
    have heq (ζ : V) : (𝓕 (∂^{v} f : 𝓢(V, H))) ζ =
        ((2 * Real.pi * Complex.I) ^ j) • ((∏ t, inner ℝ ζ (v t)) • 𝓕 f ζ) :=
      fourier_iterated_lineDeriv j f v ζ
    simp_rw [← SchwartzMap.fourier_coe, heq, smul_comm _ ((2 * Real.pi * Complex.I) ^ j)] at h
    rw [integral_smul] at h
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ^ j ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, ← h, inv_smul_smul₀ hc]
    apply integral_congr_ae
    filter_upwards with ζ
    congr 2
    push_cast
    ring
  -- Taylor's integral remainder will measure the loss of frequency order.
  have norm_taylor_remainder {V H : Type}
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
      (f : V → H) (hf : ContDiff ℝ ∞ f) (N : ℕ) (x y : V)
      (C : ℝ) (hC : 0 ≤ C)
      (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (N + 1) f (x + t • y)‖ ≤ C) :
      ‖f (x + y) - ∑ j ∈ Finset.range (N + 1),
        ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j f x (fun _ ↦ y)‖ ≤
          C * ‖y‖ ^ (N + 1) := by
    -- Integral Taylor remainder retains every derivative, while the interval has length one.
    rw [map_add_eq_sum_add_integral_iteratedFDeriv
      (fun t _ ↦ hf.contDiffAt.of_le (by simp)), add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ ((N.factorial : ℝ)⁻¹))]
    have hbound : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ N •
        iteratedFDeriv ℝ (N + 1) f (x + t • y) (fun _ ↦ y)‖ ≤
          C * ‖y‖ ^ (N + 1) := by
      suffices h : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ N •
          iteratedFDeriv ℝ (N + 1) f (x + t • y) (fun _ ↦ y)‖ ≤
            (C * ‖y‖ ^ (N + 1)) * |(1 : ℝ) - 0| by simpa using h
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨ht.1.le, ht.2⟩
      have hpow : 0 ≤ (1 - t) ^ N := pow_nonneg (by linarith [ht'.2]) N
      rw [norm_smul, Real.norm_of_nonneg hpow]
      have hp : (1 - t) ^ N ≤ 1 := pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
      calc
        _ ≤ (1 - t) ^ N * (C * ‖y‖ ^ (N + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hpow
          simpa using (iteratedFDeriv ℝ (N + 1) f (x + t • y)).le_of_opNorm_le
            (hb t ht') (fun _ ↦ y)
        _ ≤ C * ‖y‖ ^ (N + 1) := mul_le_of_le_one_left (by positivity) hp
    calc
      _ ≤ (N.factorial : ℝ)⁻¹ * (C * ‖y‖ ^ (N + 1)) := by gcongr
      _ ≤ C * ‖y‖ ^ (N + 1) := by
        apply mul_le_of_le_one_left (by positivity)
        exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.factorial_pos N))
  -- Commute mixed derivatives while keeping every multilinear direction explicit.
  have iteratedFDeriv_exchange {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → P → W) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y : P) (v : Fin i → P) (w : Fin j → P) :
      iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y w v =
        iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x v w := by
    have mixed_fderiv_comm {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
        (x : X) (y : Y) (u : X) (v : Y) :
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v := by
      let F := Function.uncurry f
      let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
      let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
      have hF : Differentiable ℝ F := hf.differentiable (by simp)
      have hDF : Differentiable ℝ (fderiv ℝ F) :=
        (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp)
      -- Each partial first derivative is the full derivative restricted to one factor.
      have hleft (a : X) (b : Y) :
          fderiv ℝ (fun t ↦ f t b) a = (fderiv ℝ F (a, b)).comp L := by
        exact ((hF (a, b)).hasFDerivAt.comp a
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)).fderiv
      have hright (a : X) (b : Y) :
          fderiv ℝ (f a) b = (fderiv ℝ F (a, b)).comp R :=
        ((hF (a, b)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right (𝕜 := ℝ) a b)).fderiv
      -- Differentiate those restrictions through fixed continuous linear composition maps.
      have hxy : fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
          fderiv ℝ (fderiv ℝ F) (x, y) (0, v) (u, 0) := by
        simp_rw [hleft]
        let C : ((X × Y) →L[ℝ] V) →L[ℝ] X →L[ℝ] V :=
          (ContinuousLinearMap.compL ℝ X (X × Y) V).flip L
        have hd := (hDF (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
        have hc := C.hasFDerivAt.comp y hd
        exact congrArg (fun K : Y →L[ℝ] X →L[ℝ] V ↦ K v u) hc.fderiv
      have hyx : fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v =
          fderiv ℝ (fderiv ℝ F) (x, y) (u, 0) (0, v) := by
        simp_rw [hright]
        let C : ((X × Y) →L[ℝ] V) →L[ℝ] Y →L[ℝ] V :=
          (ContinuousLinearMap.compL ℝ Y (X × Y) V).flip R
        have hd := (hDF (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
        have hc := C.hasFDerivAt.comp x hd
        exact congrArg (fun K : X →L[ℝ] Y →L[ℝ] V ↦ K u v) hc.fderiv
      -- Symmetry applies on the full product, with the original two factor directions.
      rw [hxy, hyx]
      exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (0, v) (u, 0)
    have mixed_fderiv_apply_comm {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : X → Y → V)
        (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y) :
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u := by
      have hl : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) := by
        have hh : ContDiff ℝ ∞ (Function.uncurry (fun z t ↦ f t z)) :=
          hf.comp (contDiff_snd.prodMk contDiff_fst)
        exact hh.fderiv contDiff_const (by simp)
      have hr : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (f t) y) :=
        hf.fderiv contDiff_const (by simp)
      rw [fderiv_clm_apply (hl.differentiable (by simp) y) (differentiableAt_const u),
        fderiv_clm_apply (hr.differentiable (by simp) x) (differentiableAt_const v)]
      simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply] using mixed_fderiv_comm f hf x y u v
    have parametric {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
        ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
      induction k with
      | zero =>
        exact hf.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
      | succ k ih =>
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
          ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
        have hd : ContDiff ℝ ∞
            (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
          h.fderiv contDiff_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
            _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
    have iterated_comm {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
          (f : X → Y → W) (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y),
          fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
            fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
        (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : X) (y : Y)
        (u : X) :
        iteratedFDeriv ℝ k (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y =
          fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) y) x u := by
      induction k generalizing y with
      | zero =>
        let J := (continuousMultilinearCurryFin0 ℝ Y V).symm.toContinuousLinearEquiv
        exact (congrArg (fun T : X →L[ℝ] Y [×0]→L[ℝ] V ↦ T u)
          (J.comp_fderiv (f := fun t ↦ f t y) (x := x))).symm
      | succ k ih =>
        ext v
        have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
          parametric f hf k
        rw [iteratedFDeriv_succ_apply_left]
        have hi : (fun z ↦ iteratedFDeriv ℝ k
            (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) =
            (fun z ↦ fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) z) x u) := by
          funext z
          exact ih z
        change ((fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k
          (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) y) (v 0)) (Fin.tail v) = _
        rw [hi]
        have hc := comm (fun t z ↦ iteratedFDeriv ℝ k (f t) z) hs x y u (v 0)
        rw [hc]
        have hd : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) := by
          have h : ContDiff ℝ ∞
              (Function.uncurry (fun t : X ↦ fun z : Y ↦ iteratedFDeriv ℝ k (f t) z)) := hs
          exact h.fderiv contDiff_const (by simp)
        have heq : (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y v) =
            (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0) (Fin.tail v)) := by
          funext t
          exact iteratedFDeriv_succ_apply_left v
        have hx : ContDiff ℝ ∞ (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y) :=
          (parametric f hf (k + 1)).comp (contDiff_id.prodMk contDiff_const)
        have ha : ContDiff ℝ ∞
            (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0)) :=
          hd.clm_apply contDiff_const
        rw [← fderiv_continuousMultilinear_apply_const_apply
          (hx.contDiffAt.differentiableAt (by simp)), heq,
          fderiv_continuousMultilinear_apply_const_apply (ha.contDiffAt.differentiableAt (by simp))]
    have apply_deriv {X Y W : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup W] [NormedSpace ℝ W]
        (k l : ℕ) (g : X → Y [×l]→L[ℝ] W) (hg : ContDiff ℝ ∞ g)
        (x : X) (v : Fin k → X) (w : Fin l → Y) :
        iteratedFDeriv ℝ k (fun x ↦ g x w) x v = iteratedFDeriv ℝ k g x v w := by
      let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin l ↦ Y) W w
      exact congrArg (fun T : X [×k]→L[ℝ] W ↦ T v)
        (L.iteratedFDeriv_comp_left hg.contDiffAt (by simp))
    have swap (i j : ℕ) : ∀ (f : P → P → W),
        ContDiff ℝ ∞ (Function.uncurry f) → ∀ (x y : P) (v : Fin i → P) (w : Fin j → P),
        iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y w v =
          iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x v w := by
      induction i with
      | zero =>
        intro f hf x y v w
        have hs : ContDiff ℝ ∞ (fun b ↦ iteratedFDeriv ℝ 0 (fun a ↦ f a b) x) :=
          ((parametric (fun y x ↦ f x y)
          (hf.comp (contDiff_snd.prodMk contDiff_fst)) 0).comp
            (contDiff_id.prodMk contDiff_const))
        rw [← apply_deriv j 0 _ hs y w v]
        simp only [iteratedFDeriv_zero_apply]
      | succ i ih =>
        intro f hf x y v w
        let u := v (Fin.last i)
        let g (a b : P) : W := fderiv ℝ (fun t ↦ f t b) a u
        have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
          have hh : ContDiff ℝ ∞
              (Function.uncurry (fun z : P × P ↦ fun a : P ↦ f a z.2)) :=
            hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
          exact (hh.fderiv contDiff_fst (by simp)).clm_apply contDiff_const
        have hs (k : ℕ) : ContDiff ℝ ∞
            (fun b ↦ iteratedFDeriv ℝ k (fun a ↦ f a b) x) :=
          (parametric (fun b a ↦ f a b) (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
            (contDiff_id.prodMk contDiff_const)
        have hgs : ContDiff ℝ ∞
            (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x) :=
          (parametric (fun b a ↦ g a b) (hg.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
            (contDiff_id.prodMk contDiff_const)
        have hsx : ContDiff ℝ ∞ (fun a ↦ iteratedFDeriv ℝ j (f a) y) :=
          (parametric f hf j).comp (contDiff_id.prodMk contDiff_const)
        have hvalue (b : P) :
            iteratedFDeriv ℝ (i + 1) (fun a ↦ f a b) x v =
              iteratedFDeriv ℝ i (fun a ↦ g a b) x (Fin.init v) := by
          rw [iteratedFDeriv_succ_apply_right]
          have hd : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ f a b)) :=
            (hf.comp (contDiff_id.prodMk contDiff_const)).fderiv_right (by simp)
          exact (iteratedFDeriv_clm_apply_const_apply hd (by simp)).symm
        calc
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ (i + 1) (fun a ↦ f a b) x v) y w :=
            (apply_deriv j (i + 1) _ (hs (i + 1)) y w v).symm
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x (Fin.init v)) y w := by
            simp_rw [hvalue]
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x) y w (Fin.init v) :=
            apply_deriv j i _ hgs y w (Fin.init v)
          _ = iteratedFDeriv ℝ i
              (fun a ↦ iteratedFDeriv ℝ j (g a) y) x (Fin.init v) w := ih g hg x y _ w
          _ = iteratedFDeriv ℝ i
              (fun a ↦ fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y) a u)
                x (Fin.init v) w := by
            have heq (a : P) : iteratedFDeriv ℝ j (g a) y =
                fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y) a u :=
              iterated_comm mixed_fderiv_apply_comm f hf j a y u
            simp_rw [heq]
          _ = iteratedFDeriv ℝ (i + 1)
              (fun a ↦ iteratedFDeriv ℝ j (f a) y) x v w := by
            rw [iteratedFDeriv_succ_apply_right]
            have hd : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y)) :=
              hsx.fderiv_right (by simp)
            exact congrArg (fun T : P [×j]→L[ℝ] W ↦ T w)
              (iteratedFDeriv_clm_apply_const_apply hd (by simp))
    exact swap i j f hf x y v w
  have norm_iteratedFDeriv_iteratedFDeriv {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (i j : ℕ) (f : P → W) (x : P) :
      ‖iteratedFDeriv ℝ i (iteratedFDeriv ℝ j f) x‖ =
        ‖iteratedFDeriv ℝ (i + j) f x‖ := by
    induction j generalizing i with
    | zero =>
      rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      simp
    | succ j ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
        norm_iteratedFDeriv_fderiv, ih]
      rw [show i + 1 + j = i + (j + 1) by omega]
  have iteratedFDeriv_apply_const {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (i j : ℕ) (g : P → P [×j]→L[ℝ] W) (hg : ContDiff ℝ ∞ g)
      (x : P) (v : Fin i → P) (w : Fin j → P) :
      iteratedFDeriv ℝ i (fun x ↦ g x w) x v = iteratedFDeriv ℝ i g x v w := by
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ P) W w
    exact congrArg (fun T : P [×i]→L[ℝ] W ↦ T v)
      (L.iteratedFDeriv_comp_left hg.contDiffAt (by simp))
  have iteratedFDeriv_comm_apply {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → W) (hf : ContDiff ℝ ∞ f) (i j : ℕ)
      (x : P) (v : Fin i → P) (w : Fin j → P) :
      iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j f x w) x v =
        iteratedFDeriv ℝ j (fun x ↦ iteratedFDeriv ℝ i f x v) x w := by
    rw [iteratedFDeriv_apply_const i j _ (hf.iteratedFDeriv_right (by simp)),
      iteratedFDeriv_apply_const j i _ (hf.iteratedFDeriv_right (by simp))]
    have h := iteratedFDeriv_exchange (fun a b : P ↦ f (a + b))
      (hf.comp (contDiff_fst.add contDiff_snd)) j i 0 x w v
    simpa only [iteratedFDeriv_comp_add_right, iteratedFDeriv_comp_add_left,
      zero_add] using h
  have contDiff_parametric_iteratedFDeriv {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  have iteratedFDeriv_exchange_apply {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → P → W) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y : P) (v : Fin i → P) (w : Fin j → P) :
      iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y w) x v =
        iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x v) y w := by
    have hx : ContDiff ℝ ∞ (fun x ↦ iteratedFDeriv ℝ j (f x) y) :=
      (contDiff_parametric_iteratedFDeriv f hf j).comp (contDiff_id.prodMk contDiff_const)
    have hy : ContDiff ℝ ∞ (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) :=
      (contDiff_parametric_iteratedFDeriv (fun y x ↦ f x y)
        (hf.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
          (contDiff_id.prodMk contDiff_const)
    rw [iteratedFDeriv_apply_const i j _ hx, iteratedFDeriv_apply_const j i _ hy]
    exact (iteratedFDeriv_exchange f hf i j x y v w).symm
  have norm_iteratedFDeriv_exchange {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → P → W) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y : P) :
      ‖iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y‖ =
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x‖ := by
    let T := iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x
    let S := iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y
    apply le_antisymm
    · apply S.opNorm_le_bound (norm_nonneg T)
      intro w
      apply (S w).opNorm_le_bound (by positivity)
      intro v
      rw [show S w v = T v w from iteratedFDeriv_exchange f hf i j x y v w]
      calc
        _ ≤ (‖T‖ * ∏ t, ‖v t‖) * ∏ t, ‖w t‖ :=
          (T v).le_of_opNorm_le (T.le_opNorm v) w
        _ = _ := by ring
    · apply T.opNorm_le_bound (norm_nonneg S)
      intro v
      apply (T v).opNorm_le_bound (by positivity)
      intro w
      rw [show T v w = S w v from (iteratedFDeriv_exchange f hf i j x y v w).symm]
      calc
        _ ≤ (‖S‖ * ∏ t, ‖w t‖) * ∏ t, ‖v t‖ :=
          (S w).le_of_opNorm_le (S.le_opNorm w) v
        _ = _ := by ring
  have iteratedFDeriv_taylor_remainder {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → W) (hf : ContDiff ℝ ∞ f) (N i : ℕ) (x ζ : P) :
      iteratedFDeriv ℝ i (fun η ↦ f η - ∑ j ∈ Finset.range N,
        (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f (η - ζ) (fun _ ↦ ζ)) x =
        iteratedFDeriv ℝ i f x - ∑ j ∈ Finset.range N,
          (j.factorial : ℝ)⁻¹ •
            iteratedFDeriv ℝ j (iteratedFDeriv ℝ i f) (x - ζ) (fun _ ↦ ζ) := by
    have hs (j : ℕ) : ContDiff ℝ ∞
        (fun η ↦ iteratedFDeriv ℝ j f (η - ζ) (fun _ ↦ ζ)) := by
      let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ P) W (fun _ ↦ ζ)
      exact L.contDiff.comp ((hf.iteratedFDeriv_right (by simp)).comp
        (contDiff_id.sub contDiff_const))
    rw [fun_iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp))
      ((ContDiff.sum (fun j _ ↦ (hs j).const_smul _)).contDiffAt.of_le (by simp)),
      iteratedFDeriv_fun_sum_apply
        (fun j _ ↦ ((hs j).const_smul _).contDiffAt.of_le (by simp))]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedFDeriv_const_smul_apply' ((hs j).contDiffAt.of_le (by simp))]
    congr 1
    ext v
    rw [show (fun η ↦ iteratedFDeriv ℝ j f (η - ζ) (fun _ ↦ ζ)) =
      (fun η ↦ (fun a ↦ iteratedFDeriv ℝ j f a (fun _ ↦ ζ)) (η - ζ)) by rfl,
      iteratedFDeriv_comp_sub (𝕜 := ℝ)
        (f := fun a ↦ iteratedFDeriv ℝ j f a (fun _ ↦ ζ)) i ζ x]
    rw [iteratedFDeriv_comm_apply f hf i j (x - ζ) v (fun _ ↦ ζ),
      iteratedFDeriv_apply_const j i _ (hf.iteratedFDeriv_right (by simp))]
  have iteratedFDeriv_taylor_remainder_parametric {P W : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → P → W) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (N i : ℕ) (x η ζ : P) :
      iteratedFDeriv ℝ i (fun x ↦ f x η - ∑ j ∈ Finset.range N,
        (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j (f x) (η - ζ) (fun _ ↦ ζ)) x =
        iteratedFDeriv ℝ i (fun x ↦ f x η) x - ∑ j ∈ Finset.range N,
          (j.factorial : ℝ)⁻¹ •
            iteratedFDeriv ℝ j (fun η ↦ iteratedFDeriv ℝ i (fun x ↦ f x η) x)
              (η - ζ) (fun _ ↦ ζ) := by
    have hs (j : ℕ) : ContDiff ℝ ∞
        (fun x ↦ iteratedFDeriv ℝ j (f x) (η - ζ) (fun _ ↦ ζ)) := by
      let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ P) W (fun _ ↦ ζ)
      exact L.contDiff.comp ((contDiff_parametric_iteratedFDeriv f hf j).comp
        (contDiff_id.prodMk contDiff_const))
    have hfx : ContDiff ℝ ∞ (fun x ↦ f x η) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    rw [fun_iteratedFDeriv_sub_apply (hfx.contDiffAt.of_le (by simp))
      ((ContDiff.sum (fun j _ ↦ (hs j).const_smul _)).contDiffAt.of_le (by simp)),
      iteratedFDeriv_fun_sum_apply
        (fun j _ ↦ ((hs j).const_smul _).contDiffAt.of_le (by simp))]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedFDeriv_const_smul_apply' ((hs j).contDiffAt.of_le (by simp))]
    congr 1
    ext v
    rw [iteratedFDeriv_exchange_apply f hf i j x (η - ζ) v (fun _ ↦ ζ)]
    have hsm : ContDiff ℝ ∞ (fun η ↦ iteratedFDeriv ℝ i (fun x ↦ f x η) x) :=
      (contDiff_parametric_iteratedFDeriv (fun η x ↦ f x η)
        (hf.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
          (contDiff_id.prodMk contDiff_const)
    exact iteratedFDeriv_apply_const j i _ hsm (η - ζ) (fun _ ↦ ζ) v
  have peetre_weight_shift {P : Type} [SeminormedAddCommGroup P]
      (s : ℝ) (x y : P) :
      (1 + ‖x + y‖) ^ s ≤ (1 + ‖x‖) ^ s * (1 + ‖y‖) ^ |s| := by
    have htriangle (x y : P) : 1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
      have hnorm := norm_add_le x y
      have hprod := mul_nonneg (norm_nonneg x) (norm_nonneg y)
      nlinarith
    by_cases hs : 0 ≤ s
    · rw [abs_of_nonneg hs, ← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (htriangle x y) hs
    · have hs' : s ≤ 0 := le_of_not_ge hs
      have hreverse : 1 + ‖x‖ ≤ (1 + ‖x + y‖) * (1 + ‖y‖) := by
        simpa only [add_neg_cancel_right, norm_neg] using htriangle (x + y) (-y)
      have h := Real.rpow_le_rpow_of_nonpos (by positivity) hreverse hs'
      rw [Real.mul_rpow (by positivity) (by positivity)] at h
      calc
        _ ≤ (1 + ‖x‖) ^ s / (1 + ‖y‖) ^ s :=
          (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) s)).mpr h
        _ = _ := by rw [abs_of_nonpos hs', Real.rpow_neg (by positivity), div_eq_mul_inv]
  -- Arbitrary Fourier decay absorbs the Taylor polynomial and the shifted weight.
  have taylor_remainder_symbol_bound {n : ℕ} {W : Type}
      [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) → W)
      (hR : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
          EuclideanSpace ℝ (Fin n) ↦ R z.1.1 z.1.2 z.2))
      (m : ℝ) (L : Set (EuclideanSpace ℝ (Fin n)))
      (hb : ∀ i k d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
        ‖iteratedFDeriv ℝ i
          (fun x ↦ iteratedFDeriv ℝ k (fun η ↦ R x η ζ) η) x‖ ≤
            C * (1 + ‖η‖) ^ (m - (k : ℝ)) * (1 + ‖ζ‖) ^ (-(d : ℝ)))
      (N i k d : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
        ‖iteratedFDeriv ℝ k (fun η ↦ iteratedFDeriv ℝ i
          (fun x ↦ R x η ζ - ∑ j ∈ Finset.range (N + 1),
            (j.factorial : ℝ)⁻¹ •
              iteratedFDeriv ℝ j (fun η ↦ R x η ζ) (η - ζ) (fun _ ↦ ζ)) x) η‖ ≤
            C * (1 + ‖η‖) ^ (m - (N + 1 : ℕ) - (k : ℝ)) *
              (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let s : ℝ := m - ((N + 1 + k : ℕ) : ℝ)
    let a : ℕ := ⌈|s|⌉₊
    obtain ⟨C, hC, hCb⟩ := hb i (N + 1 + k) (d + (N + 1) + a)
    refine ⟨C, hC, ?_⟩
    intro x hx η ζ
    have hRs : ContDiff ℝ ∞ (Function.uncurry (fun x η : V ↦ R x η ζ)) :=
      hR.comp (contDiff_id.prodMk contDiff_const)
    let g : V → V [×i]→L[ℝ] W := fun η ↦ iteratedFDeriv ℝ i (fun x ↦ R x η ζ) x
    have hgs : ContDiff ℝ ∞ g :=
      (contDiff_parametric_iteratedFDeriv (fun η x : V ↦ R x η ζ)
        (hRs.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
          (contDiff_id.prodMk contDiff_const)
    have heq : (fun η : V ↦ iteratedFDeriv ℝ i
        (fun x ↦ R x η ζ - ∑ j ∈ Finset.range (N + 1),
          (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j (fun η ↦ R x η ζ)
            (η - ζ) (fun _ ↦ ζ)) x) =
        fun η ↦ g η - ∑ j ∈ Finset.range (N + 1),
          (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j g (η - ζ) (fun _ ↦ ζ) := by
      funext η
      exact iteratedFDeriv_taylor_remainder_parametric _ hRs (N + 1) i x η ζ
    rw [heq, iteratedFDeriv_taylor_remainder g hgs (N + 1) k η ζ]
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (N + 1) (iteratedFDeriv ℝ k g) ((η - ζ) + t • ζ)‖ ≤
          C * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-((d + (N + 1) : ℕ) : ℝ)) := by
      intro t ht
      rw [norm_iteratedFDeriv_iteratedFDeriv]
      dsimp only [g]
      rw [norm_iteratedFDeriv_exchange _ hRs i (N + 1 + k)]
      have he : (η - ζ) + t • ζ = η + (t - 1) • ζ := by module
      have hnorm : ‖(t - 1) • ζ‖ ≤ ‖ζ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.2])]
        nlinarith [norm_nonneg ζ, ht.1, ht.2]
      have hweight : (1 + ‖(η - ζ) + t • ζ‖) ^ s ≤
          (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ a := by
        rw [he]
        apply (peetre_weight_shift s η ((t - 1) • ζ)).trans
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
        calc
          _ ≤ (1 + ‖ζ‖) ^ |s| :=
            Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg _)
          _ ≤ (1 + ‖ζ‖) ^ a := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le
              (by linarith [norm_nonneg ζ]) (Nat.le_ceil |s|)
      calc
        _ ≤ C * (1 + ‖(η - ζ) + t • ζ‖) ^ s *
            (1 + ‖ζ‖) ^ (-((d + (N + 1) + a : ℕ) : ℝ)) := hCb x hx _ ζ
        _ ≤ C * ((1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ a) *
            (1 + ‖ζ‖) ^ (-((d + (N + 1) + a : ℕ) : ℝ)) := by gcongr
        _ = _ := by
          have hp : 0 < 1 + ‖ζ‖ := by positivity
          have he : (1 + ‖ζ‖) ^ a *
              (1 + ‖ζ‖) ^ (-((d + (N + 1) + a : ℕ) : ℝ)) =
                (1 + ‖ζ‖) ^ (-((d + (N + 1) : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hp]
            congr 1
            push_cast
            ring
          calc
            _ = (C * (1 + ‖η‖) ^ s) * ((1 + ‖ζ‖) ^ a *
                (1 + ‖ζ‖) ^ (-((d + (N + 1) + a : ℕ) : ℝ))) := by ring
            _ = _ := by rw [he]
    have ht := norm_taylor_remainder (iteratedFDeriv ℝ k g)
      (hgs.iteratedFDeriv_right (by simp)) N (η - ζ) ζ
      (C * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-((d + (N + 1) : ℕ) : ℝ)))
      (by positivity) hbound
    simp only [sub_add_cancel] at ht
    apply ht.trans
    calc
      _ ≤ C * (1 + ‖η‖) ^ s * (1 + ‖ζ‖) ^ (-((d + (N + 1) : ℕ) : ℝ)) *
          (1 + ‖ζ‖) ^ (N + 1) := by gcongr; linarith [norm_nonneg ζ]
      _ = _ := by
        have hp : 0 < 1 + ‖ζ‖ := by positivity
        rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hp]
        have hs : s = m - (N + 1 : ℕ) - (k : ℝ) := by dsimp [s]; push_cast; ring
        rw [hs]
        congr 2
        push_cast
        ring
  -- Resolve directional moments in the original Euclidean basis and normalization.
  have multilinear_diagonal_eq_sum {n j : ℕ} {W : Type}
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (T : (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] W)
      (ζ : EuclideanSpace ℝ (Fin n)) :
      T (fun _ ↦ ζ) = ∑ α : Fin j → Fin n,
        (∏ t, inner ℝ ζ (EuclideanSpace.single (α t) 1)) •
          T (fun t ↦ EuclideanSpace.single (α t) 1) := by
    classical
    have hsum : ζ = ∑ l : Fin n, inner ℝ ζ (EuclideanSpace.single l 1) •
        EuclideanSpace.single l 1 := by
      ext l
      simp [EuclideanSpace.inner_single_right, Pi.single_apply]
    calc
      _ = T (fun _ ↦ ∑ l : Fin n, inner ℝ ζ (EuclideanSpace.single l 1) •
          EuclideanSpace.single l 1) := by rw [← hsum]
      _ = ∑ α : Fin j → Fin n,
          T (fun t ↦ inner ℝ ζ (EuclideanSpace.single (α t) 1) •
            EuclideanSpace.single (α t) 1) :=
        T.toMultilinearMap.map_sum (fun (_ : Fin j) l ↦
          inner ℝ ζ (EuclideanSpace.single l 1) • EuclideanSpace.single l 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro α _
        exact T.map_smul_univ _ _
  have integral_fourier_multilinear_moment {n j : ℕ} {W : Type}
      [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
      (f : 𝓢(EuclideanSpace ℝ (Fin n),
        (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] W))
      (x : EuclideanSpace ℝ (Fin n)) :
      (∫ ζ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ζ x : ℂ)) •
        (𝓕 f ζ) (fun _ ↦ ζ)) =
          ((2 * Real.pi * Complex.I) ^ j)⁻¹ • ∑ α : Fin j → Fin n,
            iteratedFDeriv ℝ j
              (fun y ↦ f y (fun t ↦ EuclideanSpace.single (α t) 1)) x
                (fun t ↦ EuclideanSpace.single (α t) 1) := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let dirs (α : Fin j → Fin n) : Fin j → V :=
      fun t ↦ EuclideanSpace.single (α t) 1
    let F (α : Fin j → Fin n) : 𝓢(V, W) :=
      f.postcompCLM (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ V) W (dirs α))
    have hF (α : Fin j → Fin n) (y : V) : F α y = f y (dirs α) := rfl
    have hFourier (α : Fin j → Fin n) (ζ : V) :
        (𝓕 f ζ) (dirs α) = 𝓕 (F α) ζ := by
      rw [SchwartzMap.fourier_coe, Real.fourier_continuousMultilinearMap_apply f.integrable,
        SchwartzMap.fourier_coe]
      rfl
    let c : ℂ := 2 * Real.pi * Complex.I
    have hc : c ^ j ≠ 0 := pow_ne_zero _
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
    let phase (ζ : V) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ζ x : ℂ))
    have hpnorm (ζ : V) : ‖phase ζ‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hi (α : Fin j → Fin n) : Integrable (fun ζ ↦
        phase ζ • ((∏ t, inner ℝ ζ (dirs α t)) • 𝓕 (F α) ζ)) := by
      have heq (ζ : V) : ((∏ t, inner ℝ ζ (dirs α t)) • 𝓕 (F α) ζ) =
          (c ^ j)⁻¹ • 𝓕 (∂^{dirs α} (F α)) ζ := by
        rw [fourier_iterated_lineDeriv j (F α) (dirs α) ζ]
        exact (inv_smul_smul₀ hc _).symm
      simp_rw [heq]
      have hint : Integrable (fun ζ ↦ (c ^ j)⁻¹ • 𝓕 (∂^{dirs α} (F α)) ζ) :=
        (𝓕 (∂^{dirs α} (F α)) : 𝓢(V, W)).integrable.smul _
      apply hint.norm.mono'
      · have hp : Continuous phase := by dsimp [phase]; fun_prop
        exact (hp.smul ((SchwartzMap.continuous _).const_smul _)).aestronglyMeasurable
      filter_upwards with ζ
      rw [norm_smul, hpnorm, one_mul]
    have hpoint (ζ : V) : phase ζ • (𝓕 f ζ) (fun _ ↦ ζ) =
        ∑ α : Fin j → Fin n, phase ζ • ((∏ t, inner ℝ ζ (dirs α t)) • 𝓕 (F α) ζ) := by
      rw [multilinear_diagonal_eq_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro α _
      rw [hFourier]
    change (∫ ζ, phase ζ • (𝓕 f ζ) (fun _ ↦ ζ)) = _
    simp_rw [hpoint]
    rw [integral_finsetSum _ (fun α _ ↦ hi α), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    exact integral_fourier_moment j (F α) (dirs α) x
  have integral_amplitude_taylorTerm {n r q : ℕ} (m : ℝ)
      (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
      (hsupp : HasCompactSupport (Function.uncurry a)) (j : ℕ)
      (x η : EuclideanSpace ℝ (Fin n)) :
      let R := fun x η ζ : EuclideanSpace ℝ (Fin n) ↦
        ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)
      ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, (j.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ j (fun η ↦ R x η ζ) (η - ζ) (fun _ ↦ ζ) =
          amplitudeExpansionTerm a j x η := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let W := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let R := fun x η ζ : V ↦
      ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)
    let Ky : Set V := Prod.snd '' tsupport (Function.uncurry a)
    have hKy : IsCompact Ky := hsupp.image continuous_snd
    have ha' : ContDiff ℝ ∞ (Function.uncurry (fun y ξ : V ↦ a x y ξ)) :=
      ha.1.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    let f : V → V [×j]→L[ℝ] W := fun y ↦ iteratedFDeriv ℝ j (a x y) η
    have hfs : ContDiff ℝ ∞ f :=
      (contDiff_parametric_iteratedFDeriv (fun y ξ : V ↦ a x y ξ) ha' j).comp
        (contDiff_id.prodMk contDiff_const)
    have hfc : HasCompactSupport f := by
      apply hKy.of_isClosed_subset (isClosed_tsupport f)
      apply closure_minimal ?_ hKy.isClosed
      intro y hy
      by_contra hyK
      have hz : a x y = 0 := image_eq_zero_of_notMem_tsupport (f := Function.uncurry a)
        (fun h ↦ hyK ⟨(x, y), h, rfl⟩)
      exact hy (by simp [f, hz])
    let F : 𝓢(V, V [×j]→L[ℝ] W) := hfc.toSchwartzMap hfs
    have hReta (ζ : V) : iteratedFDeriv ℝ j (fun η ↦ R x η ζ) (η - ζ) =
        Complex.exp (Complex.I * (inner ℝ x ζ : ℂ)) •
          (𝓕 F) ((2 * Real.pi)⁻¹ • ζ) := by
      have h := (amplitude_reduction_estimates m a ha hsupp).2.2.2.1 j x (η - ζ) ζ
      have hFco : (F : V → V [×j]→L[ℝ] W) = f := rfl
      rw [SchwartzMap.fourier_coe, hFco]
      simpa only [R, f, sub_add_cancel] using h
    change ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, (j.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ j (fun η ↦ R x η ζ) (η - ζ) (fun _ ↦ ζ) = _
    simp_rw [hReta, smul_apply]
    let d : ℝ := 2 * Real.pi
    have hd : 0 < d := mul_pos (by norm_num) Real.pi_pos
    let G (ζ : V) : W := (j.factorial : ℝ)⁻¹ •
      (Complex.exp (Complex.I * (inner ℝ x ζ : ℂ)) • (𝓕 F) (d⁻¹ • ζ) (fun _ ↦ ζ))
    have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure V) G d (hR := hd.le)
    have hscaled (ζ : V) : G (d • ζ) = (j.factorial : ℝ)⁻¹ • (d ^ j •
        (Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ζ x : ℂ)) •
          (𝓕 F ζ) (fun _ ↦ ζ))) := by
      dsimp only [G]
      rw [inv_smul_smul₀ hd.ne']
      rw [(𝓕 F ζ).map_smul_univ (fun _ ↦ d) (fun _ ↦ ζ)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [smul_comm _ (d ^ j)]
      congr 3
      rw [inner_smul_right, real_inner_comm x ζ]
      dsimp [d]
      push_cast
      ring
    have hnormalize : ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, G ζ = ∫ ζ, G (d • ζ) := by
      simpa only [V, finrank_euclideanSpace_fin, d] using hscale.symm
    change ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, G ζ = _
    rw [hnormalize]
    simp_rw [hscaled]
    rw [integral_smul, integral_smul, integral_fourier_multilinear_moment F x]
    let dirs (α : Fin j → Fin n) : Fin j → V :=
      fun t ↦ EuclideanSpace.single (α t) 1
    have hcoeff (w : W) : (j.factorial : ℝ)⁻¹ •
        (d ^ j • (((2 * Real.pi * Complex.I) ^ j)⁻¹ • w)) =
          ((-Complex.I) ^ j / (j.factorial : ℂ)) • w := by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      congr 1
      have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      dsimp [d]
      push_cast
      simp only [mul_pow, mul_inv_rev]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
      ring_nf
      rw [show j * 2 = 2 * j by omega, pow_mul, Complex.I_sq, mul_assoc,
        ← mul_pow]
      simp
    rw [hcoeff]
    congr 1
    apply Finset.sum_congr rfl
    intro α _
    change iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ j (a x y) η (dirs α)) x (dirs α) =
      iteratedFDeriv ℝ j (fun ξ ↦ iteratedFDeriv ℝ j (fun y ↦ a x y ξ) x) η (dirs α) (dirs α)
    rw [iteratedFDeriv_exchange_apply (fun y ξ : V ↦ a x y ξ) ha' j j x η
      (dirs α) (dirs α)]
    have hs : ContDiff ℝ ∞ (fun ξ ↦ iteratedFDeriv ℝ j (fun y ↦ a x y ξ) x) :=
      (contDiff_parametric_iteratedFDeriv (fun ξ y : V ↦ a x y ξ)
        (ha'.comp (contDiff_snd.prodMk contDiff_fst)) j).comp
          (contDiff_id.prodMk contDiff_const)
    exact iteratedFDeriv_apply_const j j _ hs η (dirs α) (dirs α)
  -- Dominated derivative towers justify differentiation of the same Bochner integral.
  have smooth_integral_of_bounds {n : ℕ} {X W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
      [CompleteSpace W]
      (f : X → EuclideanSpace ℝ (Fin n) → W)
      (hf : ∀ ξ, ContDiff ℝ ∞ (fun x ↦ f x ξ))
      (hmeas : ∀ k x, AEStronglyMeasurable
        (fun ξ ↦ iteratedFDeriv ℝ k (fun x ↦ f x ξ) x))
      (hbound : ∀ (k : ℕ) (x₀ : X), ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
        Integrable b ∧ ∀ x ∈ Metric.closedBall x₀ 1, ∀ ξ,
          ‖iteratedFDeriv ℝ k (fun x ↦ f x ξ) x‖ ≤ b ξ) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f x ξ) ∧
        ∀ k x, iteratedFDeriv ℝ k (fun x ↦ ∫ ξ, f x ξ) x =
          ∫ ξ, iteratedFDeriv ℝ k (fun x ↦ f x ξ) x := by
    let V := EuclideanSpace ℝ (Fin n)
    let D (k : ℕ) (x : X) (ξ : V) := iteratedFDeriv ℝ k (fun x ↦ f x ξ) x
    have hi (k : ℕ) (x : X) : Integrable (D k x) := by
      obtain ⟨b, hb, hbk⟩ := hbound k x
      exact hb.mono' (hmeas k x)
          (Filter.Eventually.of_forall (hbk x (Metric.mem_closedBall_self (by norm_num))))
    have hd (k : ℕ) (x : X) :
        HasFDerivAt (fun x ↦ ∫ ξ, D k x ξ)
          ((∫ ξ, D (k + 1) x ξ).curryLeft) x := by
      obtain ⟨b, hb, hbk⟩ := hbound (k + 1) x
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) W
      have heq (z : X) (ξ : V) : fderiv ℝ (fun z ↦ D k z ξ) z = L (D (k + 1) z ξ) := by
        dsimp only [D]
        rw [iteratedFDeriv_succ_eq_comp_left]
        exact (L.apply_symm_apply _).symm
      have hdiff (ξ : V) (z : X) : HasFDerivAt (fun z ↦ D k z ξ) (L (D (k + 1) z ξ)) z := by
        rw [← heq]
        exact ((hf ξ).differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) z).hasFDerivAt
      have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := D k) (F' := fun z ξ ↦ L (D (k + 1) z ξ)) (s := Metric.ball x 1)
        (bound := b) (x₀ := x) (Metric.ball_mem_nhds x (by norm_num))
        (Filter.Eventually.of_forall (fun z ↦ (hi k z).1)) (hi k x)
        ((L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hi (k + 1) x)).1)
        (Filter.Eventually.of_forall (fun ξ z hz ↦ by
          simpa using hbk z (Metric.ball_subset_closedBall hz) ξ))
        hb (Filter.Eventually.of_forall (fun ξ z _ ↦ hdiff ξ z))
      have hL : (∫ ξ, L (D (k + 1) x ξ)) = L (∫ ξ, D (k + 1) x ξ) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi (k + 1) x)
      rw [hL] at h
      exact h
    have hTaylor : HasFTaylorSeriesUpTo (∞ : ℕ∞ω) (fun x ↦ ∫ ξ, f x ξ)
        (fun x k ↦ ∫ ξ, D k x ξ) := by
      constructor
      · intro x
        let L := continuousMultilinearCurryFin0 ℝ X W
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
    exact ⟨hTaylor.contDiff, fun k x ↦ (hTaylor.eq_iteratedFDeriv (by simp) x).symm⟩
  -- Reconstruct symbol estimates from the reversed mixed-derivative bounds.
  have isSymbol_integral_of_bounds {n r q : ℕ}
      (p : SymbolFunction n r q) (hp : ContDiff ℝ ∞ (Function.uncurry p))
      (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
      (hB : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
          EuclideanSpace ℝ (Fin n) ↦ B z.1.1 z.1.2 z.2))
      (heq : ∀ x η, p x η = ∫ ζ, B x η ζ) (s : ℝ)
      (hb : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → ∀ i k : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
          ‖iteratedFDeriv ℝ k (fun η ↦
            iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x) η‖ ≤
              C * (1 + ‖η‖) ^ (s - (k : ℝ)) *
                (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))) :
      IsSymbol Set.univ s p := by
    let V := EuclideanSpace ℝ (Fin n)
    let W := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let decay (ζ : V) : ℝ := (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))
    have hdecay : Integrable decay := integrable_one_add_norm (by simp [V])
    have hnonneg (ζ : V) : 0 ≤ decay ζ := Real.rpow_nonneg (by positivity) _
    have hdx (i : ℕ) : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
        iteratedFDeriv ℝ i (fun x ↦ B x z.1.2 z.2) z.1.1) := by
      have h : ContDiff ℝ ∞ (Function.uncurry (fun u : V × V ↦ fun x : V ↦ B x u.1 u.2)) :=
        hB.comp ((contDiff_snd.prodMk contDiff_fst.fst).prodMk contDiff_fst.snd)
      exact (contDiff_parametric_iteratedFDeriv _ h i).comp
        ((contDiff_fst.snd.prodMk contDiff_snd).prodMk contDiff_fst.fst)
    have hmix (i k : ℕ) : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
        iteratedFDeriv ℝ k (fun η ↦ iteratedFDeriv ℝ i
          (fun x ↦ B x η z.2) z.1.1) z.1.2) := by
      have h : ContDiff ℝ ∞ (Function.uncurry (fun u : V × V ↦ fun η : V ↦
          iteratedFDeriv ℝ i (fun x ↦ B x η u.2) u.1)) :=
        (hdx i).comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
      exact (contDiff_parametric_iteratedFDeriv _ h k).comp
        ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
    have hxint (η : V) : ContDiff ℝ ∞ (fun x ↦ ∫ ζ, B x η ζ) ∧
        ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ ζ, B x η ζ) x =
          ∫ ζ, iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x := by
      refine smooth_integral_of_bounds (fun x ζ ↦ B x η ζ)
        (fun ζ ↦ hB.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)) ?_ ?_
      · intro i x
        exact ((hdx i).continuous.comp
          ((continuous_const.prodMk continuous_const).prodMk continuous_id)).aestronglyMeasurable
      intro i x₀
      obtain ⟨C, _, hC⟩ := hb (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1) i 0
      refine ⟨fun ζ ↦ C * (1 + ‖η‖) ^ s * decay ζ, hdecay.const_mul _, ?_⟩
      intro x hx ζ
      simpa only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] using hC x hx η ζ
    have hηint (i : ℕ) (x : V) :
        ContDiff ℝ ∞ (fun η ↦ ∫ ζ, iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x) ∧
        ∀ k η, iteratedFDeriv ℝ k
          (fun η ↦ ∫ ζ, iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x) η =
          ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x) η := by
      refine smooth_integral_of_bounds (fun η ζ ↦
        iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x)
        (fun ζ ↦ (hdx i).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const))
        ?_ ?_
      · intro k η
        let : SecondCountableTopologyEither V (V [×k]→L[ℝ] V [×i]→L[ℝ] W) :=
          secondCountableTopologyEither_of_left _ _
        exact ((hmix i k).continuous.comp
          ((continuous_const.prodMk continuous_const).prodMk continuous_id)).aestronglyMeasurable
      intro k η₀
      obtain ⟨C, hC, hCb⟩ := hb {x} isCompact_singleton i k
      have hbase : Continuous (fun η : V ↦ (1 : ℝ) + ‖η‖) :=
        continuous_const.add continuous_norm
      have hw : Continuous (fun η : V ↦ (1 + ‖η‖) ^ (s - (k : ℝ))) :=
        hbase.rpow_const (fun η ↦ Or.inl (by positivity))
      obtain ⟨M, hM⟩ := ((isCompact_closedBall η₀ 1).image hw).isBounded.exists_norm_le
      refine ⟨fun ζ ↦ C * max M 0 * decay ζ, hdecay.const_mul _, ?_⟩
      intro η hη ζ
      apply (hCb x (Set.mem_singleton x) η ζ).trans
      apply mul_le_mul_of_nonneg_right _ (hnonneg ζ)
      apply mul_le_mul_of_nonneg_left _ hC
      have h := hM ((1 + ‖η‖) ^ (s - (k : ℝ))) ⟨η, hη, rfl⟩
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h
      exact h.trans (le_max_left M 0)
    have hpderiv (i : ℕ) (x η : V) : iteratedFDeriv ℝ i (fun x ↦ p x η) x =
        ∫ ζ, iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x := by
      have h : (fun x ↦ p x η) = fun x ↦ ∫ ζ, B x η ζ := funext (fun x ↦ heq x η)
      rw [h, (hxint η).2 i x]
    have hpmix (i k : ℕ) (x η : V) :
        iteratedFDeriv ℝ k (fun η ↦ iteratedFDeriv ℝ i (fun x ↦ p x η) x) η =
          ∫ ζ, iteratedFDeriv ℝ k (fun η ↦ iteratedFDeriv ℝ i (fun x ↦ B x η ζ) x) η := by
      simp_rw [hpderiv]
      exact (hηint i x).2 k η
    refine ⟨?_, ?_⟩
    · rw [Set.univ_prod_univ]
      exact hp.contDiffOn
    intro L _ hL i k
    obtain ⟨C, hC, hCb⟩ := hb L hL i k
    refine ⟨C * (∫ ζ, decay ζ), mul_nonneg hC (integral_nonneg hnonneg), ?_⟩
    intro x hx η
    change ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ k (p x) η) x‖ ≤ _
    rw [← norm_iteratedFDeriv_exchange p hp i k x η, hpmix]
    calc
      _ ≤ ∫ ζ, C * (1 + ‖η‖) ^ (s - (k : ℝ)) * decay ζ :=
        norm_integral_le_of_norm_le (hdecay.const_mul _)
          (Filter.Eventually.of_forall (hCb x hx η))
      _ = _ := by rw [integral_const_mul]; ring
  -- Apply these local calculations to the original compact amplitude and all Taylor orders.
  let V := EuclideanSpace ℝ (Fin n)
  let W := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let R (x η ζ : V) : W :=
    ∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ζ : ℂ)) • a x y (η + ζ)
  obtain ⟨hS, hR, hb, _, _⟩ := amplitude_reduction_estimates m a ha hsupp
  let F (j : ℕ) (x η ζ : V) : W := (j.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ j (fun η ↦ R x η ζ) (η - ζ) (fun _ ↦ ζ)
  let T (N : ℕ) (x η ζ : V) : W := R x η ζ - ∑ j ∈ Finset.range N, F j x η ζ
  -- The Taylor terms are jointly smooth, including their varying direction vectors.
  have hF (j : ℕ) : ContDiff ℝ ∞ (fun z : (V × V) × V ↦ F j z.1.1 z.1.2 z.2) := by
    have hparam : ContDiff ℝ ∞ (Function.uncurry
        (fun u : V × V ↦ fun η : V ↦ R u.1 η u.2)) :=
      hR.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
    have hd : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
        iteratedFDeriv ℝ j (fun η ↦ R z.1.1 η z.2) (z.1.2 - z.2)) :=
      (contDiff_parametric_iteratedFDeriv _ hparam j).comp
        ((contDiff_fst.fst.prodMk contDiff_snd).prodMk (contDiff_fst.snd.sub contDiff_snd))
    change ContDiff ℝ ∞ (fun z : (V × V) × V ↦ (j.factorial : ℝ)⁻¹ • _)
    apply ContDiff.const_smul
    simp_rw [multilinear_diagonal_eq_sum]
    apply ContDiff.sum
    intro α _
    have hs : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
        ∏ t, inner ℝ z.2 (EuclideanSpace.single (α t) 1)) := by
      apply contDiff_prod
      intro t _
      exact contDiff_snd.inner ℝ contDiff_const
    have hv := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ V) W
      (fun t ↦ EuclideanSpace.single (α t) 1)).contDiff.comp hd
    exact hs.smul hv
  have hT (N : ℕ) : ContDiff ℝ ∞ (fun z : (V × V) × V ↦ T N z.1.1 z.1.2 z.2) :=
    hR.sub (ContDiff.sum (fun j _ ↦ hF j))
  have hTb (N : ℕ) (L : Set V) (hL : IsCompact L) (i k d : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ η ζ,
        ‖iteratedFDeriv ℝ k (fun η ↦ iteratedFDeriv ℝ i
          (fun x ↦ T (N + 1) x η ζ) x) η‖ ≤
            C * (1 + ‖η‖) ^ (m - (N + 1 : ℕ) - (k : ℝ)) *
              (1 + ‖ζ‖) ^ (-(d : ℝ)) :=
    taylor_remainder_symbol_bound R hR m L (hb L hL) N i k d
  -- Every Taylor coefficient is integrable as the difference of consecutive tails.
  have hTint (N : ℕ) (x η : V) : Integrable (T N x η) := by
    cases N with
    | zero =>
      simpa only [T, Finset.range_zero, Finset.sum_empty, sub_zero] using
        integrable_amplitudeSymbol_outer m a ha hsupp x η
    | succ N =>
      obtain ⟨C, _, hC⟩ := hTb N {x} isCompact_singleton 0 0 (n + 1)
      have hi : Integrable (fun ζ : V ↦ (1 + ‖ζ‖) ^ (-((n + 1 : ℕ) : ℝ))) :=
        integrable_one_add_norm (by simp [V])
      have hm : AEStronglyMeasurable (T (N + 1) x η) :=
        (((hT (N + 1)).continuous.comp
          ((continuous_const.prodMk continuous_const).prodMk continuous_id)).aestronglyMeasurable)
      apply (hi.const_mul (C * (1 + ‖η‖) ^ (m - (N + 1 : ℕ)))).mono' hm
      filter_upwards with ζ
      simpa only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] using
        hC x (Set.mem_singleton x) η ζ
  have hFint (j : ℕ) (x η : V) : Integrable (F j x η) := by
    have heq : F j x η = fun ζ ↦ T j x η ζ - T (j + 1) x η ζ := by
      funext ζ
      simp only [T, Finset.sum_range_succ]
      abel
    rw [heq]
    exact (hTint j x η).sub (hTint (j + 1) x η)
  have hres (N : ℕ) (x η : V) :
      (amplitudeSymbol a - ∑ j ∈ Finset.range N, amplitudeExpansionTerm a j) x η =
        ((2 * Real.pi) ^ n)⁻¹ • ∫ ζ, T N x η ζ := by
    change amplitudeSymbol a x η - (∑ j ∈ Finset.range N, amplitudeExpansionTerm a j) x η = _
    simp only [Finset.sum_apply]
    rw [show (fun ζ ↦ T N x η ζ) =
      (fun ζ ↦ R x η ζ - ∑ j ∈ Finset.range N, F j x η ζ) from rfl,
      integral_sub (integrable_amplitudeSymbol_outer m a ha hsupp x η)
        (integrable_finsetSum _ (fun j _ ↦ hFint j x η)),
      smul_sub, integral_finsetSum _ (fun j _ ↦ hFint j x η), Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact (integral_amplitude_taylorTerm m a ha hsupp j x η).symm
  -- Apply the mixed-derivative bounds to the actual original residual.
  intro N
  cases N with
  | zero => simpa only [Nat.cast_zero, sub_zero, Finset.range_zero, Finset.sum_empty] using hS
  | succ N =>
    let p : SymbolFunction n r q :=
      amplitudeSymbol a - ∑ j ∈ Finset.range (N + 1), amplitudeExpansionTerm a j
    let d : ℝ := (2 * Real.pi) ^ n
    have hd : d ≠ 0 := pow_ne_zero n (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have hp : ContDiff ℝ ∞ (Function.uncurry p) := by
      have hs : ContDiff ℝ ∞ (Function.uncurry (amplitudeSymbol a)) := by
        simpa only [Set.univ_prod_univ, contDiffOn_univ] using hS.1
      have ht (j : ℕ) : ContDiff ℝ ∞ (Function.uncurry (amplitudeExpansionTerm a j)) := by
        simpa only [Set.univ_prod_univ, contDiffOn_univ] using
          (isSymbol_amplitudeExpansionTerm m a ha j).1
      have heq : Function.uncurry p = (fun z : V × V ↦ amplitudeSymbol a z.1 z.2 -
          ∑ j ∈ Finset.range (N + 1), amplitudeExpansionTerm a j z.1 z.2) := by
        funext z
        simp only [p, Function.uncurry, Pi.sub_apply, Finset.sum_apply]
      rw [heq]
      exact hs.sub (ContDiff.sum (s := Finset.range (N + 1)) (fun j _ ↦ ht j))
    have hq : IsSymbol Set.univ (m - (N + 1 : ℕ)) (fun x η ↦ d • p x η) := by
      apply isSymbol_integral_of_bounds _ (hp.const_smul d) (T (N + 1)) (hT (N + 1))
      · intro x η
        rw [show p x η = d⁻¹ • ∫ ζ, T (N + 1) x η ζ from hres (N + 1) x η,
          smul_inv_smul₀ hd]
      · intro L hL i k
        exact hTb N L hL i k (n + 1)
    have hfinal := hq.smul isOpen_univ ((d⁻¹ : ℝ) : ℂ)
    have heq : ((d⁻¹ : ℝ) : ℂ) • (fun x η ↦ d • p x η) = p := by
      funext x η
      change ((d⁻¹ : ℝ) : ℂ) • ((d : ℂ) • p x η) = _
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hd,
        Complex.ofReal_one, one_smul]
    rw [heq] at hfinal
    exact hfinal

set_option maxHeartbeats 4000000 in

open scoped FourierTransform in
/-- The integral determines a unique continuous complex-linear operator on Schwartz functions. -/
theorem existsUnique_amplitudeOperator (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a)) :
    ∃! T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      ∀ u x, T u x = amplitudeApply a u x := by
  /- Uniform Fourier-Schwartz bounds for the compact y family dominate all
  x derivatives of the frequency integral. Differentiation under the integral
  gives a smooth output supported in the compact first projection. Bounds by
  finitely many input Schwartz seminorms make the resulting Schwartz map continuous.
  The two integrability results give complex linearity, and the prescribed values
  for every u and x give uniqueness. -/
  have mixed_norm {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y : P) :
      ‖iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y‖ =
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x‖ := by
    have mixed_fderiv_comm {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
        (x : X) (y : Y) (u : X) (v : Y) :
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v := by
      let F := Function.uncurry f
      let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
      let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
      have hF : Differentiable ℝ F := hf.differentiable (by simp)
      have hDF : Differentiable ℝ (fderiv ℝ F) :=
        (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp)
      -- Each partial first derivative is the full derivative restricted to one factor.
      have hleft (a : X) (b : Y) :
          fderiv ℝ (fun t ↦ f t b) a = (fderiv ℝ F (a, b)).comp L := by
        exact ((hF (a, b)).hasFDerivAt.comp a
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)).fderiv
      have hright (a : X) (b : Y) :
          fderiv ℝ (f a) b = (fderiv ℝ F (a, b)).comp R :=
        ((hF (a, b)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right (𝕜 := ℝ) a b)).fderiv
      -- Differentiate those restrictions through fixed continuous linear composition maps.
      have hxy : fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
          fderiv ℝ (fderiv ℝ F) (x, y) (0, v) (u, 0) := by
        simp_rw [hleft]
        let C : ((X × Y) →L[ℝ] V) →L[ℝ] X →L[ℝ] V :=
          (ContinuousLinearMap.compL ℝ X (X × Y) V).flip L
        have hd := (hDF (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
        have hc := C.hasFDerivAt.comp y hd
        exact congrArg (fun K : Y →L[ℝ] X →L[ℝ] V ↦ K v u) hc.fderiv
      have hyx : fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v =
          fderiv ℝ (fderiv ℝ F) (x, y) (u, 0) (0, v) := by
        simp_rw [hright]
        let C : ((X × Y) →L[ℝ] V) →L[ℝ] Y →L[ℝ] V :=
          (ContinuousLinearMap.compL ℝ Y (X × Y) V).flip R
        have hd := (hDF (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
        have hc := C.hasFDerivAt.comp x hd
        exact congrArg (fun K : X →L[ℝ] Y →L[ℝ] V ↦ K u v) hc.fderiv
      -- Symmetry applies on the full product, with the original two factor directions.
      rw [hxy, hyx]
      exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (0, v) (u, 0)
    have mixed_fderiv_apply_comm {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : X → Y → V)
        (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y) :
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u := by
      have hl : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) := by
        have hh : ContDiff ℝ ∞ (Function.uncurry (fun z t ↦ f t z)) :=
          hf.comp (contDiff_snd.prodMk contDiff_fst)
        exact hh.fderiv contDiff_const (by simp)
      have hr : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (f t) y) :=
        hf.fderiv contDiff_const (by simp)
      rw [fderiv_clm_apply (hl.differentiable (by simp) y) (differentiableAt_const u),
        fderiv_clm_apply (hr.differentiable (by simp) x) (differentiableAt_const v)]
      simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply] using mixed_fderiv_comm f hf x y u v
    have parametric {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
        ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
      induction k with
      | zero =>
        exact hf.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
      | succ k ih =>
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
          ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
        have hd : ContDiff ℝ ∞
            (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
          h.fderiv contDiff_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
            _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
    have iterated_comm {X Y V : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup V] [NormedSpace ℝ V]
        (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
          (f : X → Y → W) (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y),
          fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
            fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
        (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : X) (y : Y)
        (u : X) :
        iteratedFDeriv ℝ k (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y =
          fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) y) x u := by
      induction k generalizing y with
      | zero =>
        let J := (continuousMultilinearCurryFin0 ℝ Y V).symm.toContinuousLinearEquiv
        exact (congrArg (fun T : X →L[ℝ] Y [×0]→L[ℝ] V ↦ T u)
          (J.comp_fderiv (f := fun t ↦ f t y) (x := x))).symm
      | succ k ih =>
        ext v
        have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
          parametric f hf k
        rw [iteratedFDeriv_succ_apply_left]
        have hi : (fun z ↦ iteratedFDeriv ℝ k
            (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) =
            (fun z ↦ fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) z) x u) := by
          funext z
          exact ih z
        change ((fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k
          (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) y) (v 0)) (Fin.tail v) = _
        rw [hi]
        have hc := comm (fun t z ↦ iteratedFDeriv ℝ k (f t) z) hs x y u (v 0)
        rw [hc]
        have hd : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) := by
          have h : ContDiff ℝ ∞
              (Function.uncurry (fun t : X ↦ fun z : Y ↦ iteratedFDeriv ℝ k (f t) z)) := hs
          exact h.fderiv contDiff_const (by simp)
        have heq : (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y v) =
            (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0) (Fin.tail v)) := by
          funext t
          exact iteratedFDeriv_succ_apply_left v
        have hx : ContDiff ℝ ∞ (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y) :=
          (parametric f hf (k + 1)).comp (contDiff_id.prodMk contDiff_const)
        have ha : ContDiff ℝ ∞
            (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0)) :=
          hd.clm_apply contDiff_const
        rw [← fderiv_continuousMultilinear_apply_const_apply
          (hx.contDiffAt.differentiableAt (by simp)), heq,
          fderiv_continuousMultilinear_apply_const_apply (ha.contDiffAt.differentiableAt (by simp))]
    have apply_deriv {X Y W : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup W] [NormedSpace ℝ W]
        (k l : ℕ) (g : X → Y [×l]→L[ℝ] W) (hg : ContDiff ℝ ∞ g)
        (x : X) (v : Fin k → X) (w : Fin l → Y) :
        iteratedFDeriv ℝ k (fun x ↦ g x w) x v = iteratedFDeriv ℝ k g x v w := by
      let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin l ↦ Y) W w
      exact congrArg (fun T : X [×k]→L[ℝ] W ↦ T v)
        (L.iteratedFDeriv_comp_left hg.contDiffAt (by simp))
    have swap (i j : ℕ) : ∀ (f : P → P → V),
        ContDiff ℝ ∞ (Function.uncurry f) → ∀ (x y : P) (v : Fin i → P) (w : Fin j → P),
        iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y w v =
          iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x v w := by
      induction i with
      | zero =>
        intro f hf x y v w
        have hs : ContDiff ℝ ∞ (fun b ↦ iteratedFDeriv ℝ 0 (fun a ↦ f a b) x) :=
          ((parametric (fun y x ↦ f x y)
          (hf.comp (contDiff_snd.prodMk contDiff_fst)) 0).comp
            (contDiff_id.prodMk contDiff_const))
        rw [← apply_deriv j 0 _ hs y w v]
        simp only [iteratedFDeriv_zero_apply]
      | succ i ih =>
        intro f hf x y v w
        let u := v (Fin.last i)
        let g (a b : P) : V := fderiv ℝ (fun t ↦ f t b) a u
        have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
          have hh : ContDiff ℝ ∞
              (Function.uncurry (fun z : P × P ↦ fun a : P ↦ f a z.2)) :=
            hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
          exact (hh.fderiv contDiff_fst (by simp)).clm_apply contDiff_const
        have hs (k : ℕ) : ContDiff ℝ ∞
            (fun b ↦ iteratedFDeriv ℝ k (fun a ↦ f a b) x) :=
          (parametric (fun b a ↦ f a b) (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
            (contDiff_id.prodMk contDiff_const)
        have hgs : ContDiff ℝ ∞
            (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x) :=
          (parametric (fun b a ↦ g a b) (hg.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
            (contDiff_id.prodMk contDiff_const)
        have hsx : ContDiff ℝ ∞ (fun a ↦ iteratedFDeriv ℝ j (f a) y) :=
          (parametric f hf j).comp (contDiff_id.prodMk contDiff_const)
        have hvalue (b : P) :
            iteratedFDeriv ℝ (i + 1) (fun a ↦ f a b) x v =
              iteratedFDeriv ℝ i (fun a ↦ g a b) x (Fin.init v) := by
          rw [iteratedFDeriv_succ_apply_right]
          have hd : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ f a b)) :=
            (hf.comp (contDiff_id.prodMk contDiff_const)).fderiv_right (by simp)
          exact (iteratedFDeriv_clm_apply_const_apply hd (by simp)).symm
        calc
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ (i + 1) (fun a ↦ f a b) x v) y w :=
            (apply_deriv j (i + 1) _ (hs (i + 1)) y w v).symm
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x (Fin.init v)) y w := by
            simp_rw [hvalue]
          _ = iteratedFDeriv ℝ j
              (fun b ↦ iteratedFDeriv ℝ i (fun a ↦ g a b) x) y w (Fin.init v) :=
            apply_deriv j i _ hgs y w (Fin.init v)
          _ = iteratedFDeriv ℝ i
              (fun a ↦ iteratedFDeriv ℝ j (g a) y) x (Fin.init v) w := ih g hg x y _ w
          _ = iteratedFDeriv ℝ i
              (fun a ↦ fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y) a u)
                x (Fin.init v) w := by
            have heq (a : P) : iteratedFDeriv ℝ j (g a) y =
                fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y) a u :=
              iterated_comm mixed_fderiv_apply_comm f hf j a y u
            simp_rw [heq]
          _ = iteratedFDeriv ℝ (i + 1)
              (fun a ↦ iteratedFDeriv ℝ j (f a) y) x v w := by
            rw [iteratedFDeriv_succ_apply_right]
            have hd : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y)) :=
              hsx.fderiv_right (by simp)
            exact congrArg (fun T : P [×j]→L[ℝ] V ↦ T w)
              (iteratedFDeriv_clm_apply_const_apply hd (by simp))
    -- A permutation of the two blocks of directions preserves the multilinear operator norm.
    let T := iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (f x) y) x
    let S := iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ f x y) x) y
    apply le_antisymm
    · apply S.opNorm_le_bound (norm_nonneg T)
      intro w
      apply (S w).opNorm_le_bound (by positivity)
      intro v
      rw [show S w v = T v w from swap i j f hf x y v w]
      calc
        _ ≤ (‖T‖ * ∏ t, ‖v t‖) * ∏ t, ‖w t‖ :=
          (T v).le_of_opNorm_le (T.le_opNorm v) w
        _ = _ := by ring
    · apply T.opNorm_le_bound (norm_nonneg S)
      intro v
      apply (T v).opNorm_le_bound (by positivity)
      intro w
      rw [show T v w = S w v from (swap i j f hf x y v w).symm]
      calc
        _ ≤ (‖S‖ * ∏ t, ‖w t‖) * ∏ t, ‖v t‖ :=
          (S w).le_of_opNorm_le (S.le_opNorm w) v
        _ = _ := by ring
  have zero_norm {n r q : ℕ} (m : ℝ) (a : AmplitudeFunction n r q)
      (ha : IsAmplitude m a)
      (i j : ℕ) (x y ξ : EuclideanSpace ℝ (Fin n)) :
      ‖amplitudeDerivative a i j 0 x y ξ‖ =
        ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (fun y ↦ a x y ξ) y) x‖ := by
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let J : H ≃ₗᵢ[ℝ] V [×0]→L[ℝ] H := (continuousMultilinearCurryFin0 ℝ V H).symm
    let T : (V [×j]→L[ℝ] H) ≃ₗᵢ[ℝ] V [×j]→L[ℝ] V [×0]→L[ℝ] H :=
      { (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
          (fun _ : Fin j ↦ V)).toLinearEquiv with
        norm_map' := fun D ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap D }
    have heq : (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ iteratedFDeriv ℝ 0 (a z w) ξ) y) =
        T ∘ (fun z ↦ iteratedFDeriv ℝ j (fun w ↦ a z w ξ) y) := by
      funext z
      have hzero : (fun w ↦ iteratedFDeriv ℝ 0 (a z w) ξ) = J ∘ (fun w ↦ a z w ξ) := by
        funext w
        exact congrFun iteratedFDeriv_zero_eq_comp ξ
      rw [hzero]
      exact J.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_left
        ((ha.1.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).contDiffAt)
        (by simp)
    simp only [amplitudeDerivative, heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    rfl
  have amplitude_bounds {n r q : ℕ}
      (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
      (hsupp : HasCompactSupport (Function.uncurry a)) :
      ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ y,
        y ∈ Prod.snd '' tsupport (Function.uncurry a) →
          ‖iteratedFDeriv ℝ j
            (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ) x) y‖ ≤
              C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let Kx : Set V := Prod.fst '' tsupport (Function.uncurry a)
    let Ky : Set V := Prod.snd '' tsupport (Function.uncurry a)
    have hKx : IsCompact Kx := hsupp.image continuous_fst
    have hKy : IsCompact Ky := hsupp.image continuous_snd
    intro i j
    obtain ⟨C, hC, hb⟩ := ha.2 (Kx ×ˢ Ky) (hKx.prod hKy) i j 0
    refine ⟨C, hC, ?_⟩
    intro x ξ y hy
    by_cases hx : x ∈ Kx
    · have hswap := mixed_norm (fun x y ↦ a x y ξ)
        (ha.1.comp (contDiff_id.prodMk contDiff_const)) i j x y
      rw [hswap, ← zero_norm m a ha i j x y ξ]
      calc
        _ ≤ C * (1 + ‖ξ‖) ^ m := by simpa using hb x y ⟨hx, hy⟩ ξ
        _ ≤ C * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)) hC
        _ = _ := by rw [Real.rpow_natCast]
    · have hzero : (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ) x) = 0 := by
        funext z
        have hs : tsupport (fun x ↦ a x z ξ) ⊆ Kx := by
          apply closure_minimal ?_ hKx.isClosed
          intro w hw
          by_contra hwK
          have hz : Function.uncurry a (w, z) = 0 := image_eq_zero_of_notMem_tsupport
            (fun h ↦ hwK ⟨(w, z), h, rfl⟩)
          exact hw (congrFun hz ξ)
        exact image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (hs (tsupport_iteratedFDeriv_subset i h)))
      rw [hzero]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      positivity
  have fourier_bound {ι : Type} {n r : ℕ} {W : Type}
      [NormedAddCommGroup W] [NormedSpace ℂ W]
      (f : ι → 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
      (hf : ∀ t u ξ, ContDiff ℝ ∞ (f t u ξ))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hsupp : ∀ t u ξ, tsupport (f t u ξ) ⊆ K) (d : ℕ)
      (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t u ξ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (f t u ξ) y‖ ≤ C *
          (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℂ _ _) u * (1 + ‖ξ‖) ^ d)
      (c : ℝ) (hc : c ≠ 0) (k : ℕ) :
      ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t u ξ,
        ‖𝓕 (f t u ξ) (c • ξ)‖ ≤ C *
          (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ _ _) u *
            (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let S (t : ι) (u : 𝓢(V, E)) (ξ : V) : 𝓢(V, W) :=
      (show HasCompactSupport (f t u ξ) from
        hK.of_isClosed_subset (isClosed_tsupport _) (hsupp t u ξ)).toSchwartzMap (hf t u ξ)
    have hseminorm (j i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t u ξ,
        SchwartzMap.seminorm ℂ j i (S t u ξ) ≤ C *
          (Finset.Iic (0, i)).sup (schwartzSeminormFamily ℂ V E) u * (1 + ‖ξ‖) ^ d := by
      obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
      obtain ⟨C, hC, hbound⟩ := hb i
      refine ⟨(max R 0) ^ j * C, by positivity, ?_⟩
      intro t u ξ
      apply SchwartzMap.seminorm_le_bound ℂ j i (S t u ξ) (by positivity)
      intro y
      change ‖y‖ ^ j * ‖iteratedFDeriv ℝ i (f t u ξ) y‖ ≤ _
      by_cases hy : y ∈ K
      · calc
          _ ≤ (max R 0) ^ j * (C *
              (Finset.Iic (0, i)).sup (schwartzSeminormFamily ℂ V E) u *
                (1 + ‖ξ‖) ^ d) := by
            gcongr
            · exact (hR y hy).trans (le_max_left R 0)
            · exact hbound t u ξ y hy
          _ = _ := by ring
      · have hz : iteratedFDeriv ℝ i (f t u ξ) y = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun h ↦ hy (hsupp t u ξ (tsupport_iteratedFDeriv_subset i h)))
        rw [hz, norm_zero, mul_zero]
        positivity
    -- Fourier continuity selects a finite list of seminorms before the input bound is taken.
    let e : V ≃L[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V c hc).toContinuousLinearEquiv
    let T : 𝓢(V, W) →L[ℂ] 𝓢(V, W) :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e).comp (FourierTransform.fourierCLM ℂ _)
    let p : Seminorm ℂ 𝓢(V, W) :=
      (Finset.Iic (d + k, 0)).sup (fun i ↦ SchwartzMap.seminorm ℂ i.1 i.2)
    let q : Seminorm ℂ 𝓢(V, W) := p.comp T.toLinearMap
    have hp : Continuous p :=
      Seminorm.continuous_finsetSup (fun i _ ↦ (schwartz_withSeminorms ℂ V W).continuous_seminorm i)
    obtain ⟨s, A, _, hA⟩ := Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℂ V W) q (hp.comp T.continuous)
    choose C hC hbound using hseminorm
    let J : ℕ := s.sup Prod.snd
    let B := ∑ i ∈ s, C i.1 i.2
    have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ ↦ hC i.1 i.2)
    refine ⟨J, 2 ^ (d + k) * A * B, by positivity, ?_⟩
    intro t u ξ
    let P : ℝ := (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ V E) u
    have hP : 0 ≤ P := apply_nonneg _ _
    have hsub (i : ℕ × ℕ) (hi : i ∈ s) :
        (Finset.Iic (0, i.2)).sup (schwartzSeminormFamily ℂ V E) u ≤ P := by
      apply Seminorm.finset_sup_apply_le hP
      intro b hb
      apply Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ V E) ?_) u
      apply Finset.mem_Iic.mpr
      have hb' := Finset.mem_Iic.mp hb
      exact ⟨hb'.1, hb'.2.trans (show i.2 ≤ J from Finset.le_sup (f := Prod.snd) hi)⟩
    have hT : T (S t u ξ) ξ = 𝓕 (f t u ξ) (c • ξ) := rfl
    have hs : s.sup (schwartzSeminormFamily ℂ V W) (S t u ξ) ≤
        B * P * (1 + ‖ξ‖) ^ d := by
      apply Seminorm.finset_sup_apply_le (by positivity)
      intro i hi
      calc
        _ ≤ C i.1 i.2 * (Finset.Iic (0, i.2)).sup
            (schwartzSeminormFamily ℂ V E) u * (1 + ‖ξ‖) ^ d := hbound i.1 i.2 t u ξ
        _ ≤ B * P * (1 + ‖ξ‖) ^ d := by
          have hiC := hC i.1 i.2
          gcongr
          · exact Finset.single_le_sum (fun j _ ↦ hC j.1 j.2) hi
          · exact hsub i hi
    have hweight : (1 + ‖ξ‖) ^ (d + k) * ‖T (S t u ξ) ξ‖ ≤
        (2 ^ (d + k) * A * B) * P * (1 + ‖ξ‖) ^ d := by
      calc
        _ ≤ 2 ^ (d + k) * p (T (S t u ξ)) := by
          simpa only [p, schwartzSeminormFamily, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
            LinearIsometryEquiv.norm_map] using
            SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
              (m := (d + k, 0)) (le_refl _) (le_refl _) (T (S t u ξ)) ξ
        _ ≤ 2 ^ (d + k) * (A * (s.sup (schwartzSeminormFamily ℂ V W) (S t u ξ))) :=
          mul_le_mul_of_nonneg_left (hA (S t u ξ)) (by positivity)
        _ ≤ 2 ^ (d + k) * (A * (B * P * (1 + ‖ξ‖) ^ d)) := by gcongr
        _ = _ := by ring
    have hpos : 0 < 1 + ‖ξ‖ := by positivity
    have hcancel : (1 + ‖ξ‖) ^ k * ‖T (S t u ξ) ξ‖ ≤
        (2 ^ (d + k) * A * B) * P := by
      apply (mul_le_mul_iff_right₀ (pow_pos hpos d)).mp
      simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hweight
    calc
      _ ≤ ((2 ^ (d + k) * A * B) * P) / (1 + ‖ξ‖) ^ k :=
        (le_div_iff₀ (pow_pos hpos k)).mpr (by simpa only [hT, mul_comm] using hcancel)
      _ = _ := by rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_natCast]; rfl
  have integrate {n : ℕ} {X W : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (f : X → EuclideanSpace ℝ (Fin n) → W)
      (hf : ∀ ξ, ContDiff ℝ ∞ (fun x ↦ f x ξ))
      (hmeas : ∀ k x, AEStronglyMeasurable
        (fun ξ ↦ iteratedFDeriv ℝ k (fun x ↦ f x ξ) x))
      (hbound : ∀ k : ℕ, ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
        Integrable b ∧ ∀ x ξ, ‖iteratedFDeriv ℝ k (fun x ↦ f x ξ) x‖ ≤ b ξ) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f x ξ) ∧
        ∀ k x, iteratedFDeriv ℝ k (fun x ↦ ∫ ξ, f x ξ) x =
          ∫ ξ, iteratedFDeriv ℝ k (fun x ↦ f x ξ) x := by
    let V := EuclideanSpace ℝ (Fin n)
    let D (k : ℕ) (x : X) (ξ : V) := iteratedFDeriv ℝ k (fun x ↦ f x ξ) x
    have hi (k : ℕ) (x : X) : Integrable (D k x) := by
      obtain ⟨b, hb, hbk⟩ := hbound k
      exact hb.mono' (hmeas k x)
          (Filter.Eventually.of_forall (hbk x))
    have hd (k : ℕ) (x : X) :
        HasFDerivAt (fun x ↦ ∫ ξ, D k x ξ)
          ((∫ ξ, D (k + 1) x ξ).curryLeft) x := by
      obtain ⟨b, hb, hbk⟩ := hbound (k + 1)
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) W
      have heq (z : X) (ξ : V) : fderiv ℝ (fun z ↦ D k z ξ) z = L (D (k + 1) z ξ) := by
        dsimp only [D]
        rw [iteratedFDeriv_succ_eq_comp_left]
        exact (L.apply_symm_apply _).symm
      have hdiff (ξ : V) (z : X) : HasFDerivAt (fun z ↦ D k z ξ) (L (D (k + 1) z ξ)) z := by
        rw [← heq]
        exact ((hf ξ).differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) z).hasFDerivAt
      have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := D k) (F' := fun z ξ ↦ L (D (k + 1) z ξ)) (s := Set.univ)
        (bound := b) (x₀ := x) (by simp)
        (Filter.Eventually.of_forall (fun z ↦ (hi k z).1)) (hi k x)
        ((L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hi (k + 1) x)).1)
        (Filter.Eventually.of_forall (fun ξ z _ ↦ by simpa using hbk z ξ))
        hb (Filter.Eventually.of_forall (fun ξ z _ ↦ hdiff ξ z))
      have hL : (∫ ξ, L (D (k + 1) x ξ)) = L (∫ ξ, D (k + 1) x ξ) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi (k + 1) x)
      rw [hL] at h
      exact h
    have hTaylor : HasFTaylorSeriesUpTo (∞ : ℕ∞ω) (fun x ↦ ∫ ξ, f x ξ)
        (fun x k ↦ ∫ ξ, D k x ξ) := by
      constructor
      · intro x
        let L := continuousMultilinearCurryFin0 ℝ X W
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
    exact ⟨hTaylor.contDiff, fun k x ↦ (hTaylor.eq_iteratedFDeriv (by simp) x).symm⟩
  have compact_integrate {n : ℕ} {W : Type}
      [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
      (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
      (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (Kx Ky : Set (EuclideanSpace ℝ (Fin n))) (hKx : IsCompact Kx) (hKy : IsCompact Ky)
      (hzero : ∀ x y, x ∉ Kx ∨ y ∉ Ky → f x y = 0) :
      ContDiff ℝ ∞ (fun x ↦ ∫ y, f x y) ∧
        ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ y, f x y) x =
          ∫ y, iteratedFDeriv ℝ i (fun x ↦ f x y) x := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
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
    let D (i : ℕ) (x y : V) := iteratedFDeriv ℝ i (fun x ↦ f x y) x
    have hD (i : ℕ) : ContDiff ℝ ∞ (Function.uncurry (D i)) :=
      (parametric (fun y x ↦ f x y) (hf.comp (contDiff_snd.prodMk contDiff_fst)) i).comp
        (contDiff_snd.prodMk contDiff_fst)
    have hDzero (i : ℕ) (x y : V) (h : x ∉ Kx ∨ y ∉ Ky) : D i x y = 0 := by
      rcases h with hx | hy
      · have hs : tsupport (fun x ↦ f x y) ⊆ Kx := by
          apply closure_minimal ?_ hKx.isClosed
          intro z hz
          by_contra hzx
          exact hz (hzero z y (Or.inl hzx))
        change iteratedFDeriv ℝ i (fun x ↦ f x y) x = 0
        exact image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (hs (tsupport_iteratedFDeriv_subset i h)))
      · have hz : (fun x ↦ f x y) = 0 := funext (fun x ↦ hzero x y (Or.inr hy))
        simp [D, hz]
    apply integrate f
      (fun y ↦ hf.comp (contDiff_id.prodMk contDiff_const))
      (fun i x ↦ ((hD i).continuous.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    intro i
    obtain ⟨R, hR⟩ := ((hKx.prod hKy).image (hD i).continuous).isBounded.exists_norm_le
    refine ⟨Ky.indicator (fun _ ↦ max R 0),
      (integrable_indicator_iff hKy.measurableSet).mpr
        (integrableOn_const (μ := volume) (C := max R 0) hKy.measure_lt_top.ne), ?_⟩
    intro x y
    change ‖D i x y‖ ≤ _
    by_cases hy : y ∈ Ky
    · rw [Set.indicator_of_mem hy]
      by_cases hx : x ∈ Kx
      · exact (hR (D i x y) ⟨(x, y), ⟨hx, hy⟩, rfl⟩).trans (le_max_left _ _)
      · rw [hDzero i x y (Or.inl hx), norm_zero]
        exact le_max_right _ _
    · rw [Set.indicator_of_notMem hy, hDzero i x y (Or.inr hy), norm_zero]
  have partial_fourier_bound {n r q : ℕ}
      (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
      (hsupp : HasCompactSupport (Function.uncurry a))
      (hab : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ y,
        y ∈ Prod.snd '' tsupport (Function.uncurry a) →
          ‖iteratedFDeriv ℝ j
            (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ) x) y‖ ≤
              C * (1 + ‖ξ‖) ^ ⌈m⌉₊)
      (c : ℝ) (hc : c ≠ 0) :
      ∀ i k : ℕ, ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ x (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) ξ,
          ‖𝓕 (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ (u y)) x) (c • ξ)‖ ≤
            C * (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ _ _) u *
              (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    let H := E →L[ℂ] F
    let K : Set V := Prod.snd '' tsupport (Function.uncurry a)
    have hK : IsCompact K := hsupp.image continuous_snd
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
    let f (u : 𝓢(V, E)) (x ξ y : V) : F := a x y ξ (u y)
    have hf (u : 𝓢(V, E)) : ContDiff ℝ ∞
        (fun z : (V × V) × V ↦ f u z.1.1 z.2 z.1.2) := by
      let R : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
      exact (R.contDiff.comp ha.1).clm_apply ((u.smooth ⊤).comp contDiff_fst.snd)
    let D (i : ℕ) (x : V) (u : 𝓢(V, E)) (ξ y : V) :=
      iteratedFDeriv ℝ i (fun x ↦ f u x ξ y) x
    have hDs (i : ℕ) (u : 𝓢(V, E)) : ContDiff ℝ ∞
        (fun z : (V × V) × V ↦ D i z.1.1 u z.2 z.1.2) := by
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : V × V ↦ fun x : V ↦ f u x z.2 z.1)) :=
        (hf u).comp ((contDiff_snd.prodMk contDiff_fst.fst).prodMk contDiff_fst.snd)
      exact (parametric _ h i).comp
        ((contDiff_fst.snd.prodMk contDiff_snd).prodMk contDiff_fst.fst)
    have hDsupport (i : ℕ) (x : V) (u : 𝓢(V, E)) (ξ : V) : tsupport (D i x u ξ) ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      have hz (x : V) : a x y ξ = 0 := by
        have hzero : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hyK ⟨(x, y), h, rfl⟩)
        exact congrFun hzero ξ
      have hzfun : (fun x ↦ f u x ξ y) = 0 := by funext x; simp [f, hz]
      exact hy (by simp [D, hzfun])
    have hDbound (i j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x u ξ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (D i x u ξ) y‖ ≤ C *
          (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℂ V E) u * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
      let R : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
      let B : (V [×i]→L[ℝ] H) →L[ℝ] E →L[ℝ] (V [×i]→L[ℝ] F) :=
        ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ V) H F).comp
          R.flip).flip
      let A (x ξ y : V) := iteratedFDeriv ℝ i (fun x ↦ a x y ξ) x
      have hA (x ξ : V) : ContDiff ℝ ∞ (A x ξ) := by
        have h : ContDiff ℝ ∞ (Function.uncurry (fun y x : V ↦ a x y ξ)) :=
          ha.1.comp ((contDiff_snd.prodMk contDiff_fst).prodMk contDiff_const)
        exact (parametric _ h i).comp (contDiff_id.prodMk contDiff_const)
      have heq (x ξ y : V) (u : 𝓢(V, E)) : D i x u ξ y = B (A x ξ y) (u y) := by
        let L : H →L[ℝ] F := R.flip (u y)
        have hs : ContDiff ℝ ∞ (fun x ↦ a x y ξ) :=
          ha.1.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)
        exact L.iteratedFDeriv_comp_left hs.contDiffAt (by simp)
      choose C hC hbound using fun j ↦ hab i j
      let M : ℝ := ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * C l
      have hM : 0 ≤ M := Finset.sum_nonneg (fun l _ ↦ mul_nonneg (by positivity) (hC l))
      refine ⟨‖B‖ * M, by positivity, ?_⟩
      intro x u ξ y hy
      have hEq : D i x u ξ = fun y ↦ B (A x ξ y) (u y) := funext (fun y ↦ heq x ξ y u)
      rw [hEq]
      calc
        _ ≤ ‖B‖ * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (A x ξ) y‖ * ‖iteratedFDeriv ℝ (j - l) u y‖ :=
          B.norm_iteratedFDeriv_le_of_bilinear (hA x ξ) (u.smooth ⊤) y (by simp)
        _ ≤ ‖B‖ * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
            (C l * (1 + ‖ξ‖) ^ ⌈m⌉₊) *
              (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℂ V E) u := by
          apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
          apply Finset.sum_le_sum
          intro l _
          have hlC := hC l
          gcongr
          · exact hbound l x ξ y hy
          · apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ u (j - l) y).trans
            change schwartzSeminormFamily ℂ V E (0, j - l) u ≤ _
            apply Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ V E) ?_) u
            exact Finset.mem_Iic.mpr ⟨le_refl _, Nat.sub_le _ _⟩
        _ = _ := by
          dsimp [M]
          simp only [mul_assoc, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro l _
          ring
    intro i k
    have hS (x : V) (u : 𝓢(V, E)) (ξ : V) : ContDiff ℝ ∞ (D i x u ξ) :=
      (hDs i u).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
    exact fourier_bound (ι := V) (n := n) (r := r) (W := V [×i]→L[ℝ] F)
      (D i) hS K hK (hDsupport i) ⌈m⌉₊ (hDbound i) c hc k
  have inner_smooth {n r q : ℕ}
      (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
      (hsupp : HasCompactSupport (Function.uncurry a))
      (hab : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ y,
        y ∈ Prod.snd '' tsupport (Function.uncurry a) →
          ‖iteratedFDeriv ℝ j
            (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ) x) y‖ ≤
              C * (1 + ‖ξ‖) ^ ⌈m⌉₊)
      (c : ℝ) :
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) ξ,
        ContDiff ℝ ∞ (fun x ↦ 𝓕 (fun y ↦ a x y ξ (u y)) (c • ξ)) ∧
        ∀ i x, iteratedFDeriv ℝ i (fun x ↦ 𝓕 (fun y ↦ a x y ξ (u y)) (c • ξ)) x =
          𝓕 (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ (u y)) x) (c • ξ) := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    let H := E →L[ℂ] F
    let K : Set V := Prod.snd '' tsupport (Function.uncurry a)
    have hK : IsCompact K := hsupp.image continuous_snd
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
    let f (u : 𝓢(V, E)) (x ξ y : V) : F := a x y ξ (u y)
    have hf (u : 𝓢(V, E)) : ContDiff ℝ ∞
        (fun z : (V × V) × V ↦ f u z.1.1 z.2 z.1.2) := by
      let R : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
      exact (R.contDiff.comp ha.1).clm_apply ((u.smooth ⊤).comp contDiff_fst.snd)
    let D (i : ℕ) (x : V) (u : 𝓢(V, E)) (ξ y : V) :=
      iteratedFDeriv ℝ i (fun x ↦ f u x ξ y) x
    have hDs (i : ℕ) (u : 𝓢(V, E)) : ContDiff ℝ ∞
        (fun z : (V × V) × V ↦ D i z.1.1 u z.2 z.1.2) := by
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : V × V ↦ fun x : V ↦ f u x z.2 z.1)) :=
        (hf u).comp ((contDiff_snd.prodMk contDiff_fst.fst).prodMk contDiff_fst.snd)
      exact (parametric _ h i).comp
        ((contDiff_fst.snd.prodMk contDiff_snd).prodMk contDiff_fst.fst)
    have hDsupport (i : ℕ) (x : V) (u : 𝓢(V, E)) (ξ : V) : tsupport (D i x u ξ) ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      have hz (x : V) : a x y ξ = 0 := by
        have hzero : Function.uncurry a (x, y) = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hyK ⟨(x, y), h, rfl⟩)
        exact congrFun hzero ξ
      have hzfun : (fun x ↦ f u x ξ y) = 0 := by funext x; simp [f, hz]
      exact hy (by simp [D, hzfun])
    have hDbound (i j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x u ξ y, y ∈ K →
        ‖iteratedFDeriv ℝ j (D i x u ξ) y‖ ≤ C *
          (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℂ V E) u * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
      let R : H →L[ℝ] E →L[ℝ] F := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
      let B : (V [×i]→L[ℝ] H) →L[ℝ] E →L[ℝ] (V [×i]→L[ℝ] F) :=
        ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ V) H F).comp
          R.flip).flip
      let A (x ξ y : V) := iteratedFDeriv ℝ i (fun x ↦ a x y ξ) x
      have hA (x ξ : V) : ContDiff ℝ ∞ (A x ξ) := by
        have h : ContDiff ℝ ∞ (Function.uncurry (fun y x : V ↦ a x y ξ)) :=
          ha.1.comp ((contDiff_snd.prodMk contDiff_fst).prodMk contDiff_const)
        exact (parametric _ h i).comp (contDiff_id.prodMk contDiff_const)
      have heq (x ξ y : V) (u : 𝓢(V, E)) : D i x u ξ y = B (A x ξ y) (u y) := by
        let L : H →L[ℝ] F := R.flip (u y)
        have hs : ContDiff ℝ ∞ (fun x ↦ a x y ξ) :=
          ha.1.comp ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)
        exact L.iteratedFDeriv_comp_left hs.contDiffAt (by simp)
      choose C hC hbound using fun j ↦ hab i j
      let M : ℝ := ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * C l
      have hM : 0 ≤ M := Finset.sum_nonneg (fun l _ ↦ mul_nonneg (by positivity) (hC l))
      refine ⟨‖B‖ * M, by positivity, ?_⟩
      intro x u ξ y hy
      have hEq : D i x u ξ = fun y ↦ B (A x ξ y) (u y) := funext (fun y ↦ heq x ξ y u)
      rw [hEq]
      calc
        _ ≤ ‖B‖ * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (A x ξ) y‖ * ‖iteratedFDeriv ℝ (j - l) u y‖ :=
          B.norm_iteratedFDeriv_le_of_bilinear (hA x ξ) (u.smooth ⊤) y (by simp)
        _ ≤ ‖B‖ * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
            (C l * (1 + ‖ξ‖) ^ ⌈m⌉₊) *
              (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℂ V E) u := by
          apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
          apply Finset.sum_le_sum
          intro l _
          have hlC := hC l
          gcongr
          · exact hbound l x ξ y hy
          · apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ u (j - l) y).trans
            change schwartzSeminormFamily ℂ V E (0, j - l) u ≤ _
            apply Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ V E) ?_) u
            exact Finset.mem_Iic.mpr ⟨le_refl _, Nat.sub_le _ _⟩
        _ = _ := by
          dsimp [M]
          simp only [mul_assoc, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro l _
          ring
    let phase (ξ y : V) : ℂ :=
      Complex.exp (((-2 * Real.pi * inner ℝ y (c • ξ) : ℝ) : ℂ) * Complex.I)
    have hphaseNorm (ξ y : V) : ‖phase ξ y‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re]
    have hphase (ξ : V) : Continuous (phase ξ) := by dsimp [phase]; fun_prop
    let G (u : 𝓢(V, E)) (x ξ : V) := ∫ y, phase ξ y • f u x ξ y
    have hkernel (i : ℕ) (u : 𝓢(V, E)) (x ξ y : V) :
        iteratedFDeriv ℝ i (fun x ↦ phase ξ y • f u x ξ y) x = phase ξ y • D i x u ξ y := by
      apply iteratedFDeriv_const_smul_apply'
      exact ((hf u).comp
        ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)).contDiffAt.of_le (by simp)
    have hG (u : 𝓢(V, E)) (ξ : V) : ContDiff ℝ ∞ (fun x ↦ G u x ξ) ∧
        ∀ i x, iteratedFDeriv ℝ i (fun x ↦ G u x ξ) x =
          ∫ y, phase ξ y • D i x u ξ y := by
      have hI := integrate (fun x y ↦ phase ξ y • f u x ξ y)
        (fun y ↦ ((hf u).comp
          ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const)).const_smul (phase ξ y))
      have hmeas (i : ℕ) (x : V) : AEStronglyMeasurable
          (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ phase ξ y • f u x ξ y) x) := by
        simp_rw [hkernel]
        exact ((hphase ξ).smul ((hDs i u).continuous.comp
          ((continuous_const.prodMk continuous_id).prodMk continuous_const))).aestronglyMeasurable
      have hb (i : ℕ) : ∃ b : V → ℝ, Integrable b ∧
          ∀ x y, ‖iteratedFDeriv ℝ i (fun x ↦ phase ξ y • f u x ξ y) x‖ ≤ b y := by
        obtain ⟨C, hC, hbound⟩ := hDbound i 0
        let M := C * (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℂ V E) u * (1 + ‖ξ‖) ^ ⌈m⌉₊
        refine ⟨K.indicator (fun _ ↦ M), ?_, ?_⟩
        · exact (integrable_indicator_iff hK.measurableSet).mpr
            (integrableOn_const (μ := volume) (C := M) hK.measure_lt_top.ne)
        intro x y
        rw [hkernel, norm_smul, hphaseNorm, one_mul]
        by_cases hy : y ∈ K
        · rw [Set.indicator_of_mem hy]
          simpa only [norm_iteratedFDeriv_zero] using hbound x u ξ y hy
        · rw [Set.indicator_of_notMem hy]
          have hz : D i x u ξ y = 0 := image_eq_zero_of_notMem_tsupport
            (fun h ↦ hy (hDsupport i x u ξ h))
          rw [hz, norm_zero]
      obtain ⟨hs, hd⟩ := hI hmeas hb
      refine ⟨hs, ?_⟩
      intro i x
      rw [hd i x]
      apply integral_congr_ae
      filter_upwards with y
      exact hkernel i u x ξ y
    intro u ξ
    simpa only [G, phase, Real.fourier_eq', f, D] using hG u ξ
  have hab := amplitude_bounds m a ha hsupp
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let Kx : Set V := Prod.fst '' tsupport (Function.uncurry a)
  let Ky : Set V := Prod.snd '' tsupport (Function.uncurry a)
  have hKx : IsCompact Kx := hsupp.image continuous_fst
  have hKy : IsCompact Ky := hsupp.image continuous_snd
  have hazero (x y ξ : V) (h : x ∉ Kx ∨ y ∉ Ky) : a x y ξ = 0 := by
    have hz : Function.uncurry a (x, y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxy
      rcases h with hx | hy
      · exact hx ⟨(x, y), hxy, rfl⟩
      · exact hy ⟨(x, y), hxy, rfl⟩
    exact congrFun hz ξ
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let g (u : 𝓢(V, E)) (x ξ : V) := 𝓕 (fun y ↦ a x y ξ (u y)) (c • ξ)
  have hg (u : 𝓢(V, E)) (ξ : V) : ContDiff ℝ ∞ (fun x ↦ g u x ξ) ∧
      ∀ i x, iteratedFDeriv ℝ i (fun x ↦ g u x ξ) x =
        𝓕 (fun y ↦ iteratedFDeriv ℝ i (fun x ↦ a x y ξ (u y)) x) (c • ξ) :=
    inner_smooth m a ha hsupp hab c u ξ
  have hdecay (i k : ℕ) : ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x (u : 𝓢(V, E)) ξ,
      ‖iteratedFDeriv ℝ i (fun x ↦ g u x ξ) x‖ ≤
        C * (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ V E) u *
          (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    obtain ⟨J, C, hC, hb⟩ := partial_fourier_bound m a ha hsupp hab c hc i k
    exact ⟨J, C, hC, fun x u ξ ↦ by rw [(hg u ξ).2 i x]; exact hb x u ξ⟩
  let kernel (u : 𝓢(V, E)) (ξ x y : V) :=
    Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) • a x y ξ (u y)
  let H (u : 𝓢(V, E)) (x ξ : V) := ∫ y, kernel u ξ x y
  let phase (ξ x : V) := Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))
  have hphase (ξ : V) : ContDiff ℝ ∞ (phase ξ) := by
    simpa [phase, Function.comp_def, real_inner_comm, mul_comm] using
      Complex.hasTemperateGrowth_exp_mul_I.1.comp (innerSL ℝ ξ).contDiff
  have hH (u : 𝓢(V, E)) (x ξ : V) : H u x ξ = phase ξ x • g u x ξ := by
    change (∫ y, kernel u ξ x y) = phase ξ x •
      𝓕 (fun y ↦ a x y ξ (u y)) (c • ξ)
    rw [Real.fourier_eq', ← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [kernel, phase, smul_smul]
    congr 1
    rw [← Complex.exp_add, inner_sub_left, inner_smul_right]
    congr 1
    push_cast
    dsimp [c]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  have hHs (u : 𝓢(V, E)) (ξ : V) : ContDiff ℝ ∞ (fun x ↦ H u x ξ) := by
    have heq : (fun x ↦ H u x ξ) = fun x ↦ phase ξ x • g u x ξ := funext (fun x ↦ hH u x ξ)
    rw [heq]
    exact (hphase ξ).smul (hg u ξ).1
  have hHsupport (u : 𝓢(V, E)) (ξ : V) : tsupport (fun x ↦ H u x ξ) ⊆ Kx := by
    apply closure_minimal ?_ hKx.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp [H, kernel, hazero _ _ _ (Or.inl hxK)])
  -- Output phase derivatives have only polynomial frequency growth on the fixed support.
  have phase_bounds {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (k : ℕ) :
      ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ i
          (fun x ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) x‖ ≤ C * (1 + ‖ξ‖) ^ d := by
    let V := EuclideanSpace ℝ (Fin n)
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨d, C, hC, hder⟩ := Complex.hasTemperateGrowth_exp_mul_I.norm_iteratedFDeriv_le_uniform k
    refine ⟨d + k, C * (1 + max R 0) ^ d, by positivity, ?_⟩
    intro i hi x hx ξ
    let L : V →L[ℝ] ℝ := innerSL ℝ ξ
    let e : ℝ → ℂ := fun t ↦ Complex.exp (t * Complex.I)
    have he : ContDiff ℝ ∞ e := Complex.hasTemperateGrowth_exp_mul_I.1
    have hfun : (fun x : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) = e ∘ L := by
      funext x
      simp [e, L, real_inner_comm, mul_comm]
    rw [hfun, L.iteratedFDeriv_comp_right he x (by simp)]
    have hbase : 1 + ‖L x‖ ≤ (1 + max R 0) * (1 + ‖ξ‖) := by
      have hnorm : ‖L x‖ ≤ ‖ξ‖ * max R 0 :=
        (norm_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_left
          ((hR x hx).trans (le_max_left _ _)) (norm_nonneg _))
      nlinarith [norm_nonneg ξ, le_max_right R 0]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i e (L x)‖ * ‖L‖ ^ i := by
        simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ i e (L x)) (fun _ ↦ L)
      _ ≤ (C * (1 + ‖L x‖) ^ d) * ‖L‖ ^ i := by
        gcongr
        exact hder i hi (L x)
      _ ≤ (C * ((1 + max R 0) * (1 + ‖ξ‖)) ^ d) * (1 + ‖ξ‖) ^ k := by
        gcongr
        calc
          ‖L‖ ^ i = ‖ξ‖ ^ i := by rw [innerSL_apply_norm]
          _ ≤ (1 + ‖ξ‖) ^ i := by gcongr; linarith [norm_nonneg ξ]
          _ ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hi
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hHbound (i : ℕ) : ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (u : 𝓢(V, E)) x ξ,
      ‖iteratedFDeriv ℝ i (fun x ↦ H u x ξ) x‖ ≤
        C * (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ V E) u *
          (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ)) := by
    obtain ⟨d, A, hA, hphaseBound⟩ := phase_bounds Kx hKx i
    choose J C hC hbound using fun l ↦ hdecay (i - l) (n + 1 + d)
    let L : ℕ := (Finset.range (i + 1)).sup J
    let B : ℝ := ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * A * C l
    have hB : 0 ≤ B := Finset.sum_nonneg
      (fun l _ ↦ mul_nonneg (mul_nonneg (by positivity) hA) (hC l))
    refine ⟨L, B, hB, ?_⟩
    intro u x ξ
    let P : ℝ := (Finset.Iic (0, L)).sup (schwartzSeminormFamily ℂ V E) u
    have hP : 0 ≤ P := apply_nonneg _ _
    by_cases hx : x ∈ Kx
    · have hfun : (fun x ↦ H u x ξ) = fun x ↦ phase ξ x • g u x ξ :=
        funext (fun x ↦ hH u x ξ)
      rw [hfun]
      calc
        _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l (phase ξ) x‖ *
              ‖iteratedFDeriv ℝ (i - l) (fun x ↦ g u x ξ) x‖ :=
          norm_iteratedFDeriv_smul_le (hphase ξ) (hg u ξ).1 x (by simp)
        _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
            (A * (1 + ‖ξ‖) ^ d) * (C l * P * (1 + ‖ξ‖) ^ (-((n + 1 + d : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum
          intro l hl
          have hCl := hC l
          gcongr
          · exact hphaseBound l (by simpa using hl) x hx ξ
          · apply (hbound l x u ξ).trans
            gcongr
            apply Seminorm.finset_sup_apply_le hP
            intro b hb
            apply Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ V E) ?_) u
            apply Finset.mem_Iic.mpr
            have hb' := Finset.mem_Iic.mp hb
            exact ⟨hb'.1, hb'.2.trans (Finset.le_sup (f := J) hl)⟩
        _ = B * P * (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ)) := by
          dsimp [B]
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          have hp : 0 < 1 + ‖ξ‖ := by positivity
          have he : (1 + ‖ξ‖) ^ d * (1 + ‖ξ‖) ^ (-((n + 1 + d : ℕ) : ℝ)) =
              (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hp]
            congr 1
            push_cast
            ring
          calc
            _ = ((i.choose l : ℝ) * A * C l) * P *
                ((1 + ‖ξ‖) ^ d * (1 + ‖ξ‖) ^ (-((n + 1 + d : ℕ) : ℝ))) := by ring
            _ = _ := by rw [he]
    · have hz : iteratedFDeriv ℝ i (fun x ↦ H u x ξ) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (hHsupport u ξ (tsupport_iteratedFDeriv_subset i h)))
      rw [hz, norm_zero]
      positivity
  -- The actual inner integral supplies measurable frequency derivatives at every order.
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
  have hkernelJoint (u : 𝓢(V, E)) : ContDiff ℝ ∞
      (Function.uncurry (fun z : V × V ↦ fun x ↦ kernel u z.1 x z.2)) := by
    have he : ContDiff ℝ ∞ (fun z : (V × V) × V ↦
        Complex.exp (Complex.I * (inner ℝ (z.2 - z.1.2) z.1.1 : ℂ))) := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.1.comp
          ((contDiff_inner (𝕜 := ℝ)).comp
            ((contDiff_snd.sub contDiff_fst.snd).prodMk contDiff_fst.fst))
    let R : (E →L[ℂ] F) →L[ℝ] E →L[ℝ] F :=
      ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ
    exact he.smul ((R.contDiff.comp (ha.1.comp
      ((contDiff_snd.prodMk contDiff_fst.snd).prodMk contDiff_fst.fst))).clm_apply
        ((u.smooth ⊤).comp contDiff_fst.snd))
  have hHi (u : 𝓢(V, E)) (ξ : V) : ∀ i x,
      iteratedFDeriv ℝ i (fun x ↦ H u x ξ) x =
        ∫ y, iteratedFDeriv ℝ i (fun x ↦ kernel u ξ x y) x := by
    have hks : ContDiff ℝ ∞ (Function.uncurry (kernel u ξ)) :=
      (hkernelJoint u).comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)
    exact (compact_integrate (kernel u ξ) hks Kx Ky hKx hKy
      (fun x y h ↦ by simp [kernel, hazero x y ξ h])).2
  have hHmeas (i : ℕ) (u : 𝓢(V, E)) (x : V) : AEStronglyMeasurable
      (fun ξ ↦ iteratedFDeriv ℝ i (fun x ↦ H u x ξ) x) := by
    simp_rw [hHi]
    have hm : StronglyMeasurable (Function.uncurry
        (fun ξ y ↦ iteratedFDeriv ℝ i (fun x ↦ kernel u ξ x y) x)) :=
      ((parametric _ (hkernelJoint u) i).continuous.comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : V × V ↦ x))))
        |>.stronglyMeasurable
    exact hm.integral_prod_right.aestronglyMeasurable
  have hIntegral (u : 𝓢(V, E)) : ContDiff ℝ ∞ (fun x ↦ ∫ ξ, H u x ξ) ∧
      ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ ξ, H u x ξ) x =
        ∫ ξ, iteratedFDeriv ℝ i (fun x ↦ H u x ξ) x := by
    apply integrate (H u) (hHs u) (fun i x ↦ hHmeas i u x)
    intro i
    obtain ⟨J, C, _, hb⟩ := hHbound i
    have hi : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by simp [V])
    exact ⟨_, hi.const_mul (C * (Finset.Iic (0, J)).sup
      (schwartzSeminormFamily ℂ V E) u), hb u⟩
  let c₀ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hsmooth (u : 𝓢(V, E)) : ContDiff ℝ ∞ (amplitudeApply a u) :=
    (hIntegral u).1.const_smul c₀
  have houtputSupport (u : 𝓢(V, E)) : tsupport (amplitudeApply a u) ⊆ Kx := by
    apply closure_minimal ?_ hKx.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp [amplitudeApply, hazero _ _ _ (Or.inl hxK)])
  have houtputBound (ki : ℕ × ℕ) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (u : 𝓢(V, E)) (x : V), ‖x‖ ^ ki.1 *
        ‖iteratedFDeriv ℝ ki.2 (amplitudeApply a u) x‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ V E) u := by
    obtain ⟨J, C, hC, hb⟩ := hHbound ki.2
    obtain ⟨R, hR⟩ := hKx.isBounded.exists_norm_le
    let w (ξ : V) : ℝ := (1 + ‖ξ‖) ^ (-((n + 1 : ℕ) : ℝ))
    have hw : Integrable w := integrable_one_add_norm (by simp [V])
    have hw₀ : 0 ≤ ∫ ξ, w ξ := integral_nonneg (fun _ ↦ Real.rpow_nonneg (by positivity) _)
    refine ⟨Finset.Iic (0, J), (max R 0) ^ ki.1 * ‖c₀‖ * C * (∫ ξ, w ξ),
      by positivity, ?_⟩
    intro u x
    by_cases hx : x ∈ Kx
    · have hd : iteratedFDeriv ℝ ki.2 (amplitudeApply a u) x =
          c₀ • (∫ ξ, iteratedFDeriv ℝ ki.2 (fun x ↦ H u x ξ) x) := by
        change iteratedFDeriv ℝ ki.2 (fun x ↦ c₀ • ∫ ξ, H u x ξ) x = _
        rw [iteratedFDeriv_const_smul_apply' ((hIntegral u).1.contDiffAt.of_le (by simp)),
          (hIntegral u).2 ki.2 x]
      have hi : ‖∫ ξ, iteratedFDeriv ℝ ki.2 (fun x ↦ H u x ξ) x‖ ≤
          C * (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ V E) u * (∫ ξ, w ξ) := by
        calc
          _ ≤ ∫ ξ, C * (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ V E) u * w ξ :=
            norm_integral_le_of_norm_le (hw.const_mul _) (Filter.Eventually.of_forall (hb u x))
          _ = _ := integral_const_mul _ _
      rw [hd, norm_smul]
      calc
        _ ≤ (max R 0) ^ ki.1 * (‖c₀‖ *
            (C * (Finset.Iic (0, J)).sup (schwartzSeminormFamily ℂ V E) u * (∫ ξ, w ξ))) := by
          gcongr
          exact (hR x hx).trans (le_max_left _ _)
        _ = _ := by ring
    · have hz : iteratedFDeriv ℝ ki.2 (amplitudeApply a u) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (houtputSupport u (tsupport_iteratedFDeriv_subset ki.2 h)))
      rw [hz, norm_zero, mul_zero]
      positivity
  -- Both integrations preserve the same complex-linear input; the estimates give continuity.
  have hadd (u v : 𝓢(V, E)) (x : V) :
      amplitudeApply a (u + v) x = amplitudeApply a u x + amplitudeApply a v x := by
    unfold amplitudeApply
    simp only [add_apply, map_add, smul_add]
    simp_rw [integral_add (integrable_amplitudeApply_inner m a ha hsupp u x _)
      (integrable_amplitudeApply_inner m a ha hsupp v x _)]
    rw [integral_add (integrable_amplitudeApply_outer m a ha hsupp u x)
      (integrable_amplitudeApply_outer m a ha hsupp v x), smul_add]
  have hsmul (z : ℂ) (u : 𝓢(V, E)) (x : V) :
      amplitudeApply a (z • u) x = z • amplitudeApply a u x := by
    unfold amplitudeApply
    simp only [smul_apply, map_smul, smul_comm _ z, integral_smul]
  let T : 𝓢(V, E) →L[ℂ] 𝓢(V, F) :=
    SchwartzMap.mkCLM (𝕜 := ℂ) (σ := RingHom.id ℂ) (amplitudeApply a)
      hadd hsmul hsmooth houtputBound
  refine ⟨T, fun _ _ ↦ rfl, ?_⟩
  intro S hS
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  exact hS u x

/-- The uniquely specified Schwartz operator acts by the actual amplitude integral. -/
def amplitudeOperator (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a)) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
  (existsUnique_amplitudeOperator m a ha hsupp).exists.choose

/-- The Schwartz operator retains the pointwise integral specification. -/
theorem amplitudeOperator_apply (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    amplitudeOperator m a ha hsupp u x = amplitudeApply a u x := by
  /- Apply the existence theorem's pointwise specification to the chosen operator. -/
  exact (existsUnique_amplitudeOperator m a ha hsupp).exists.choose_spec u x

/-- SG Observation 3.6: vanishing near the diagonal gives a symbol of every order. -/
theorem isSmoothingSymbol_amplitudeSymbol_of_off_diagonal
    (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (V : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hV : IsOpen V) (hdiag : ∀ x, (x, x) ∈ V)
    (hzero : ∀ z ∈ V, ∀ ξ, a z.1 z.2 ξ = 0) :
    IsSmoothingSymbol Set.univ (amplitudeSymbol a) := by
  /- Vanishing on an open neighborhood of the diagonal makes every mixed y,ξ derivative
  vanish there, so all expansion coefficients are zero. The remainder statement places
  the reduced symbol in S^(m-N) for every natural N. These orders are cofinal toward
  negative infinity; monotonicity of symbol order gives every real order. -/
  have hterms (j : ℕ) : amplitudeExpansionTerm a j = 0 := by
    funext x ξ
    have hy (η : EuclideanSpace ℝ (Fin n)) :
        iteratedFDeriv ℝ j (fun y ↦ a x y η) x = 0 := by
      have hnear : (fun y ↦ a x y η) =ᶠ[nhds x] 0 := by
        have hmem : {y | (x, y) ∈ V} ∈ nhds x :=
          (hV.preimage (continuous_const.prodMk continuous_id)).mem_nhds (hdiag x)
        filter_upwards [hmem] with y hy
        exact hzero (x, y) hy η
      simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
        (hnear.iteratedFDeriv ℝ j).eq_of_nhds
    simp [amplitudeExpansionTerm, hy]
  -- The integer remainder orders are cofinal below every prescribed real order.
  intro l
  obtain ⟨N, hN⟩ := exists_nat_gt (m - l)
  have h := hasSymbolExpansion_amplitudeSymbol m a ha hsupp N
  simp only [hterms, Finset.sum_const_zero, sub_zero] at h
  exact h.mono (by linarith)

/-- The off-diagonal amplitude operator improves arbitrary real Sobolev orders. -/
theorem exists_amplitude_sobolev_extension_of_off_diagonal
    (m : ℝ) (a : AmplitudeFunction n r q)
    (ha : IsAmplitude m a) (hsupp : HasCompactSupport (Function.uncurry a))
    (V : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hV : IsOpen V) (hdiag : ∀ x, (x, x) ∈ V)
    (hzero : ∀ z ∈ V, ∀ ξ, a z.1 z.2 ξ = 0) (s t : ℝ) :
    ∃ T : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n q t (T (schwartzSobolevCoordinate s u)) φ =
            ∫ x, φ x • amplitudeApply a u x := by
  /- The preceding observation puts the reduced symbol in S^(s-t). Its spatial support
  is compact. Apply the existing compactly supported quantization estimate to obtain
  H^s to H^t boundedness in the actual Bessel coordinates. The exact reduction identity
  replaces quantization by the original amplitude integral in the test-function equation.
  Neither s nor t is constrained relative to the other. -/
  have hsymbol : IsSymbol Set.univ (s - t) (amplitudeSymbol a) :=
    isSmoothingSymbol_amplitudeSymbol_of_off_diagonal m a ha hsupp V hV hdiag hzero (s - t)
  have hcompact : HasCompactSupport (amplitudeSymbol a) :=
    hasCompactSupport_amplitudeSymbol a hsupp
  -- The same reduced symbol has every order, so choose exactly the desired Sobolev gain.
  obtain ⟨T, hT⟩ := exists_quantize_sobolev_extension (s - t) s (amplitudeSymbol a) hsymbol
    (tsupport (amplitudeSymbol a)) hcompact
    (fun x hx ξ ↦ congrFun (image_eq_zero_of_notMem_tsupport hx) ξ)
  have horder : s - (s - t) = t := by ring
  simp only [horder] at hT
  refine ⟨T, ?_⟩
  intro u φ
  -- Exact reduction identifies the original iterated amplitude integral, including its constants.
  rw [hT, quantize_amplitudeSymbol m a ha hsupp u]

end AtiyahSinger
