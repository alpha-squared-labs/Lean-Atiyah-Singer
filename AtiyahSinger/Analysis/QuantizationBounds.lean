/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.SymbolTopology

import all AtiyahSinger.Analysis.Quantization
import all AtiyahSinger.Analysis.SchurKernel
import all AtiyahSinger.Analysis.SymbolFourier
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform Sobolev estimates for compact quantization

Public module ID: M0908.

The Fourier proof of SG III.3.2 uses finitely many spatial symbol derivatives.
Here its constants are chosen before the symbol. The resulting estimate is used
by fixed finite bundle quantizers to prove operator-norm continuity in the original
symbol seminorm topology. All Fourier and Bessel normalizations are unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter FourierTransform MeasureTheory
open scoped ContDiff NNReal SchwartzMap Topology

set_option maxSynthPendingDepth 20

variable {n r q : ℕ}

/-- An explicit integrable Fourier-kernel majorant bounds the original Sobolev action. -/
theorem quantize_sobolev_norm_le_of_fourier_bound (m s : ℝ) (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ m a) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hdi : Integrable d) (hde : ∀ x, d (-x) = d x)
    (hbound : ∀ ξ η,
      ‖((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) •
        𝓕 (fun x ↦ a x ((2 * Real.pi) • η)) (ξ - η)‖ ≤ d (ξ - η))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hv : ∀ x, v x = quantize a u x) :
    ‖schwartzSobolevCoordinate (s - m) v‖ ≤
      (∫ x, d x) * ‖schwartzSobolevCoordinate s u‖ := by
  let X := EuclideanSpace ℝ (Fin n)
  let U := EuclideanSpace ℂ (Fin r)
  let V := EuclideanSpace ℂ (Fin q)
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
  -- The supplied bound concerns the measurable kernel of this very quantization.
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  have hBm : StronglyMeasurable B := by
    have hac : Continuous (fun t : (X × X) × X ↦ a t.2 ((2 * Real.pi) • t.1.2)) :=
      hsmooth.continuous.comp (continuous_snd.prodMk
        ((continuous_snd.comp continuous_fst).const_smul (2 * Real.pi)))
    have hh : Continuous (fun t : (X × X) × X ↦
        Complex.exp ((↑(-2 * Real.pi * inner ℝ t.2 (t.1.1 - t.1.2))) * Complex.I) •
          a t.2 ((2 * Real.pi) • t.1.2)) := by fun_prop
    simpa only [B, Real.fourier_eq'] using hh.stronglyMeasurable.integral_prod_right'
  have hHm : StronglyMeasurable (Function.uncurry H) := by
    have hc : Continuous (fun z : X × X ↦ w (s - m) z.1 * w (-s) z.2) :=
      ((hw (s - m)).1.continuous.comp continuous_fst).mul
        ((hw (-s)).1.continuous.comp continuous_snd)
    exact hc.stronglyMeasurable.smul hBm
  -- Opposite Bessel weights cancel in the weak pairing before applying Schur's bound.
  have hpair (z : 𝓢(X, V)) :
      ‖inner ℂ (schwartzSobolevCoordinate (s - m) v)
        (schwartzSobolevCoordinate (-(s - m)) z)‖ ≤
      (∫ x, d x) * ‖schwartzSobolevCoordinate s u‖ *
        ‖schwartzSobolevCoordinate (-(s - m)) z‖ := by
    let f : 𝓢(X, U) := SchwartzMap.smulLeftCLM U (w s) (𝓕 u)
    let g : 𝓢(X, V) := SchwartzMap.smulLeftCLM V (w (-(s - m))) (𝓕 z)
    have hnorm (t : ℝ) (k : ℕ) (f : 𝓢(X, EuclideanSpace ℂ (Fin k))) :
        ‖(SchwartzMap.smulLeftCLM _ (w t) (𝓕 f)).toLp 2 volume‖ =
          ‖schwartzSobolevCoordinate t f‖ := by
      rw [← Lp.norm_fourier_eq (f := schwartzSobolevCoordinate t f)]
      congr 1
      rw [schwartzSobolevCoordinate, SchwartzMap.toLp_fourier_eq]
      congr 1
      simp only [SchwartzMap.fourierMultiplierCLM_apply,
        FourierTransform.fourier_fourierInv_eq]
      rfl
    have hschur := (schur_pairing_estimate H hHm d hd hd0 hdi hde hbound f g).2
    have hcancel :
        (∫ z : X × X, inner ℂ (H z.1 z.2 (f z.2)) (g z.1)) =
          ∫ x, inner ℂ (quantize a u x) (z x) := by
      rw [quantize_fourier_weak m a ha K hK hsupp u z]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [H, f, g, SchwartzMap.smulLeftCLM_apply_apply (hw s),
        SchwartzMap.smulLeftCLM_apply_apply (hw (-(s - m))),
        smul_apply, ContinuousLinearMap.map_smul_of_tower,
        inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul]
      have hwcancel : w (-(s - m)) z.1 * (w (s - m) z.1 * w (-s) z.2 * w s z.2) = 1 := by
        calc
          _ = (w (s - m) z.1 * w (-(s - m)) z.1) * (w s z.2 * w (-s) z.2) := by ring
          _ = 1 := by rw [hweights, hweights, mul_one]
      rw [hwcancel, one_smul]
    rw [hcancel] at hschur
    change _ ≤ (∫ x, d x) * ‖(SchwartzMap.smulLeftCLM U (w s) (𝓕 u)).toLp 2 volume‖ *
      ‖(SchwartzMap.smulLeftCLM V (w (-(s - m))) (𝓕 z)).toLp 2 volume‖ at hschur
    rw [hnorm, hnorm] at hschur
    simpa only [sobolev_pairing_schwartz, hv] using hschur
  -- Dense Schwartz test coordinates detect the Hilbert norm of the original output.
  let y := schwartzSobolevCoordinate (s - m) v
  let c := (∫ x, d x) * ‖schwartzSobolevCoordinate s u‖
  have hc : 0 ≤ c := mul_nonneg (integral_nonneg hd0) (norm_nonneg _)
  have hall (z : Lp V 2 (volume : Measure X)) : ‖inner ℂ y z‖ ≤ c * ‖z‖ := by
    exact (denseRange_schwartzSobolevCoordinate n q (-(s - m))).induction_on z
      (isClosed_le (continuous_const.inner continuous_id).norm
        (continuous_const.mul continuous_norm)) hpair
  have hself := hall y
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hself
  by_cases hy : ‖y‖ = 0
  · change ‖y‖ ≤ c
    simpa only [hy] using hc
  · have hypos := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
    change ‖y‖ ≤ c
    nlinarith

/-- A fixed compact spatial cutoff has a uniform finite-seminorm Sobolev quantization bound. -/
theorem exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (m s : ℝ)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    ∃ (J : Finset (SymbolSeminormIndex U)) (c : ℝ≥0),
      ∀ p : symbolSpace U hU m r q,
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate (s - m)
          (quantizeSchwartz m (zeroExtendedSymbol U χ p.val)
            (isSymbol_zeroExtendedSymbol U hU m χ hχ hc hs p.val p.property)
            (hasCompactSupport_zeroExtendedSymbol U χ p.val hc) u)‖ ≤
          (c : ℝ) * (J.sup (symbolSeminorm hU m)) p *
            ‖schwartzSobolevCoordinate s u‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let a (p : symbolSpace U hU m r q) : SymbolFunction n r q := zeroExtendedSymbol U χ p.val
  have ha (p : symbolSpace U hU m r q) : IsSymbol Set.univ m (a p) :=
    isSymbol_zeroExtendedSymbol U hU m χ hχ hc hs p.val p.property
  have hasupp (p : symbolSpace U hU m r q) (x : X) (hx : x ∉ tsupport χ) (η : X) :
      a p x η = 0 := by
    simp [a, zeroExtendedSymbol, image_eq_zero_of_notMem_tsupport hx]
  -- Fourier continuity selects finitely many spatial derivatives before the symbol is chosen.
  have hFourier (N : ℕ) : ∃ (J : Finset (SymbolSeminormIndex U)) (c : ℝ), 0 ≤ c ∧
      ∀ (p : symbolSpace U hU m r q) (η ζ : X),
        ‖𝓕 (fun x ↦ a p x η) ζ‖ ≤ c * (J.sup (symbolSeminorm hU m)) p *
          (1 + ‖η‖) ^ m * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
    let T : 𝓢(X, V) →L[ℂ] 𝓢(X, V) := FourierTransform.fourierCLM ℂ _
    let qFourier : Seminorm ℂ 𝓢(X, V) :=
      (Finset.Iic (N, 0)).sup (fun i ↦ SchwartzMap.seminorm ℂ i.1 i.2)
    have hq : Continuous qFourier :=
      Seminorm.continuous_finsetSup (fun i _ ↦
        (schwartz_withSeminorms ℂ X V).continuous_seminorm i)
    obtain ⟨L, A, hA0, hA⟩ := Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℂ X V) (qFourier.comp T.toLinearMap) (hq.comp T.continuous)
    let d : ℕ := L.sup Prod.snd
    let index (i : ℕ) : SymbolSeminormIndex U :=
      ⟨tsupport χ, hs, hc, i, 0⟩
    let J : Finset (SymbolSeminormIndex U) := (Finset.range (d + 1)).image index
    let b (p : symbolSpace U hU m r q) : ℝ := (J.sup (symbolSeminorm hU m)) p
    have hb0 (p : symbolSpace U hU m r q) : 0 ≤ b p := apply_nonneg _ p
    have hχc : ContDiff ℝ ∞ (fun x ↦ (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
    have hχbound (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport χ,
        ‖iteratedFDeriv ℝ i (fun y ↦ (χ y : ℂ)) x‖ ≤ B := by
      obtain ⟨B, hB⟩ := (hc.image (hχc.continuous_iteratedFDeriv (by simp)).norm).bddAbove
      exact ⟨max B 0, le_max_right _ _, fun x hx ↦
        (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
    choose B hB hBbound using hχbound
    let C (i : ℕ) : ℝ := ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * B k
    have hC (i : ℕ) : 0 ≤ C i :=
      Finset.sum_nonneg (fun k _ ↦ mul_nonneg (Nat.cast_nonneg _) (hB k))
    have hpbound (p : symbolSpace U hU m r q) (i : ℕ) (hi : i ≤ d)
        (x : X) (hx : x ∈ tsupport χ) (η : X) :
        ‖iteratedFDeriv ℝ i (fun y ↦ p.val y η) x‖ ≤ b p * (1 + ‖η‖) ^ m := by
      have h := symbolDerivative_norm_le_seminorm hU m (index i) p x hx η
      have heq : (fun y ↦ iteratedFDeriv ℝ 0 (p.val y) η) =
          (continuousMultilinearCurryFin0 ℝ X V).symm ∘ (fun y ↦ p.val y η) := by
        funext y
        exact congrFun iteratedFDeriv_zero_eq_comp η
      have hiJ : index i ∈ J := Finset.mem_image.mpr
        ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
      have hsup : symbolSeminorm hU m (index i) p ≤ b p :=
        Seminorm.le_finset_sup_apply hiJ
      apply (show ‖iteratedFDeriv ℝ i (fun y ↦ p.val y η) x‖ ≤
          symbolSeminorm hU m (index i) p * (1 + ‖η‖) ^ m from ?_).trans
        (mul_le_mul_of_nonneg_right hsup (by positivity))
      simpa only [symbolDerivative, index, heq,
        LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.cast_zero, sub_zero] using h
    -- Leibniz's rule retains the same compact set, with constants depending only on χ.
    have hderiv (p : symbolSpace U hU m r q) (i : ℕ) (hi : i ≤ d)
        (η x : X) (hx : x ∈ tsupport χ) :
        ‖iteratedFDeriv ℝ i (fun y ↦ a p y η) x‖ ≤
          C i * b p * (1 + ‖η‖) ^ m := by
      have hslice : ContDiffOn ℝ ∞ (fun y ↦ p.val y η) U := by
        exact p.property.1.comp (contDiffOn_id.prodMk contDiffOn_const)
          (fun y hy ↦ ⟨hy, Set.mem_univ η⟩)
      have heq : (fun y ↦ a p y η) =ᶠ[𝓝 x] (fun y ↦ (χ y : ℂ) • p.val y η) := by
        filter_upwards [hU.mem_nhds (hs hx)] with y hy
        exact zeroExtendedSymbol_apply_of_mem U χ p.val y η hy
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      have hle := norm_iteratedFDerivWithin_smul_le hχc.contDiffOn hslice
        hU.uniqueDiffOn (hs hx) (n := i) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU (hs hx)] at hle
      apply hle.trans
      simp only [C, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      have hp := hpbound p (i - k) ((Nat.sub_le i k).trans hi) x hx η
      calc
        _ ≤ (i.choose k : ℝ) * B k * (b p * (1 + ‖η‖) ^ m) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hBbound k x hx) (Nat.cast_nonneg _)) hp
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB k))
        _ = _ := by ring
    obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
    let D (j i : ℕ) : ℝ := (max R 0) ^ j * C i
    have hD (j i : ℕ) : 0 ≤ D j i := mul_nonneg (by positivity) (hC i)
    let E : ℝ := ∑ i ∈ L, D i.1 i.2
    have hE : 0 ≤ E := Finset.sum_nonneg (fun i _ ↦ hD i.1 i.2)
    refine ⟨J, 2 ^ N * A * E, by positivity, ?_⟩
    intro p η ζ
    have hsmooth : ContDiff ℝ ∞ (Function.uncurry (a p)) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using (ha p).1
    have hsub : tsupport (fun x ↦ a p x η) ⊆ tsupport χ := by
      apply closure_minimal _ (isClosed_tsupport χ)
      intro x hx
      by_contra hout
      exact hx (hasupp p x hout η)
    have hsupp : HasCompactSupport (fun x ↦ a p x η) :=
      hc.of_isClosed_subset (isClosed_tsupport _) hsub
    let S : 𝓢(X, V) :=
      hsupp.toSchwartzMap (hsmooth.comp (contDiff_id.prodMk contDiff_const))
    have hseminorm (j i : ℕ) (hi : i ≤ d) :
        SchwartzMap.seminorm ℂ j i S ≤ D j i * b p * (1 + ‖η‖) ^ m := by
      apply SchwartzMap.seminorm_le_bound ℂ j i S
        (mul_nonneg (mul_nonneg (hD j i) (hb0 p)) (by positivity))
      intro x
      change ‖x‖ ^ j * ‖iteratedFDeriv ℝ i (fun x ↦ a p x η) x‖ ≤ _
      by_cases hx : x ∈ tsupport χ
      · calc
          _ ≤ (max R 0) ^ j * (C i * b p * (1 + ‖η‖) ^ m) := by
            gcongr
            · exact (hR x hx).trans (le_max_left R 0)
            · exact hderiv p i hi η x hx
          _ = _ := by ring
      · have hz : iteratedFDeriv ℝ i (fun x ↦ a p x η) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun h ↦ hx (hsub (tsupport_iteratedFDeriv_subset i h)))
        rw [hz, norm_zero, mul_zero]
        exact mul_nonneg (mul_nonneg (hD j i) (hb0 p)) (by positivity)
    have hsum : L.sup (schwartzSeminormFamily ℂ X V) S ≤
        E * b p * (1 + ‖η‖) ^ m := by
      apply Seminorm.finset_sup_apply_le
      · exact mul_nonneg (mul_nonneg hE (hb0 p)) (by positivity)
      · intro i hi
        exact (hseminorm i.1 i.2 (Finset.le_sup hi)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun j _ ↦ hD j.1 j.2) hi) (hb0 p)) (by positivity))
    have hweight : (1 + ‖ζ‖) ^ N * ‖T S ζ‖ ≤
        (2 ^ N * A * E) * b p * (1 + ‖η‖) ^ m := by
      calc
        _ ≤ 2 ^ N * qFourier (T S) := by
          simpa only [qFourier, schwartzSeminormFamily, iteratedFDeriv_zero_eq_comp,
            Function.comp_apply, LinearIsometryEquiv.norm_map] using
            SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
              (m := (N, 0)) (le_refl _) (le_refl _) (T S) ζ
        _ ≤ 2 ^ N * (A * (L.sup (schwartzSeminormFamily ℂ X V) S)) :=
          mul_le_mul_of_nonneg_left (hA S) (by positivity)
        _ ≤ 2 ^ N * (A * (E * b p * (1 + ‖η‖) ^ m)) := by gcongr
        _ = _ := by ring
    have hFourier : T S ζ = 𝓕 (fun x ↦ a p x η) ζ := rfl
    rw [hFourier] at hweight
    have hpos : 0 < 1 + ‖ζ‖ := by positivity
    calc
      _ ≤ ((2 ^ N * A * E) * b p * (1 + ‖η‖) ^ m) / (1 + ‖ζ‖) ^ N :=
        (le_div_iff₀ (pow_pos hpos N)).mpr (by simpa only [mul_comm] using hweight)
      _ = _ := by rw [Real.rpow_neg hpos.le, Real.rpow_natCast]; rfl
  -- Peetre's inequality converts this finite derivative estimate into one fixed Schur majorant.
  let t : ℝ := (s - m) / 2
  let N : ℕ := ⌈2 * |t|⌉₊ + n + 1
  obtain ⟨J, C, hC, hdecay⟩ := hFourier N
  let D : ℝ := max ((2 * (2 * Real.pi) ^ 2) ^ (m / 2)) 1
  have hD : 0 ≤ D := zero_le_one.trans (le_max_right _ _)
  let E : ℝ := C * D * (2 : ℝ) ^ |t|
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let w : X → ℝ := fun z ↦ (1 + ‖z‖) ^ (-(n : ℝ) - 1)
  have hw : Continuous w := by
    apply Continuous.rpow_const (continuous_const.add continuous_norm)
    intro x
    left
    exact ne_of_gt (show 0 < 1 + ‖x‖ from by positivity)
  have hwi : Integrable w := by
    have hd : (Module.finrank ℝ X : ℝ) < (n : ℝ) + 1 := by simp [X]
    simpa only [w, neg_add, sub_eq_add_neg] using
      (integrable_one_add_norm (E := X) (μ := volume) hd)
  have hw0 (x : X) : 0 ≤ w x := by dsimp [w]; positivity
  refine ⟨J, ⟨E * ∫ x, w x, mul_nonneg hE (integral_nonneg hw0)⟩, ?_⟩
  intro p u
  let b : ℝ := (J.sup (symbolSeminorm hU m)) p
  have hb : 0 ≤ b := apply_nonneg _ p
  let d : X → ℝ := fun z ↦ E * b * w z
  have hbound (ξ η : X) :
      ‖((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) •
        𝓕 (fun x ↦ a p x ((2 * Real.pi) • η)) (ξ - η)‖ ≤ d (ξ - η) := by
    have hshift := bessel_weight_shift t η (ξ - η)
    rw [add_sub_cancel] at hshift
    have hspatial := spatial_weight_le_bessel m η
    have hη : (1 + ‖η‖ ^ 2) ^ t * (1 + ‖η‖ ^ 2) ^ (m / 2) *
        (1 + ‖η‖ ^ 2) ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
      have he : t + m / 2 + -s / 2 = 0 := by dsimp [t]; ring
      rw [he, Real.rpow_zero]
    have hpower : (1 + ‖ξ - η‖ ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(N : ℝ)) ≤
        (1 + ‖ξ - η‖) ^ (-(n : ℝ) - 1) := by
      calc
        _ ≤ ((1 + ‖ξ - η‖) ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(N : ℝ)) := by
          gcongr
          nlinarith [norm_nonneg (ξ - η)]
        _ = (1 + ‖ξ - η‖) ^ (2 * |t| - (N : ℝ)) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
            ← Real.rpow_add (by positivity)]
          rfl
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by have := norm_nonneg (ξ - η); linarith)
          (by dsimp [N]; push_cast; linarith [Nat.le_ceil (2 * |t|)])
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ ((1 + ‖ξ‖ ^ 2) ^ t * (1 + ‖η‖ ^ 2) ^ (-s / 2)) *
          (C * b * (1 + ‖(2 * Real.pi) • η‖) ^ m * (1 + ‖ξ - η‖) ^ (-(N : ℝ))) := by
        gcongr
        exact hdecay p _ _
      _ ≤ ((2 ^ |t| * (1 + ‖η‖ ^ 2) ^ t * (1 + ‖ξ - η‖ ^ 2) ^ |t|) *
          (1 + ‖η‖ ^ 2) ^ (-s / 2)) *
          (C * b * (D * (1 + ‖η‖ ^ 2) ^ (m / 2)) * (1 + ‖ξ - η‖) ^ (-(N : ℝ))) := by
        gcongr
      _ = E * b * ((1 + ‖ξ - η‖ ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(N : ℝ))) := by
        dsimp [E]
        calc
          _ = (C * D * 2 ^ |t|) * b *
              ((1 + ‖ξ - η‖ ^ 2) ^ |t| * (1 + ‖ξ - η‖) ^ (-(N : ℝ))) *
              ((1 + ‖η‖ ^ 2) ^ t * (1 + ‖η‖ ^ 2) ^ (m / 2) *
                (1 + ‖η‖ ^ 2) ^ (-s / 2)) := by ring
          _ = _ := by rw [hη, mul_one]
      _ ≤ d (ξ - η) := mul_le_mul_of_nonneg_left hpower (mul_nonneg hE hb)
  -- Apply the bound to the original Schwartz output, retaining the exact cutoff and quantizer.
  have h := quantize_sobolev_norm_le_of_fourier_bound m s (a p) (ha p) (tsupport χ) hc
    (hasupp p) d (hw.const_mul _) (fun x ↦ mul_nonneg (mul_nonneg hE hb) (hw0 x))
    (hwi.const_mul _) (fun x ↦ by simp only [d, w, norm_neg]) hbound u
    (quantizeSchwartz m (a p) (ha p) (hasCompactSupport_zeroExtendedSymbol U χ p.val hc) u)
    (quantizeSchwartz_apply m (a p) (ha p)
      (hasCompactSupport_zeroExtendedSymbol U χ p.val hc) u)
  have hdint : (∫ x, d x) = (E * ∫ x, w x) * b := by
    rw [show d = fun x ↦ (E * b) * w x from rfl, integral_const_mul]
    ring
  rw [hdint] at h
  exact h

end AtiyahSinger
