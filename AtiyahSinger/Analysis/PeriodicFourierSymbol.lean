/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousCutoff
public import AtiyahSinger.Analysis.PeriodicFourierLocalSymbol

import all AtiyahSinger.Analysis.CompactLocalSymbolCalculus

/-!
# The local circle projection symbol modulo a Schwartz remainder

Public module ID: M0855.

The exact lattice symbol differs from the smooth positive-frequency cutoff
times its original spatial principal coefficient by a joint Schwartz function.
This packages all mixed estimates for the local PDO realization of ASI I,
section 8, p.525. The period-one Fourier convention is retained explicitly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap Topology

open FourierTransform

/-- The actual local positive Fourier symbol has a joint Schwartz principal remainder. -/
theorem exists_schwartz_periodicProjectionRemainder (ψ φ : 𝓢(ℝ, ℂ))
    (hψ : HasCompactSupport (ψ : ℝ → ℂ))
    (hsep : ∀ (x : ℝ) (n : ℤ), n ≠ 0 → ψ x * φ (x + (n : ℝ)) = 0)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ t : ℝ, t ≤ 0 → χ t = 0) (hχone : ∀ t : ℝ, 1 ≤ t → χ t = 1) :
    ∃ r : 𝓢(ℝ × ℝ, ℂ), ∀ z : ℝ × ℝ,
      r z = periodicProjectionSymbol ψ φ z.1 z.2 -
        (χ z.2 : ℂ) * (ψ z.1 * φ z.1) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let p := periodicProjectionSymbol ψ φ
  let b (z : ℝ × ℝ) := p z.1 z.2 - (χ z.2 : ℂ) * (ψ z.1 * φ z.1)
  obtain ⟨hp, hest⟩ := periodicProjectionSymbol_estimates ψ φ hsep
  have hb : ContDiff ℝ ∞ b :=
    hp.sub ((Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd)).mul
      (((ψ.smooth ⊤).comp contDiff_fst).mul ((φ.smooth ⊤).comp contDiff_fst)))
  -- Every remainder jet is supported in the same compact spatial window.
  have hbSupp : tsupport b ⊆ Prod.fst ⁻¹' tsupport ψ := by
    apply closure_minimal _ ((isClosed_tsupport ψ).preimage continuous_fst)
    intro z hz
    by_contra hx
    have hψz : ψ z.1 = 0 := image_eq_zero_of_notMem_tsupport hx
    apply hz
    simp only [b, p, periodicProjectionSymbol, hψz, zero_mul, tsum_zero,
      mul_zero, sub_zero]
  obtain ⟨R, hR⟩ := hψ.isBounded.exists_norm_le
  let K : Set (ℝ × ℝ) := tsupport ψ ×ˢ Set.Icc 0 1
  have hK : IsCompact K := hψ.prod isCompact_Icc
  refine ⟨⟨b, hb, ?_⟩, fun _ ↦ rfl⟩
  intro N k
  obtain ⟨C, hC, hdec⟩ := hest k N
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn
    ((continuous_norm.pow N).mul
      (hb.continuous_iteratedFDeriv (by simp)).norm).continuousOn
  let A : ℝ := (1 + max R 0) ^ N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨|C₀| + A * C, ?_⟩
  intro z
  by_cases hx : z.1 ∈ tsupport ψ
  · by_cases hmid : z.2 ∈ Set.Icc (0 : ℝ) 1
    · have h := hC₀ z ⟨hx, hmid⟩
      change ‖‖z‖ ^ N * ‖iteratedFDeriv ℝ k b z‖‖ ≤ C₀ at h
      rw [Real.norm_of_nonneg (by positivity)] at h
      exact (h.trans (le_abs_self C₀)).trans (le_add_of_nonneg_right (mul_nonneg hA hC))
    · -- Outside the transition strip, the remainder is exactly one of the proven tails.
      have hd : (1 + |z.2|) ^ N * ‖iteratedFDeriv ℝ k b z‖ ≤ C := by
        by_cases hz : z.2 < 0
        · have hnear : b =ᶠ[𝓝 z] Function.uncurry p := by
            filter_upwards [continuous_snd.continuousAt (Iio_mem_nhds hz)] with w hw
            simp only [b, hχzero w.2 hw.le, Complex.ofReal_zero,
              zero_mul, sub_zero, Function.uncurry]
          rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
          exact (hdec z).1 hz.le
        · have hz' : 1 < z.2 := by
            have hz₀ : 0 ≤ z.2 := le_of_not_gt hz
            exact lt_of_not_ge (fun hle ↦ hmid ⟨hz₀, hle⟩)
          have hnear : b =ᶠ[𝓝 z] (fun z : ℝ × ℝ ↦ p z.1 z.2 - ψ z.1 * φ z.1) := by
            filter_upwards [continuous_snd.continuousAt (Ioi_mem_nhds hz')] with w hw
            simp only [b, hχone w.2 hw.le, Complex.ofReal_one, one_mul]
          rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
          exact (hdec z).2 (zero_lt_one.trans hz').le
      have hznorm : ‖z‖ ≤ (1 + max R 0) * (1 + |z.2|) := by
        have hxR : ‖z.1‖ ≤ max R 0 := (hR z.1 hx).trans (le_max_left R 0)
        simp only [Prod.norm_def, Real.norm_eq_abs] at hxR ⊢
        apply max_le
        · nlinarith [le_max_right R 0, abs_nonneg z.2]
        · nlinarith [le_max_right R 0, abs_nonneg z.2]
      calc
        _ ≤ ((1 + max R 0) * (1 + |z.2|)) ^ N * ‖iteratedFDeriv ℝ k b z‖ := by
          gcongr
        _ = A * ((1 + |z.2|) ^ N * ‖iteratedFDeriv ℝ k b z‖) := by
          rw [mul_pow]
          exact mul_assoc _ _ _
        _ ≤ A * C := mul_le_mul_of_nonneg_left hd hA
        _ ≤ _ := le_add_of_nonneg_left (abs_nonneg C₀)
  · have hz : iteratedFDeriv ℝ k b z = 0 := by
      by_contra hz
      exact hx (hbSupp (support_iteratedFDeriv_subset k hz))
    simp only [hz, norm_zero, mul_zero]
    exact add_nonneg (abs_nonneg C₀) (mul_nonneg hA hC)

/-- The exact local Fourier projection symbol in the project's unnormalized frequency convention. -/
def periodicProjectionMatrixSymbol (ψ φ : 𝓢(ℝ, ℂ)) : SymbolFunction 1 1 1 :=
  fun x ξ ↦ periodicProjectionSymbol ψ φ
      ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x)
      (((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm ξ) / (2 * Real.pi)) •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))

/-- The positive cotangent branch of the same localized symbol, before frequency regularization. -/
def periodicProjectionPrincipalData (ψ φ : 𝓢(ℝ, ℂ)) : SymbolFunction 1 1 1 :=
  fun x ξ ↦ if 0 < ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm ξ) then
    (ψ ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x) *
      φ ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x)) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) else 0

/-- The exact Fourier projection has order zero and the indicated principal data. -/
theorem periodicProjectionMatrixSymbol_properties (ψ φ : 𝓢(ℝ, ℂ))
    (hψ : HasCompactSupport (ψ : ℝ → ℂ))
    (hsep : ∀ (x : ℝ) (n : ℤ), n ≠ 0 → ψ x * φ (x + (n : ℝ)) = 0) :
    IsSymbol Set.univ 0 (periodicProjectionMatrixSymbol ψ φ) ∧
      IsSmoothingSymbol Set.univ (periodicProjectionMatrixSymbol ψ φ -
        frequencyCutoffSymbol (periodicProjectionPrincipalData ψ φ)) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let X := EuclideanSpace ℝ (Fin 1)
  let Y := EuclideanSpace ℂ (Fin 1)
  let l : X ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let a := periodicProjectionPrincipalData ψ φ
  have hl : ContDiff ℝ ∞ l := l.toContinuousLinearEquiv.contDiff
  have hg : ContDiff ℝ ∞ (fun z : X × X ↦ (ψ (l z.1) * φ (l z.1)) •
      ContinuousLinearMap.id ℂ Y) :=
    (((ψ.smooth ⊤).comp (hl.comp contDiff_fst)).mul
      ((φ.smooth ⊤).comp (hl.comp contDiff_fst))).smul contDiff_const
  -- The branch is smooth on each nonzero sign component of the original one-dimensional model.
  have haSmooth : ContDiffOn ℝ ∞ (Function.uncurry a)
      (Set.univ ×ˢ {ξ : X | ξ ≠ 0}) := by
    intro z hz
    have hne : l z.2 ≠ 0 := by
      intro hzero
      exact hz.2 (l.injective (hzero.trans l.map_zero.symm))
    by_cases hpos : 0 < l z.2
    · have hnear : Function.uncurry a =ᶠ[𝓝 z]
          (fun z : X × X ↦ (ψ (l z.1) * φ (l z.1)) • ContinuousLinearMap.id ℂ Y) := by
        filter_upwards [(hl.continuous.comp continuous_snd).continuousAt (Ioi_mem_nhds hpos)]
          with w hw
        exact ite_eq_left hw
      exact (hg.contDiffAt.congr_of_eventuallyEq hnear).contDiffWithinAt
    · have hneg : l z.2 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
      have hnear : Function.uncurry a =ᶠ[𝓝 z] (fun _ ↦ 0) := by
        filter_upwards [(hl.continuous.comp continuous_snd).continuousAt (Iio_mem_nhds hneg)]
          with w hw
        exact ite_eq_right (not_lt_of_ge hw.le)
      exact (contDiffAt_const.congr_of_eventuallyEq hnear).contDiffWithinAt
  have haHom : IsHomogeneousSymbol Set.univ 0 a := by
    intro x _ ξ _ t ht
    have hsign : 0 < l (t • ξ) ↔ 0 < l ξ := by
      rw [map_smul, smul_eq_mul]
      exact mul_pos_iff_of_pos_left ht
    change (if 0 < l (t • ξ) then
      (ψ (l x) * φ (l x)) • ContinuousLinearMap.id ℂ Y else 0) =
        (t ^ (0 : ℝ)) • (if 0 < l ξ then
          (ψ (l x) * φ (l x)) • ContinuousLinearMap.id ℂ Y else 0)
    simp only [hsign, Real.rpow_zero, one_smul]
  have haReg := isSymbol_frequencyCutoffSymbol Set.univ isOpen_univ 0 a haSmooth haHom
  -- Use the same existing frequency cutoff after the exact 2π rescaling.
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hcOne : 1 < c := by dsimp [c]; nlinarith [Real.one_le_pi_div_two]
  let χ (t : ℝ) := if 0 < t then highFrequencyCutoff 1 (l.symm (c * t)) else 0
  have hχzero (t : ℝ) (ht : t ≤ 0) : χ t = 0 := ite_eq_right (not_lt_of_ge ht)
  have hχone (t : ℝ) (ht : 1 ≤ t) : χ t = 1 := by
    rw [show χ t = highFrequencyCutoff 1 (l.symm (c * t)) from ite_eq_left (lt_of_lt_of_le
      zero_lt_one ht), highFrequencyCutoff_eq_one]
    rw [l.symm.norm_map, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (zero_le_one.trans ht))]
    nlinarith
  have hχ : ContDiff ℝ ∞ χ := by
    have hcut : ContDiff ℝ ∞ (fun t : ℝ ↦ highFrequencyCutoff 1 (l.symm (c * t))) :=
      contDiff_highFrequencyCutoff.comp
        (l.symm.toContinuousLinearEquiv.contDiff.comp (contDiff_const.mul contDiff_id))
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : 0 < t
    · apply hcut.contDiffAt.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ite_eq_left hu
    · by_cases ht0 : t = 0
      · subst t
        apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        have hn : ContinuousAt (fun u : ℝ ↦ ‖l.symm (c * u)‖) 0 := by fun_prop
        have hsmall : ‖l.symm (c * (0 : ℝ))‖ < (1 / 2 : ℝ) := by simp
        filter_upwards [hn (Iio_mem_nhds hsmall)] with u hu
        dsimp only [χ]
        split_ifs
        · exact highFrequencyCutoff_eq_zero _ hu.le
        · rfl
      · have hneg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
        apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hneg] with u hu
        exact hχzero u hu.le
  obtain ⟨r, hr⟩ := exists_schwartz_periodicProjectionRemainder ψ φ hψ hsep χ hχ hχzero hχone
  let d : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 c⁻¹ (inv_ne_zero hc.ne'))
  let L : (X × X) ≃L[ℝ] (ℝ × ℝ) :=
    l.toContinuousLinearEquiv.prodCongr (l.toContinuousLinearEquiv.trans d)
  let T : ℂ →L[ℂ] (Y →L[ℂ] Y) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ Y)
  let S : 𝓢(X × X, Y →L[ℂ] Y) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L r).postcompCLM T
  have hS (x ξ : X) : S (x, ξ) = periodicProjectionMatrixSymbol ψ φ x ξ -
      frequencyCutoffSymbol a x ξ := by
    have hdiv : c * (l ξ / c) = l ξ := mul_div_cancel₀ _ hc.ne'
    have hsign : 0 < l ξ / c ↔ 0 < l ξ := div_pos_iff_of_pos_right hc
    have hbase : l.symm (c * (l ξ / c)) = ξ := by rw [hdiv, l.symm_apply_apply]
    change r (l x, c⁻¹ * l ξ) • ContinuousLinearMap.id ℂ Y = _
    rw [show c⁻¹ * l ξ = l ξ / c by rw [div_eq_mul_inv, mul_comm], hr]
    change (periodicProjectionSymbol ψ φ (l x) (l ξ / c) -
      (χ (l ξ / c) : ℂ) * (ψ (l x) * φ (l x))) • ContinuousLinearMap.id ℂ Y =
        periodicProjectionSymbol ψ φ (l x) (l ξ / c) • ContinuousLinearMap.id ℂ Y -
          (highFrequencyCutoff 1 ξ : ℂ) • (if 0 < l ξ then
            (ψ (l x) * φ (l x)) • ContinuousLinearMap.id ℂ Y else 0)
    by_cases hpos : 0 < l ξ
    · simp only [χ, hsign, hpos, ↓reduceIte, hbase, sub_smul, mul_smul]
    · simp only [χ, hsign, hpos, ↓reduceIte, Complex.ofReal_zero, zero_mul, sub_zero,
        smul_zero, sub_zero]
  have heq : (fun x ξ ↦ S (x, ξ)) = periodicProjectionMatrixSymbol ψ φ - frequencyCutoffSymbol a :=
    funext (fun x ↦ funext (hS x))
  have hs : IsSmoothingSymbol Set.univ (periodicProjectionMatrixSymbol ψ φ -
      frequencyCutoffSymbol a) := heq ▸ isSmoothingSymbol_of_schwartz S
  refine ⟨?_, hs⟩
  have h := haReg.add isOpen_univ (hs 0)
  have he : frequencyCutoffSymbol a +
      (periodicProjectionMatrixSymbol ψ φ - frequencyCutoffSymbol a) =
        periodicProjectionMatrixSymbol ψ φ := by abel
  exact he ▸ h

end AtiyahSinger
