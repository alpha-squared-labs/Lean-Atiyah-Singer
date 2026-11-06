/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndex
public import AtiyahSinger.Analysis.CircleFourierIndex
public import AtiyahSinger.Analysis.SmoothSectionMultiplication
public import AtiyahSinger.Geometry.CircleCotangent
public import AtiyahSinger.Geometry.FourierCircle

import AtiyahSinger.Analysis.CircleFourierLocalPseudodifferential
import AtiyahSinger.Analysis.HomogeneousSymbolOperatorComposition
import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol
import AtiyahSinger.Analysis.SobolevCutoff
import AtiyahSinger.Geometry.SmoothBundlePresentation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The original circle Fourier operator in the global PDO calculus

Public module ID: M0326.

AR02: Atiyah--Singer I, section 8, printed pp.525--526 and equation (8.2).
The projection on smooth sections is the unique restriction of the already
defined L² Fourier projection, under the actual scalar pullback through
`AddCircle.homeomorphCircle'`. The source operator is then literally
`M_z Π₊ + (I - Π₊)` on those same smooth sections. Its zero-order PDO property
is a conclusion in the existing finite-local-piece calculus.

Positive cotangent direction means positive evaluation on the derivative of
`t ↦ z * Circle.exp t`. The projection symbol is one on that component and
zero on the negative component. The operator symbol is multiplication by z
on the positive component and the identity on the negative component. Their
values on the zero section are immaterial to the homogeneous principal class.

The final class is the existing homogeneous symbol compactification in the
original cotangent K group. Its analytic index is -1. The oriented comparison
with the negative point pushforward is made separately and gives +1 for the
point normalization in CirclePointIndex. The native PDO realization, global
principal symbol, ellipticity and K-class evaluation retain these same objects.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set Function
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20

attribute [local instance] isSmoothComplexBundle_fourierCircleLine
  isSmoothPositiveMeasure_fourierCircleMeasure
  t2Space_cotangent locallyCompactSpace_cotangent finrank_real_complex_fact'

open Complex in
/-- The original nonnegative Fourier projection preserves the actual smooth section space. -/
theorem existsUnique_circleNonnegativeSmoothProjection :
    ∃! P : smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
        smoothSections (n := 1) (r := 1) FourierCircleLine,
      ∀ u, circleSmoothToFourierL2 (P u) =
        circleNonnegativeFourierProjection (circleSmoothToFourierL2 u) := by
  /- Stage 1: pull a smooth scalar section back through the specified
  homeomorphism, whose positive angular lift is exp(iθ). Repeated integration
  by parts gives rapidly decreasing integer Fourier coefficients. Cutting
  these coefficients to n ≥ 0 preserves rapid decrease and hence defines a
  smooth periodic function by termwise differentiated Fourier summation.
  Stage 2: descend this function to the original Circle and its trivial
  complex line. Its L² class is exactly the preexisting Hilbert projection,
  because both have the same original Fourier coefficients. The construction
  is complex-linear. Stage 3: injectivity of circleSmoothToFourierL2 forces
  uniqueness of the smooth section for each input, hence uniqueness of P.
  No PDO property or desired principal symbol is assumed in this restriction. -/
  -- Every angular derivative has the same period, so integration by parts
  -- has no boundary term at the endpoints of the original period interval.
  have periodic_iteratedDeriv (f : ℝ → ℂ)
      (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
      Function.Periodic (iteratedDeriv k f) (2 * Real.pi) := by
    have hshift : (fun x ↦ f (x + 2 * Real.pi)) = f := funext hp
    have h := congrArg (iteratedDeriv k) hshift
    rw [iteratedDeriv_comp_add_const] at h
    exact fun x ↦ congrFun h x
  -- One integration by parts multiplies the coefficient by i times its frequency.
  have periodic_fourierCoeff_deriv (f : ℝ → ℂ)
      (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi))
      (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
      (I * n) * fourierCoeffOn circlePeriodPositive.out (iteratedDeriv k f) n =
        fourierCoeffOn circlePeriodPositive.out (iteratedDeriv (k + 1) f) n := by
    have hderiv (x : ℝ) : HasDerivAt (iteratedDeriv k f)
        (iteratedDeriv (k + 1) f x) x := by
      rw [iteratedDeriv_succ]
      exact (hf.differentiable_iteratedDeriv k
        (by exact_mod_cast WithTop.coe_lt_top k) x).hasDerivAt
    have h := fourierCoeffOn_of_hasDerivAt circlePeriodPositive.out hn
      (fun x _ ↦ hderiv x)
      ((hf.continuous_iteratedDeriv (k + 1) (by simp)).intervalIntegrable _ _)
    have he := periodic_iteratedDeriv f hp k 0
    simp only [zero_add] at he
    rw [he, sub_self, mul_zero, zero_sub] at h
    rw [h]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    push_cast
    field_simp
    ring
  -- Iterate that identity and bound the remaining continuous derivative
  -- on the compact period interval to get decay of every polynomial order.
  have periodic_fourierCoeff_decay (f : ℝ → ℂ)
      (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
      ∃ C : ℝ, ∀ n : ℤ, n ≠ 0 →
        ‖(n : ℂ)‖ ^ k * ‖fourierCoeffOn circlePeriodPositive.out f n‖ ≤ C := by
    have hpower (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
        (I * n) ^ k * fourierCoeffOn circlePeriodPositive.out f n =
          fourierCoeffOn circlePeriodPositive.out (iteratedDeriv k f) n := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_assoc, ih]
        exact periodic_fourierCoeff_deriv f hf hp k n hn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous_iteratedDeriv k (by simp)).continuousOn
    refine ⟨C, fun n hn ↦ ?_⟩
    have hnorm := congrArg norm (hpower k n hn)
    simp only [norm_mul, norm_pow, norm_I, one_mul] at hnorm
    rw [hnorm, fourierCoeffOn_eq_integral]
    simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_div, abs_one,
      abs_of_pos circlePeriodPositive.out]
    have hbound : ‖∫ x in (0 : ℝ)..2 * Real.pi,
        fourier (-n) (x : AddCircle (2 * Real.pi - 0)) • iteratedDeriv k f x‖ ≤
          C * (2 * Real.pi) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 2 * Real.pi) (C := C)
        (f := fun x ↦ fourier (-n) (x : AddCircle (2 * Real.pi - 0)) • iteratedDeriv k f x) ?_
      · simpa [abs_of_pos circlePeriodPositive.out] using h
      · intro x hx
        simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
        apply hC x
        rw [Set.uIoc_of_le circlePeriodPositive.out.le] at hx
        exact ⟨hx.1.le, hx.2⟩
    calc
      _ ≤ (1 / (2 * Real.pi)) * (C * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = C := by field_simp
  -- Two additional integrations by parts give a summable inverse-square majorant.
  have summable_periodic_fourierCoeff_weight (f : ℝ → ℂ)
      (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (k : ℕ) :
      Summable (fun n : ℤ ↦ ‖(n : ℂ)‖ ^ k *
        ‖fourierCoeffOn circlePeriodPositive.out f n‖) := by
    obtain ⟨C, hC⟩ := periodic_fourierCoeff_decay f hf hp (k + 2)
    have hsum : Summable (fun n : ℤ ↦ C * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left C
    apply hsum.of_norm_bounded_eventually
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have h := hC n hn
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)),
      ← div_eq_mul_one_div]
    have hsq : ‖(n : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
      rw [← Complex.ofReal_intCast, norm_real, Real.norm_eq_abs, sq_abs]
    rw [pow_add, mul_right_comm, hsq] at h
    exact (le_div_iff₀ (sq_pos_of_ne_zero hn')).mpr h
  -- The weighted bounds justify differentiating the Fourier series to every order.
  have contDiff_fourierSeries_of_summable_weight (c : ℤ → ℂ)
      (hc : ∀ k : ℕ, Summable (fun n : ℤ ↦ ‖(n : ℂ)‖ ^ k * ‖c n‖)) :
      ContDiff ℝ ∞ (fun x : ℝ ↦ ∑' n : ℤ, c n * fourier n
        (x : AddCircle (2 * Real.pi))) := by
    have hderiv (n : ℤ) (x : ℝ) :
        HasDerivAt (fun x : ℝ ↦ fourier n (x : AddCircle (2 * Real.pi)))
          (I * n * fourier n (x : AddCircle (2 * Real.pi))) x := by
      have h := hasDerivAt_fourier (2 * Real.pi) n x
      have heq : 2 * (Real.pi : ℂ) * I * n / (2 * Real.pi) = I * n := by
        field_simp
      simpa only [ofReal_mul, ofReal_ofNat, heq] using h
    have hsmooth (n : ℤ) :
        ContDiff ℝ ∞ (fun x : ℝ ↦ c n * fourier n (x : AddCircle (2 * Real.pi))) := by
      simp only [fourier_coe_apply]
      have hreal : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
      exact contDiff_const.mul (((contDiff_const.mul hreal).div_const
        ((2 * Real.pi : ℝ) : ℂ)).cexp)
    have hiter (k : ℕ) (n : ℤ) :
        iteratedDeriv k (fun x : ℝ ↦ c n * fourier n (x : AddCircle (2 * Real.pi))) =
          fun x : ℝ ↦ (I * n) ^ k * c n * fourier n (x : AddCircle (2 * Real.pi)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext x
        rw [((hderiv n x).const_mul ((I * n) ^ k * c n)).deriv]
        ring
    apply contDiff_tsum hsmooth (fun k _ ↦ hc k)
    intro k n x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter]
    simp only [norm_mul, norm_pow, norm_I, one_mul, fourier_apply, Circle.norm_coe, mul_one,
      le_refl]
  -- Smoothness of the angular lift descends using an actual local logarithm branch.
  have contMDiff_circle_of_contDiff_exp (f : Circle → ℂ)
      (hf : ContDiff ℝ ∞ (fun t : ℝ ↦ f (Circle.exp t))) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ f := by
    intro z
    -- Rotate the logarithm branch to the current point. Its argument is one
    -- there, so it supplies a smooth local inverse to the same exponential.
    let θ (w : Circle) : ℝ := (z : ℂ).arg + (Complex.log ((z⁻¹ * w : Circle) : ℂ)).im
    have hnormalized : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
        (fun w : Circle ↦ ((z⁻¹ * w : Circle) : ℂ)) z := by
      have hcoe : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
          (fun w : Circle ↦ (w : ℂ)) z :=
        (contMDiff_coe_sphere (E := ℂ) (n := 1)).contMDiffAt
      have hmul : ContDiff ℝ ∞ (fun w : ℂ ↦ ((z⁻¹ : Circle) : ℂ) * w) :=
        contDiff_const.mul contDiff_id
      exact hmul.contMDiff.contMDiffAt.comp z hcoe
    have hslit : ((z⁻¹ * z : Circle) : ℂ) ∈ Complex.slitPlane := by simp
    have hlogC : ContDiffAt ℂ ∞ Complex.log ((z⁻¹ * z : Circle) : ℂ) :=
      Complex.contDiffAt_log hslit
    have hlog := (hlogC.restrict_scalars ℝ).contMDiffAt.comp z hnormalized
    have hθ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℝ) ∞ θ z :=
      contMDiffAt_const.add (Complex.imCLM.contMDiffAt.comp z hlog)
    have hexp (w : Circle) : Circle.exp (θ w) = w := by
      dsimp only [θ]
      rw [Complex.log_im, Circle.exp_add, Circle.exp_arg, Circle.exp_arg, mul_inv_cancel_left]
    exact (hf.contMDiff.contMDiffAt.comp z hθ).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w ↦ congrArg f (hexp w).symm)
  -- Truncation preserves all weighted bounds. The original Fourier coefficient
  -- functionals identify the reconstructed smooth function with this exact cutoff.
  have exists_smooth_circle_fourierCutoff (f : Circle → ℂ)
      (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ f) :
      ∃ g : Circle → ℂ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ g ∧
        ∀ n : ℤ, fourierCoeff (fun x ↦ g (AddCircle.homeomorphCircle' x)) n =
          if 0 ≤ n then fourierCoeff (fun x ↦ f (AddCircle.homeomorphCircle' x)) n else 0 := by
    let F : C(AddCircle (2 * Real.pi), ℂ) :=
      ⟨fun x ↦ f (AddCircle.homeomorphCircle' x),
        hf.continuous.comp AddCircle.homeomorphCircle'.continuous⟩
    have hlift : ContDiff ℝ ∞ (fun t : ℝ ↦ f (Circle.exp t)) :=
      (hf.comp contMDiff_circleExp).contDiff
    have hp : Function.Periodic (fun t : ℝ ↦ f (Circle.exp t)) (2 * Real.pi) :=
      fun t ↦ congrArg f (Circle.periodic_exp t)
    have hcoeff (n : ℤ) : fourierCoeffOn circlePeriodPositive.out
        (fun t : ℝ ↦ f (Circle.exp t)) n = fourierCoeff F n := by
      rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
      simp only [F, ContinuousMap.coe_mk, AddCircle.homeomorphCircle'_apply_mk,
        fourier_coe_apply, sub_zero, zero_add]
    have hweight (k : ℕ) : Summable (fun n : ℤ ↦ ‖(n : ℂ)‖ ^ k * ‖fourierCoeff F n‖) := by
      simpa only [hcoeff] using summable_periodic_fourierCoeff_weight _ hlift hp k
    let c (n : ℤ) : ℂ := if 0 ≤ n then fourierCoeff F n else 0
    have hc (k : ℕ) : Summable (fun n : ℤ ↦ ‖(n : ℂ)‖ ^ k * ‖c n‖) := by
      apply (hweight k).of_nonneg_of_le (fun _ ↦ by positivity)
      intro n
      dsimp [c]
      split_ifs
      · exact le_rfl
      · simp only [norm_zero, mul_zero]
        positivity
    have hseries : Summable (fun n : ℤ ↦ c n • (fourier n : C(AddCircle (2 * Real.pi), ℂ))) := by
      apply Summable.of_norm
      simpa only [norm_smul, fourier_norm, mul_one, pow_zero, one_mul] using hc 0
    let G : C(AddCircle (2 * Real.pi), ℂ) := ∑' n : ℤ, c n • fourier n
    have hG (x : AddCircle (2 * Real.pi)) : G x = ∑' n : ℤ, c n * fourier n x := by
      exact (ContinuousMap.evalCLM ℂ x).map_tsum hseries
    let g (z : Circle) : ℂ := G (AddCircle.homeomorphCircle'.symm z)
    refine ⟨g, ?_, ?_⟩
    · apply contMDiff_circle_of_contDiff_exp
      have hliftG : (fun t : ℝ ↦ g (Circle.exp t)) =
          (fun t : ℝ ↦ ∑' n : ℤ, c n * fourier n (t : AddCircle (2 * Real.pi))) := by
        funext t
        change G (AddCircle.homeomorphCircle'.symm
          (AddCircle.homeomorphCircle' (t : AddCircle (2 * Real.pi)))) = _
        rw [Homeomorph.symm_apply_apply, hG]
      rw [hliftG]
      exact contDiff_fourierSeries_of_summable_weight c hc
    · intro n
      let L : C(AddCircle (2 * Real.pi), ℂ) →L[ℂ] ℂ :=
        (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 n).comp
          ((fourierBasis (T := 2 * Real.pi)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
            (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ))
      have hL (H : C(AddCircle (2 * Real.pi), ℂ)) : L H = fourierCoeff H n := by
        change (fourierBasis (T := 2 * Real.pi)).repr
          (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ H) n = _
        rw [fourierBasis_repr, fourierCoeff_toLp]
      have hLc (j : ℤ) : L (c j • fourier j) = if j = n then c j else 0 := by
        rw [hL]
        change fourierCoeff (c j • (fourier j : AddCircle (2 * Real.pi) → ℂ)) n = _
        rw [fourierCoeff.const_smul, fourierCoeff_fourier]
        simp only [Pi.single_apply]
        by_cases h : j = n
        · simp [h]
        · simp [h, Ne.symm h]
      have hresult : fourierCoeff G n = c n := by
        rw [← hL, show G = ∑' j : ℤ, c j • fourier j from rfl, L.map_tsum hseries]
        simp only [hLc, tsum_ite_eq]
      have hfun : (fun x ↦ g (AddCircle.homeomorphCircle' x)) = G := by
        funext x
        exact congrArg G (AddCircle.homeomorphCircle'.symm_apply_apply x)
      rw [hfun, hresult]
      rfl
  -- Apply the scalar construction to the original trivial-line coordinate.
  have hcoeff (u : smoothSections (n := 1) (r := 1) FourierCircleLine) (n : ℤ) :
      fourierCoeff (circleSmoothToFourierL2 u) n =
        fourierCoeff (fun x ↦ u.val (AddCircle.homeomorphCircle' x) 0) n := by
    apply fourierCoeff_toLp
  have hrestrict (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      ∃ v : smoothSections (n := 1) (r := 1) FourierCircleLine,
        circleSmoothToFourierL2 v =
          circleNonnegativeFourierProjection (circleSmoothToFourierL2 u) := by
    obtain ⟨g, hg, hgcoeff⟩ := exists_smooth_circle_fourierCutoff
      (fun z : Circle ↦ u.val z 0) (contMDiff_fourierCircleSectionCoordinate u)
    let v (z : Circle) : FourierCircleLine z := g z • EuclideanSpace.single 0 1
    have hv : IsSmoothSection (n := 1) (r := 1) FourierCircleLine v := by
      intro e he
      let := he
      obtain rfl := Bundle.Trivial.eq_trivialization Circle (EuclideanSpace ℂ (Fin 1)) e
      have hs : ContDiff ℝ ∞
          (fun p : ℂ × EuclideanSpace ℂ (Fin 1) ↦ p.1 • p.2) := contDiff_smul
      exact (hs.contMDiff.comp (hg.prodMk_space contMDiff_const)).contMDiffOn
    refine ⟨⟨v, hv⟩, ?_⟩
    apply (fourierBasis (T := 2 * Real.pi)).repr.injective
    apply lp.ext
    funext n
    rw [fourierBasis_repr, fourierBasis_repr,
      circleNonnegativeFourierProjection_fourierCoeff, hcoeff, hcoeff]
    simpa [v, Pi.single_apply] using hgcoeff n
  -- The original L² inclusion detects equality, so its restriction is linear
  -- and uniquely determined without selecting any alternative projection.
  let output (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      smoothSections (n := 1) (r := 1) FourierCircleLine := (hrestrict u).choose
  have houtput (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      circleSmoothToFourierL2 (output u) =
        circleNonnegativeFourierProjection (circleSmoothToFourierL2 u) :=
    (hrestrict u).choose_spec
  let P : smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
      smoothSections (n := 1) (r := 1) FourierCircleLine :=
    { toFun := output
      map_add' := by
        intro u v
        apply circleSmoothToFourierL2_injective
        change circleSmoothToFourierL2 (output (u + v)) =
          circleSmoothToFourierL2 (output u + output v)
        rw [houtput, map_add, map_add, map_add, houtput, houtput]
      map_smul' := by
        intro c u
        apply circleSmoothToFourierL2_injective
        change circleSmoothToFourierL2 (output (c • u)) =
          circleSmoothToFourierL2 (c • output u)
        rw [houtput, map_smul, map_smul, map_smul, houtput] }
  have hP (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      circleSmoothToFourierL2 (P u) =
        circleNonnegativeFourierProjection (circleSmoothToFourierL2 u) :=
    (hrestrict u).choose_spec
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  apply LinearMap.ext
  intro u
  apply circleSmoothToFourierL2_injective
  exact (hQ u).trans (hP u).symm

/-- The uniquely specified smooth restriction of the original L² Fourier projection. -/
def circleNonnegativeSmoothProjection :
    smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
      smoothSections (n := 1) (r := 1) FourierCircleLine :=
  existsUnique_circleNonnegativeSmoothProjection.exists.choose

/-- Smooth restriction commutes with the same actual scalar inclusion into Fourier L². -/
theorem circleSmoothToFourierL2_nonnegativeProjection
    (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
    circleSmoothToFourierL2 (circleNonnegativeSmoothProjection u) =
      circleNonnegativeFourierProjection (circleSmoothToFourierL2 u) := by
  /- Extract the restriction formula from the exact existence witness used
  to define circleNonnegativeSmoothProjection. The source section, character
  orientation, zero frequency, and normalized Haar measure are unchanged. -/
  exact existsUnique_circleNonnegativeSmoothProjection.exists.choose_spec u

/-- The source's operator on the original smooth sections, with its literal multiplier. -/
def circleFourierSmoothOperator :
    smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
      smoothSections (n := 1) (r := 1) FourierCircleLine :=
  let hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle ↦ (z : ℂ)) := contMDiff_coe_sphere
  (smoothSectionMul (n := 1) (r := 1) (M := Circle) FourierCircleLine
    (fun z : Circle ↦ (z : ℂ)) hf).comp
      circleNonnegativeSmoothProjection +
    (LinearMap.id - circleNonnegativeSmoothProjection)

/-- The smooth source operator and the previous L² operator act on the same actual functions. -/
theorem circleSmoothToFourierL2_fourierOperator
    (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
    circleSmoothToFourierL2 (circleFourierSmoothOperator u) =
      circleFourierIndexOperator (circleSmoothToFourierL2 u) := by
  /- Stage 1: the scalar coordinate z, pulled back through homeomorphCircle',
  is the original Fourier character of frequency one for period 2π. Therefore
  pointwise smooth multiplication becomes the previously defined L∞--L²
  Hölder multiplication, with equality of the actual almost-everywhere classes.
  Stage 2: apply the projection restriction formula and complex linearity
  of the smooth inclusion to the displayed sum M_z Π₊ + (I - Π₊). -/
  let hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle ↦ (z : ℂ)) := contMDiff_coe_sphere
  let M := smoothSectionMul (n := 1) (r := 1) (M := Circle) FourierCircleLine
    (fun z : Circle ↦ (z : ℂ)) hf
  let scalar (v : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x ↦ v.val (AddCircle.homeomorphCircle' x) 0,
      (contMDiff_fourierCircleSectionCoordinate v).continuous.comp
        AddCircle.homeomorphCircle'.continuous⟩
  have hscalar (v : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      (circleSmoothToFourierL2 v : AddCircle (2 * Real.pi) → ℂ) =ᵐ[
        AddCircle.haarAddCircle] scalar v :=
    ContinuousMap.coeFn_toAEEqFun AddCircle.haarAddCircle (scalar v)
  have hchar (x : AddCircle (2 * Real.pi)) :
      (AddCircle.homeomorphCircle' x : ℂ) = fourier 1 x := by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      rw [AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp, fourier_coe_apply]
      congr 1
      push_cast
      field_simp
  -- Hölder multiplication and smooth multiplication represent the same
  -- pointwise product under the specified normalized Haar embedding.
  have hmul (v : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      circleSmoothToFourierL2 (M v) =
        circleFourierModeMultiplication (circleSmoothToFourierL2 v) := by
    apply Lp.ext
    have hh := ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ)
      (fourierLp (T := 2 * Real.pi) ⊤ 1) (circleSmoothToFourierL2 v) (r := 2)
    filter_upwards [hscalar (M v), hh, hscalar v,
      coeFn_fourierLp (T := 2 * Real.pi) ⊤ 1] with x hx hhx hv hmode
    rw [hx]
    apply Eq.trans ?_ hhx.symm
    change scalar (M v) x =
      fourierLp (T := 2 * Real.pi) ⊤ 1 x * circleSmoothToFourierL2 v x
    rw [hmode, hv]
    change (AddCircle.homeomorphCircle' x : ℂ) *
      v.val (AddCircle.homeomorphCircle' x) 0 = _
    rw [hchar]
    rfl
  change circleSmoothToFourierL2
    (M (circleNonnegativeSmoothProjection u) + (u - circleNonnegativeSmoothProjection u)) = _
  rw [map_add, map_sub, hmul, circleSmoothToFourierL2_nonnegativeProjection]
  rfl

/-- The first-character commutator of the original smooth projection has rank one. -/
theorem circleProjection_mode_commutator
    (u : smoothSections (n := 1) (r := 1) FourierCircleLine) (z : Circle) :
    (circleNonnegativeSmoothProjection
      (@smoothSectionMul 1 1 Circle inferInstance inferInstance FourierCircleLine
        inferInstance inferInstance inferInstance inferInstance inferInstance
        (fun w : Circle ↦ (w : ℂ)) (contMDiff_coe_sphere (n := 1)) u)).val z 0 -
      (z : ℂ) * (circleNonnegativeSmoothProjection u).val z 0 =
        fourierCoeff (fun x ↦ u.val (AddCircle.homeomorphCircle' x) 0) (-1) := by
  -- The original positive angular coordinate is exactly the first Fourier character.
  let M := smoothSectionMul (n := 1) (r := 1) (M := Circle) FourierCircleLine
    (fun w : Circle ↦ (w : ℂ)) contMDiff_coe_sphere
  let scalar (v : smoothSections (n := 1) (r := 1) FourierCircleLine) :
      C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x ↦ v.val (AddCircle.homeomorphCircle' x) 0,
      (contMDiff_fourierCircleSectionCoordinate v).continuous.comp
        AddCircle.homeomorphCircle'.continuous⟩
  have hchar (x : AddCircle (2 * Real.pi)) :
      (AddCircle.homeomorphCircle' x : ℂ) = fourier 1 x := by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      rw [AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp, fourier_coe_apply]
      congr 1
      push_cast
      field_simp
  -- Read the original Hilbert cutoff through the specified smooth inclusion.
  have hP (v : smoothSections (n := 1) (r := 1) FourierCircleLine) (n : ℤ) :
      fourierCoeff (scalar (circleNonnegativeSmoothProjection v)) n =
        if 0 ≤ n then fourierCoeff (scalar v) n else 0 := by
    have h := congrArg (fun w : CircleFourierL2 ↦ fourierCoeff w n)
      (circleSmoothToFourierL2_nonnegativeProjection v)
    rw [circleNonnegativeFourierProjection_fourierCoeff] at h
    have hc (w : smoothSections (n := 1) (r := 1) FourierCircleLine) :
        fourierCoeff (circleSmoothToFourierL2 w) n = fourierCoeff (scalar w) n :=
      fourierCoeff_toLp _ n
    rw [hc, hc] at h
    exact h
  -- Multiplication by that same character shifts every coefficient by one.
  have hM (v : smoothSections (n := 1) (r := 1) FourierCircleLine) (n : ℤ) :
      fourierCoeff (scalar (M v)) n = fourierCoeff (scalar v) (n - 1) := by
    apply integral_congr_ae
    filter_upwards with x
    change fourier (-n) x *
      ((AddCircle.homeomorphCircle' x : ℂ) * v.val (AddCircle.homeomorphCircle' x) 0) = _
    rw [hchar, ← mul_assoc, ← fourier_add]
    have hn : -n + 1 = -(n - 1) := by omega
    rw [hn]
    rfl
  let d := circleNonnegativeSmoothProjection (M u) - M (circleNonnegativeSmoothProjection u)
  let c := fourierCoeff (scalar u) (-1)
  -- Only the constant coefficient remains; Fourier completeness detects the actual function.
  have hd : scalar d = ContinuousMap.const _ c := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    apply (fourierBasis (T := 2 * Real.pi)).repr.injective
    apply lp.ext
    funext n
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp]
    have hdcoeff : fourierCoeff (scalar d) n =
        fourierCoeff (scalar (circleNonnegativeSmoothProjection (M u))) n -
          fourierCoeff (scalar (M (circleNonnegativeSmoothProjection u))) n := by
      have hc (v : smoothSections (n := 1) (r := 1) FourierCircleLine) :
          fourierCoeff (circleSmoothToFourierL2 v) n = fourierCoeff (scalar v) n :=
        fourierCoeff_toLp _ n
      rw [← hc, ← hc, ← hc]
      change fourierCoeff (circleSmoothToFourierL2
        (circleNonnegativeSmoothProjection (M u) - M (circleNonnegativeSmoothProjection u))) n = _
      rw [map_sub]
      simp only [← fourierBasis_repr, map_sub, lp.coeFn_sub, Pi.sub_apply]
    rw [hdcoeff, hP, hM, hM, hP]
    have hc : fourierCoeff (ContinuousMap.const (AddCircle (2 * Real.pi)) c) n =
        if n = 0 then c else 0 := by
      have he : (ContinuousMap.const (AddCircle (2 * Real.pi)) c :
          AddCircle (2 * Real.pi) → ℂ) = c • fourier 0 := by ext x; simp
      rw [he]
      change fourierCoeff (c • (fourier 0 : AddCircle (2 * Real.pi) → ℂ)) n = _
      rw [fourierCoeff.const_smul, fourierCoeff_fourier]
      simp [Pi.single_apply]
    rw [hc]
    by_cases hn : n = 0
    · subst n
      simp [c]
    · by_cases hp : 0 < n
      · simp only [ite_eq_left hp.le, ite_eq_left (show 0 ≤ n - 1 by omega),
          ite_eq_right hn, sub_self]
      · simp only [ite_eq_right (show ¬ 0 ≤ n by omega),
          ite_eq_right (show ¬ 0 ≤ n - 1 by omega), ite_eq_right hn, sub_self]
  have hh := congrArg (fun w : C(AddCircle (2 * Real.pi), ℂ) ↦
    w (AddCircle.homeomorphCircle'.symm z)) hd
  change (d.val (AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm z))) 0 = c at hh
  rw [Homeomorph.apply_symm_apply] at hh
  exact hh


/-- The actual nonnegative Fourier projection has a smooth kernel between disjoint cutoffs. -/
theorem isSmoothingOperator_circleProjection_offDiagonal (φ ψ : Circle → ℂ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ ψ)
    (hdis : Disjoint (tsupport φ) (tsupport ψ)) :
    IsSmoothingOperator (n := 1) (r := 1) (q := 1)
      (E := FourierCircleLine) (F := FourierCircleLine) fourierCircleMeasure
      ((smoothSectionMul FourierCircleLine ψ hψ).comp
        (circleNonnegativeSmoothProjection.comp (smoothSectionMul FourierCircleLine φ hφ))) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  let C := EuclideanSpace ℂ (Fin 1)
  let k (z w : Circle) : ℂ := ψ z * φ w / (1 - (z : ℂ) / (w : ℂ))
  -- Disjoint supports remove the Cauchy singularity on the whole product circle.
  have hk : ContMDiff (I.prod I) 𝓘(ℝ, ℂ) ∞ (Function.uncurry k) := by
    change ContMDiff (I.prod I) 𝓘(ℝ, ℂ) ∞ (fun p : Circle × Circle ↦
      ψ p.1 * φ p.2 / (1 - (p.1 : ℂ) / (p.2 : ℂ)))
    intro p
    by_cases he : p.1 = p.2
    · -- On the diagonal at least one cutoff vanishes on an entire neighborhood.
      by_cases hx : p.2 ∈ tsupport φ
      · have hy : p.1 ∉ tsupport ψ := by
          intro hy
          exact Set.disjoint_left.mp hdis hx (he ▸ hy)
        have hev := (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto
          continuous_fst.continuousAt
        apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [hev] with z hz
        simp only [Function.comp_apply, Pi.zero_apply] at hz
        simp [hz]
      · have hev := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
          continuous_snd.continuousAt
        apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [hev] with z hz
        simp only [Function.comp_apply, Pi.zero_apply] at hz
        simp [hz]
    · have hne : (1 : ℂ) - (p.1 : ℂ) / (p.2 : ℂ) ≠ 0 := by
        intro h
        have hd : (p.1 : ℂ) / (p.2 : ℂ) = 1 := (sub_eq_zero.mp h).symm
        exact he (Subtype.ext ((div_eq_one_iff_eq p.2.coe_ne_zero).mp hd))
      have hz : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) 𝓘(ℝ, ℂ) ∞
          (fun p : Circle × Circle ↦ (p.1 : ℂ)) :=
        contMDiff_coe_sphere.comp contMDiff_fst
      have hw : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) 𝓘(ℝ, ℂ) ∞
          (fun p : Circle × Circle ↦ (p.2 : ℂ)) :=
        contMDiff_coe_sphere.comp contMDiff_snd
      have hnum := (show ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) from
        contDiff_fst.mul contDiff_snd).contMDiff.contMDiffAt.comp p
          ((hψ.comp contMDiff_fst).contMDiffAt.prodMk_space
            (hφ.comp contMDiff_snd).contMDiffAt)
      have hdiv : ContDiffAt ℂ ∞ (fun z : ℂ × ℂ ↦ z.1 / z.2)
          ((p.1 : ℂ), (p.2 : ℂ)) := contDiffAt_fst.div contDiffAt_snd p.2.coe_ne_zero
      have hquot := (hdiv.restrict_scalars ℝ).contMDiffAt.comp p
        (hz.contMDiffAt.prodMk_space hw.contMDiffAt)
      have hden := (contMDiffAt_const (c := (1 : ℂ))).sub hquot
      have hdiv' : ContDiffAt ℂ ∞ (fun z : ℂ × ℂ ↦ z.1 / z.2)
          (ψ p.1 * φ p.2, 1 - (p.1 : ℂ) / (p.2 : ℂ)) :=
        contDiffAt_fst.div contDiffAt_snd hne
      exact (hdiv'.restrict_scalars ℝ).contMDiffAt.comp p (hnum.prodMk_space hden)
  let K : SmoothKernel (n := 1) (r := 1) (q := 1) FourierCircleLine FourierCircleLine :=
    { toFun z w := k z w • ContinuousLinearMap.id ℂ C
      isSmooth := by
        intro e f he hf
        let := he
        let := hf
        obtain rfl := Bundle.Trivial.eq_trivialization Circle C e
        obtain rfl := Bundle.Trivial.eq_trivialization Circle C f
        have hsmul : ContDiff ℝ ∞ (fun c : ℂ ↦ c • ContinuousLinearMap.id ℂ C) :=
          contDiff_id.smul contDiff_const
        apply (hsmul.contMDiff.comp hk).contMDiffOn.congr
        intro p _hp
        apply ContinuousLinearMap.ext
        intro v
        change (Bundle.Trivial.trivialization Circle C).continuousLinearMapAt ℂ p.1
          ((k p.1 p.2 • ContinuousLinearMap.id ℂ C)
            ((Bundle.Trivial.trivialization Circle C).symmL ℂ p.2 v)) = _
        rw [(Bundle.Trivial.trivialization Circle C).continuousLinearMapAt_apply_of_mem ℂ
          (by simp), (Bundle.Trivial.trivialization Circle C).symmL_apply (by simp)]
        rw [Bundle.Trivial.trivialization_symm_apply Circle C p.2 v]
        simp only [Bundle.Trivial.trivialization, Function.uncurry, Function.comp_apply]
        rfl }
  refine ⟨K, ?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext z
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  -- The original fixed output coordinate commutes with the actual kernel integral.
  have hint : (K.toLinearMap fourierCircleMeasure u).val z 0 =
      ∫ w, k z w * u.val w 0 ∂fourierCircleMeasure := by
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 ↦ ℂ) 0).integral_comp_comm
      (K.integrable_apply fourierCircleMeasure u z)).symm
  rw [hint]
  change (∫ w, k z w * u.val w 0 ∂fourierCircleMeasure) =
    ψ z * (circleNonnegativeSmoothProjection (smoothSectionMul FourierCircleLine φ hφ u)).val z 0
  by_cases hψz : ψ z = 0
  · simp [k, hψz]
  -- The input cutoff vanishes near this output point, so division by z-w is smooth.
  have hz : z ∉ tsupport φ := by
    intro hz
    exact Set.disjoint_left.mp hdis hz (subset_tsupport ψ (by exact hψz))
  let γ (w : Circle) : ℂ := φ w / ((z : ℂ) - (w : ℂ))
  have hγ : ContMDiff I 𝓘(ℝ, ℂ) ∞ γ := by
    intro w
    by_cases hw : w = z
    · subst w
      apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      simp only [Pi.zero_apply] at hy
      simp [γ, hy]
    · have hne : (z : ℂ) - (w : ℂ) ≠ 0 := by
        intro hh
        exact hw (Subtype.ext (sub_eq_zero.mp hh).symm)
      have hden : ContMDiffAt I 𝓘(ℝ, ℂ) ∞ (fun w : Circle ↦ (z : ℂ) - (w : ℂ)) w :=
        contMDiffAt_const.sub contMDiff_coe_sphere.contMDiffAt
      have hd : ContDiffAt ℂ ∞ (fun p : ℂ × ℂ ↦ p.1 / p.2)
          (φ w, (z : ℂ) - (w : ℂ)) := contDiffAt_fst.div contDiffAt_snd hne
      exact (hd.restrict_scalars ℝ).contMDiffAt.comp w
        (hφ.contMDiffAt.prodMk_space hden)
  let v := smoothSectionMul FourierCircleLine γ hγ u
  let M := smoothSectionMul (n := 1) (r := 1) (M := Circle) FourierCircleLine
    (fun w : Circle ↦ (w : ℂ)) contMDiff_coe_sphere
  have hinput : (z : ℂ) • v - M v = smoothSectionMul FourierCircleLine φ hφ u := by
    apply Subtype.ext
    funext w
    change (z : ℂ) • (γ w • u.val w) - (w : ℂ) • (γ w • u.val w) = φ w • u.val w
    rw [← sub_smul, smul_smul]
    by_cases hw : w = z
    · subst w
      rw [image_eq_zero_of_notMem_tsupport hz]
      simp [γ]
    · have hne : (z : ℂ) - (w : ℂ) ≠ 0 := by
        intro hh
        exact hw (Subtype.ext (sub_eq_zero.mp hh).symm)
      congr 1
      dsimp [γ]
      field_simp
  have hproj := congrArg circleNonnegativeSmoothProjection hinput
  rw [map_sub, map_smul] at hproj
  have hev := congrArg
    (fun w : smoothSections (n := 1) (r := 1) FourierCircleLine ↦ w.val z 0) hproj
  have hcomm := circleProjection_mode_commutator v z
  have heval : (circleNonnegativeSmoothProjection
      (smoothSectionMul FourierCircleLine φ hφ u)).val z 0 =
      -fourierCoeff (fun x ↦ v.val (AddCircle.homeomorphCircle' x) 0) (-1) := by
    calc
      _ = -((circleNonnegativeSmoothProjection (M v)).val z 0 -
          (z : ℂ) * (circleNonnegativeSmoothProjection v).val z 0) := by
        rw [← hev]
        change (z : ℂ) * (circleNonnegativeSmoothProjection v).val z 0 -
          (circleNonnegativeSmoothProjection (M v)).val z 0 = _
        ring
      _ = _ := congrArg Neg.neg hcomm
  -- The negative first coefficient is integration against the original positive character.
  have hchar (x : AddCircle (2 * Real.pi)) :
      (AddCircle.homeomorphCircle' x : ℂ) = fourier 1 x := by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      rw [AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp, fourier_coe_apply]
      congr 1
      push_cast
      field_simp
  have hcoeff : fourierCoeff (fun x ↦ v.val (AddCircle.homeomorphCircle' x) 0) (-1) =
      ∫ w, (w : ℂ) * v.val w 0 ∂fourierCircleMeasure := by
    have hcont : Continuous (fun w : Circle ↦ (w : ℂ) * v.val w 0) :=
      continuous_subtype_val.mul (contMDiff_fourierCircleSectionCoordinate v).continuous
    unfold fourierCircleMeasure
    rw [integral_map AddCircle.homeomorphCircle'.continuous.measurable.aemeasurable
      hcont.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with x
    change fourier (-(-1)) x * v.val (AddCircle.homeomorphCircle' x) 0 = _
    rw [hchar]
    norm_num
  rw [heval, hcoeff, ← integral_neg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  change k z w * u.val w 0 = ψ z * (-((w : ℂ) * (γ w * u.val w 0)))
  dsimp only [k, γ]
  by_cases hw : w = z
  · subst w
    rw [image_eq_zero_of_notMem_tsupport hz]
    simp
  · have hne : (z : ℂ) - (w : ℂ) ≠ 0 := by
      intro hh
      exact hw (Subtype.ext (sub_eq_zero.mp hh).symm)
    have hden : (1 : ℂ) - (z : ℂ) / (w : ℂ) ≠ 0 := by
      intro hh
      have he : (z : ℂ) / (w : ℂ) = 1 := (sub_eq_zero.mp hh).symm
      exact hw (Subtype.ext ((div_eq_one_iff_eq w.coe_ne_zero).mp he).symm)
    have hdeneq : (1 : ℂ) - (z : ℂ) / (w : ℂ) = -((z : ℂ) - (w : ℂ)) / (w : ℂ) := by
      field_simp
      ring
    rw [hdeneq]
    field_simp

/-- ASI p.525: the same smooth Fourier projection is a global PDO of order zero. -/
theorem isPseudodifferentialOperator_circleNonnegativeSmoothProjection :
    IsPseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0
      circleNonnegativeSmoothProjection := by
  -- First realize each double localization in its original native chart.
  have hlocal := isPseudodifferentialOperator_circleLocalizedProjection
    circleNonnegativeSmoothProjection circleSmoothToFourierL2_nonnegativeProjection
  -- Glue these exact native pieces using the original finite partition.
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  let S := pseudodifferentialSpace (n := 1) (r := 1) (q := 1)
    FourierCircleLine FourierCircleLine fourierCircleMeasure 0
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := 1) (r := 1) FourierCircleLine
  let φ (j : Fin A.size) (z : Circle) : ℂ := A.cutoff j z
  have hφ (j : Fin A.size) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (φ j) :=
    Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)
  let M (j : Fin A.size) :=
    smoothSectionMul (n := 1) (r := 1) FourierCircleLine (φ j) (hφ j)
  have hφsupport (j : Fin A.size) : tsupport (φ j) ⊆ tsupport (A.cutoff j) :=
    tsupport_comp_subset (g := Complex.ofReal) rfl (A.cutoff j)
  -- Around each input partition support, choose an output cutoff equal to one
  -- on a whole neighborhood, still inside the same original native chart.
  have hpiece (j : Fin A.size) : circleNonnegativeSmoothProjection.comp (M j) ∈ S := by
    let K := tsupport (A.cutoff j)
    let U := (A.chart j).source
    have hKU : K ⊆ U := fun z hz ↦ (A.support_subset j hz).1
    obtain ⟨V, hVo, hKV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure
      (A.compact_support j) (A.chart j).open_source hKU
    obtain ⟨W, hWo, hVW, hWU, _hcW⟩ := exists_open_between_and_isCompact_closure
      hcV (A.chart j).open_source hVU
    obtain ⟨β, hβ, _hβrange, hsβ, hβone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff I hWo isClosed_closure hVW
    let ψ (z : Circle) : ℂ := β z
    have hψ : ContMDiff I 𝓘(ℝ, ℂ) ∞ ψ := Complex.ofRealCLM.contMDiff.comp hβ
    have hψsupport : tsupport ψ ⊆ U := by
      apply (tsupport_comp_subset (g := Complex.ofReal) rfl β).trans
      change closure (support β) ⊆ U
      rw [hsβ]
      exact hWU
    let χ (z : Circle) : ℂ := 1 - ψ z
    have hχ : ContMDiff I 𝓘(ℝ, ℂ) ∞ χ := contMDiff_const.sub hψ
    have hdis : Disjoint (tsupport (φ j)) (tsupport χ) := by
      apply Set.disjoint_left.mpr
      intro z hz hzχ
      have hzV := hKV (hφsupport j hz)
      have hzero : χ =ᶠ[𝓝 z] 0 := by
        filter_upwards [hVo.mem_nhds hzV] with w hw
        have hone := (hβone w).mp (subset_closure hw)
        simp [χ, ψ, hone]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hzχ
    have hnear := hlocal (A.chart j) (A.chart_mem_atlas j) (φ j) ψ (hφ j) hψ
      ((hφsupport j).trans hKU) hψsupport
    have hfar := isSmoothingOperator_circleProjection_offDiagonal
      (φ j) χ (hφ j) hχ hdis
    have hsum := S.add_mem hnear
      (IsSmoothingOperator.isPseudodifferentialOperator 0 _ hfar)
    -- The two output multipliers add to one on the same intermediate section.
    convert hsum using 1
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext z
    change (circleNonnegativeSmoothProjection (M j u)).val z =
      ψ z • (circleNonnegativeSmoothProjection (M j u)).val z +
        χ z • (circleNonnegativeSmoothProjection (M j u)).val z
    rw [← add_smul]
    simp only [χ, add_sub_cancel, one_smul]
  -- The original partition identity decomposes the input exactly. Linearity
  -- then reconstructs the original projection as the finite sum of these pieces.
  have hinput : (∑ j, M j) = LinearMap.id := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.sum_apply, LinearMap.id_apply]
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ j, (A.cutoff j z : ℂ) • u.val z) = u.val z
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_cutoff, Complex.ofReal_one, one_smul]
  have hsum : (∑ j, circleNonnegativeSmoothProjection.comp (M j)) =
      circleNonnegativeSmoothProjection := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, ← map_sum]
    have hu := congrArg (fun L ↦ L u) hinput
    simp only [LinearMap.sum_apply, LinearMap.id_apply] at hu
    rw [hu]
  rw [← hsum]
  exact S.sum_mem (fun j _ ↦ hpiece j)

/-- The original projection packaged in the existing zero-order PDO structure. -/
def circleNonnegativeProjectionPDO :
    PseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0 where
  toLinearMap := circleNonnegativeSmoothProjection
  isPseudodifferentialOperator :=
    isPseudodifferentialOperator_circleNonnegativeSmoothProjection

/-- ASI p.525: multiplication and addition make the same source operator a zero-order PDO. -/
theorem isPseudodifferentialOperator_circleFourierSmoothOperator :
    IsPseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0 circleFourierSmoothOperator := by
  -- Use the same coordinate multiplier and the previously identified smooth projection.
  let hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle ↦ (z : ℂ)) := contMDiff_coe_sphere
  let M := smoothSectionMul (n := 1) (r := 1) (M := Circle) FourierCircleLine
    (fun z : Circle ↦ (z : ℂ)) hf
  have hM : IsPseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0 M :=
    isPseudodifferentialOperator_smoothSectionMul _ hf
  have hP := isPseudodifferentialOperator_circleNonnegativeSmoothProjection
  have hcomp : IsPseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0
      (M.comp circleNonnegativeSmoothProjection) := by
    simpa only [zero_add] using
      IsPseudodifferentialOperator.comp M circleNonnegativeSmoothProjection hM hP
  -- The fixed order-zero space is a submodule, so the complementary projection and
  -- the displayed sum retain their literal section maps and the same Haar density.
  let S := pseudodifferentialSpace (n := 1) (r := 1) (q := 1)
    FourierCircleLine FourierCircleLine fourierCircleMeasure 0
  exact S.add_mem hcomp (S.sub_mem (isPseudodifferentialOperator_id fourierCircleMeasure) hP)

/-- The source operator packaged with its established local PDO representation. -/
def circleFourierPDO : PseudodifferentialOperator (n := 1) (r := 1) (q := 1)
    FourierCircleLine FourierCircleLine fourierCircleMeasure 0 where
  toLinearMap := circleFourierSmoothOperator
  isPseudodifferentialOperator := isPseudodifferentialOperator_circleFourierSmoothOperator

/-- The projection's actual degree-zero data, using the positive angular cotangent direction. -/
def circleNonnegativePrincipalSymbol :
    GlobalSymbolFunction (n := 1) FourierCircleLine FourierCircleLine :=
  fun z ξ ↦ if 0 < circleCovectorCoordinate z ξ then
    ContinuousLinearMap.id ℂ (FourierCircleLine z) else 0

/-- The two constant projection branches are smooth on the punctured cotangent bundle. -/
theorem isSmoothOffZeroGlobalSymbol_circleNonnegativePrincipalSymbol :
    IsSmoothOffZeroGlobalSymbol (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine circleNonnegativePrincipalSymbol := by
  /- The angular vector field is smooth and nowhere zero. Every nonzero
  covector has nonzero angular coefficient, so each point has a neighborhood
  of fixed coefficient sign. There the branch is the constant identity or
  zero in the global line frame. Smooth changes of frame and chart preserve
  this conclusion in every chart required by the original predicate. -/
  intro c hc e f _ _ p hp
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  let P := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
  have hcm : c ∈ IsManifold.maximalAtlas I ∞ Circle :=
    IsManifold.subset_maximalAtlas (I := I) hc
  -- The original inverse chart and differential give the native cotangent coordinate map.
  have hbase : ContMDiffAt 𝓘(ℝ, P) I ∞ (fun z ↦ c.symm z.1) p :=
    (contMDiffAt_symm_of_mem_maximalAtlas hcm hp.1.1.1).comp p
      contDiffAt_fst.contMDiffAt
  have hd := ((contMDiffAt_of_mem_maximalAtlas hcm (c.map_target hp.1.1.1)).mfderiv_const
    (m := (∞ : WithTop ℕ∞)) (by simp)).comp p hbase
  have hinner : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, CotangentModel 1) ∞
      (fun z ↦ innerSL ℝ z.2) p :=
    (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp p contDiffAt_snd.contMDiffAt
  have hmap : ContMDiffAt 𝓘(ℝ, P) (I.prod 𝓘(ℝ, CotangentModel 1)) ∞
      (fun z ↦ (⟨c.symm z.1, covectorFromChart c (c.symm z.1) z.2⟩ :
        CotangentTotalSpace)) p := by
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨hbase, ?_⟩
    apply (hinner.clm_comp hd).congr_of_eventuallyEq
    filter_upwards with z
    ext v
    simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Function.id_def, ContinuousLinearMap.comp_apply, I]
    rfl
  let a (z : P) := circleCovectorCoordinate (c.symm z.1)
    (covectorFromChart c (c.symm z.1) z.2)
  have ha : ContinuousAt a p := by
    have h := (continuous_snd.comp circleCotangentTrivialization.continuous).continuousAt.comp
      hmap.continuousAt
    simpa only [Function.comp_def, circleCotangentTrivialization_apply] using h
  have hne : a p ≠ 0 := by
    intro hz
    have hzero := (circleCovectorCoordinate_eq_zero_iff _ _).mp hz
    have hi := covectorInChart_covectorFromChart c hc (c.symm p.1)
      (c.map_target hp.1.1.1) p.2
    rw [hzero] at hi
    have hzcoord : covectorInChart c (c.symm p.1) 0 = 0 := by
      ext j
      rfl
    exact hp.2 (hi.symm.trans hzcoord)
  -- Away from zero, continuity fixes the sign on a neighborhood of the original covector.
  have hid := ((isGlobalSymbol_globalSymbolId
    (E := FourierCircleLine) (n := 1) (r := 1)) c hc e f).1
  have hidAt := hid.contDiffAt
    (((isOpen_symbolChartDomain FourierCircleLine FourierCircleLine c e f).prod
      isOpen_univ).mem_nhds ⟨hp.1, Set.mem_univ _⟩)
  apply ContDiffAt.contDiffWithinAt
  by_cases hpos : 0 < a p
  · apply hidAt.congr_of_eventuallyEq
    filter_upwards [ha (Ioi_mem_nhds hpos)] with z hz
    simp only [Function.uncurry, globalSymbolInChart, circleNonnegativePrincipalSymbol,
      globalSymbolId, show 0 < circleCovectorCoordinate (c.symm z.1)
        (covectorFromChart c (c.symm z.1) z.2) from hz, ite_true]
  · have hneg : a p < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
    apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin 1) →L[ℂ]
      EuclideanSpace ℂ (Fin 1)))).congr_of_eventuallyEq
    filter_upwards [ha (Iio_mem_nhds hneg)] with z hz
    simp only [Function.uncurry, globalSymbolInChart, circleNonnegativePrincipalSymbol,
      show ¬ 0 < circleCovectorCoordinate (c.symm z.1)
        (covectorFromChart c (c.symm z.1) z.2) from not_lt_of_ge hz.le,
      ite_false, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- Positive covector scaling preserves the two projection branches. -/
theorem isHomogeneousGlobalSymbol_circleNonnegativePrincipalSymbol :
    IsHomogeneousGlobalSymbol (n := 1) FourierCircleLine FourierCircleLine 0
      circleNonnegativePrincipalSymbol := by
  /- Evaluation on the same angular tangent vector is real-linear in ξ.
  Multiplication by a positive real number leaves its sign unchanged and
  the degree-zero real scaling factor is one. -/
  intro z ξ _ t ht
  -- Evaluation on the actual angular tangent is real linear in the original covector.
  have hsign : 0 < circleCovectorCoordinate z (t • ξ) ↔
      0 < circleCovectorCoordinate z ξ := by
    change 0 < t * ξ (circleAngularTangent z) ↔ 0 < ξ (circleAngularTangent z)
    exact mul_pos_iff_of_pos_left ht
  simp only [circleNonnegativePrincipalSymbol, hsign, Real.rpow_zero, Complex.ofReal_one,
    one_smul]

/-- The displayed projection data in the existing homogeneous-symbol space. -/
def circleNonnegativeHomogeneousSymbol :
    homogeneousGlobalSymbolSpace (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine 0 :=
  ⟨circleNonnegativePrincipalSymbol,
    isSmoothOffZeroGlobalSymbol_circleNonnegativePrincipalSymbol,
    isHomogeneousGlobalSymbol_circleNonnegativePrincipalSymbol⟩

/-- The actual projection principal quotient is represented by its positive/negative branches. -/
theorem principalSymbol_circleNonnegativeProjectionPDO
    (R : QuantizationPresentation (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine) :
    circleNonnegativeProjectionPDO.principalSymbol =
      globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0
        (R.regularizedSymbol 0 circleNonnegativePrincipalSymbol
          isSmoothOffZeroGlobalSymbol_circleNonnegativePrincipalSymbol
          isHomogeneousGlobalSymbol_circleNonnegativePrincipalSymbol) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := 1) (r := 1) FourierCircleLine
  let φ (j : Fin A.size) (z : Circle) : ℂ := A.cutoff j z
  have hφ (j : Fin A.size) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (φ j) :=
    Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)
  let M (j : Fin A.size) :=
    smoothSectionMul (n := 1) (r := 1) FourierCircleLine (φ j) (hφ j)
  have hφsupport (j : Fin A.size) : tsupport (φ j) ⊆ tsupport (A.cutoff j) :=
    tsupport_comp_subset (g := Complex.ofReal) rfl (A.cutoff j)
  -- Multiply the original homogeneous data by the actual input partition.
  have has (j : Fin A.size) : IsSmoothOffZeroGlobalSymbol (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine
      (fun z ξ ↦ φ j z • circleNonnegativePrincipalSymbol z ξ) := by
    intro c hc e f _ _ z hz
    have hcm := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
    have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hcm hz.1.1.1).comp z
      contDiffAt_fst.contMDiffAt
    have hweight := ((hφ j).contMDiffAt.comp z hbase).contDiffAt
    have hopen := (isOpen_symbolChartDomain FourierCircleLine FourierCircleLine c e f).prod
      (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))))
    have ha := (isSmoothOffZeroGlobalSymbol_circleNonnegativePrincipalSymbol c hc e f).contDiffAt
      (hopen.mem_nhds hz)
    apply ContDiffAt.contDiffWithinAt
    apply (hweight.smul ha).congr_of_eventuallyEq
    filter_upwards with w
    ext v
    simp [Function.uncurry, globalSymbolInChart]
  have hah (j : Fin A.size) : IsHomogeneousGlobalSymbol (n := 1)
      FourierCircleLine FourierCircleLine 0
      (fun z ξ ↦ φ j z • circleNonnegativePrincipalSymbol z ξ) := by
    intro z ξ hξ t ht
    dsimp only
    rw [isHomogeneousGlobalSymbol_circleNonnegativePrincipalSymbol z ξ hξ t ht]
    exact smul_comm _ _ _
  let a (j : Fin A.size) : homogeneousGlobalSymbolSpace (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine 0 :=
    ⟨fun z ξ ↦ φ j z • circleNonnegativePrincipalSymbol z ξ, has j, hah j⟩
  have hpiece (j : Fin A.size) :
      ∃ (L : PseudodifferentialPiece (n := 1) (r := 1) (q := 1)
          FourierCircleLine FourierCircleLine 0)
        (K : SmoothKernel (n := 1) (r := 1) (q := 1) FourierCircleLine FourierCircleLine),
        K.toLinearMap fourierCircleMeasure = circleNonnegativeSmoothProjection.comp (M j) -
          L.toLinearMap ∧
        IsGlobalSymbol (n := 1) (r := 1) (q := 1)
          FourierCircleLine FourierCircleLine (-1)
          (L.globalSymbolFunction - R.regularizedSymbolFunction (a j).val) := by
    let K := tsupport (A.cutoff j)
    let U := (A.chart j).source
    have hKU : K ⊆ U := fun z hz ↦ (A.support_subset j hz).1
    obtain ⟨V, hVo, hKV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure
      (A.compact_support j) (A.chart j).open_source hKU
    obtain ⟨W, hWo, hVW, hWU, _hcW⟩ := exists_open_between_and_isCompact_closure
      hcV (A.chart j).open_source hVU
    obtain ⟨β, hβ, _hβrange, hsβ, hβone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff I hWo isClosed_closure hVW
    let ψ (z : Circle) : ℂ := β z
    have hψ : ContMDiff I 𝓘(ℝ, ℂ) ∞ ψ := Complex.ofRealCLM.contMDiff.comp hβ
    have hψsupport : tsupport ψ ⊆ U := by
      apply (tsupport_comp_subset (g := Complex.ofReal) rfl β).trans
      change closure (support β) ⊆ U
      rw [hsβ]
      exact hWU
    let χ (z : Circle) : ℂ := 1 - ψ z
    have hχ : ContMDiff I 𝓘(ℝ, ℂ) ∞ χ := contMDiff_const.sub hψ
    have hdis : Disjoint (tsupport (φ j)) (tsupport χ) := by
      apply Set.disjoint_left.mpr
      intro z hz hzχ
      have hzV := hKV (hφsupport j hz)
      have hzero : χ =ᶠ[𝓝 z] 0 := by
        filter_upwards [hVo.mem_nhds hzV] with w hw
        have hone := (hβone w).mp (subset_closure hw)
        simp [χ, ψ, hone]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hzχ
    obtain ⟨L, hL, hsymbol⟩ := exists_circleLocalizedProjection_piece
      circleNonnegativeSmoothProjection circleSmoothToFourierL2_nonnegativeProjection
      (A.chart j) (A.chart_mem_atlas j) (φ j) ψ (hφ j) hψ
      ((hφsupport j).trans hKU) hψsupport
    obtain ⟨S, hS⟩ := isSmoothingOperator_circleProjection_offDiagonal
      (φ j) χ (hφ j) hχ hdis
    refine ⟨L, S, ?_, hsymbol R (a j) ?_⟩
    · rw [hS, hL]
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext z
      change χ z • (circleNonnegativeSmoothProjection (M j u)).val z =
        (circleNonnegativeSmoothProjection (M j u)).val z -
          ψ z • (circleNonnegativeSmoothProjection (M j u)).val z
      simp only [χ, sub_smul, one_smul]
    · intro z ξ
      change φ j z • circleNonnegativePrincipalSymbol z ξ =
        (ψ z * φ j z) • circleNonnegativePrincipalSymbol z ξ
      by_cases hz : φ j z = 0
      · simp only [hz, mul_zero, zero_smul]
      · have hone : ψ z = 1 := by
          change (β z : ℂ) = 1
          rw [(hβone z).mp (subset_closure (hKV (hφsupport j (subset_closure hz))))]
          exact Complex.ofReal_one
        rw [hone, one_mul]
  choose L K hK hsymbol using hpiece
  -- Sum the actual off-diagonal smooth kernels using the same original density.
  let S : SmoothKernel (n := 1) (r := 1) (q := 1) FourierCircleLine FourierCircleLine := {
    toFun := fun x y ↦ ∑ j, (K j).toFun x y
    isSmooth := by
      intro e f _ _
      have hsum : ContMDiffOn (I.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) ∞
          (fun z : Circle × Circle ↦ ∑ j,
            kernelInFrames FourierCircleLine FourierCircleLine (K j).toFun e f z)
          (f.baseSet ×ˢ e.baseSet) := by
        apply contMDiffOn_finsetSum
        intro j _
        exact (K j).isSmooth e f
      apply hsum.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro v
      simp [kernelInFrames, sum_apply, map_sum] }
  have hS : S.toLinearMap fourierCircleMeasure = ∑ j, (K j).toLinearMap fourierCircleMeasure := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    change (∫ y, (∑ j, (K j).toFun x y) (u.val y) ∂fourierCircleMeasure) =
      (∑ j, ((K j).toLinearMap fourierCircleMeasure u).val x)
    simp only [sum_apply]
    exact integral_finsetSum Finset.univ (fun j _ ↦ (K j).integrable_apply fourierCircleMeasure u x)
  have hinput : (∑ j, M j) = LinearMap.id := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.sum_apply, LinearMap.id_apply]
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ j, (A.cutoff j z : ℂ) • u.val z) = u.val z
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_cutoff, Complex.ofReal_one, one_smul]
  have hsum : (∑ j, circleNonnegativeSmoothProjection.comp (M j)) =
      circleNonnegativeSmoothProjection := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, ← map_sum]
    have hu := congrArg (fun Q ↦ Q u) hinput
    simp only [LinearMap.sum_apply, LinearMap.id_apply] at hu
    rw [hu]
  have hrepresentation : IsSmoothingOperator fourierCircleMeasure
      (circleNonnegativeProjectionPDO.toLinearMap - ∑ j, (L j).toLinearMap) := by
    refine ⟨S, ?_⟩
    rw [hS]
    simp_rw [hK]
    rw [Finset.sum_sub_distrib, hsum]
    rfl
  rw [circleNonnegativeProjectionPDO.principalSymbol_eq_of_representation A.size L hrepresentation]
  apply (globalPrincipalSymbolClass_eq_iff FourierCircleLine FourierCircleLine 0 _ _).mpr
  -- The partition sums to one on the same original fibers, including the cutoff convention.
  have hreg : (∑ j, R.regularizedSymbolFunction (a j).val) =
      R.regularizedSymbolFunction circleNonnegativePrincipalSymbol := by
    funext z ξ
    simp only [Finset.sum_apply, QuantizationPresentation.regularizedSymbolFunction]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    change (∑ j, ((R.patch k).weight z * highFrequencyCutoff 1
      (covectorInChart (R.patch k).chart z ξ) : ℝ) •
        (φ j z • circleNonnegativePrincipalSymbol z ξ)) = _
    rw [← Finset.smul_sum, ← Finset.sum_smul]
    have hφsum : ∑ j, φ j z = 1 := by
      change (∑ j, (A.cutoff j z : ℂ)) = 1
      rw [← Complex.ofReal_sum, A.sum_cutoff, Complex.ofReal_one]
    rw [hφsum, one_smul]
    rfl
  have herror := (globalSymbolSpace (n := 1) (r := 1) (q := 1)
    FourierCircleLine FourierCircleLine (-1)).sum_mem (t := Finset.univ)
      (fun j _ ↦ hsymbol j)
  rw [Finset.sum_sub_distrib, hreg] at herror
  change IsGlobalSymbol (n := 1) (r := 1) (q := 1)
    FourierCircleLine FourierCircleLine (-1)
    (∑ j, (L j).globalSymbolFunction - R.regularizedSymbolFunction
      circleNonnegativePrincipalSymbol) at herror
  simpa only [zero_sub, Submodule.coe_sum, PseudodifferentialPiece.globalSymbol,
    QuantizationPresentation.regularizedSymbol] using herror

/-- ASI (8.2): the actual symbol is z on positive covectors and one on negative covectors. -/
def circleFourierPrincipalSymbol :
    GlobalSymbolFunction (n := 1) FourierCircleLine FourierCircleLine :=
  fun z ξ ↦ (if 0 < circleCovectorCoordinate z ξ then (z : ℂ) else 1) •
    ContinuousLinearMap.id ℂ (FourierCircleLine z)

/-- The displayed source-operator branches are smooth off the original zero section. -/
theorem isSmoothOffZeroGlobalSymbol_circleFourierPrincipalSymbol :
    IsSmoothOffZeroGlobalSymbol (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine circleFourierPrincipalSymbol := by
  /- On each open sign component, the formula is multiplication by the
  smooth original complex coordinate z or the identity. The angular
  coefficient has no zero on a nonzero covector, so these are disjoint open
  components and no matching across ξ=0 is required. Check in the existing
  global line frame, then transport to every valid smooth frame and chart. -/
  intro c hc e f _ _ p hp
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  have hcm := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hcm hp.1.1.1).comp p
    contDiffAt_fst.contMDiffAt
  have hz : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 1) ×
      EuclideanSpace ℝ (Fin 1) ↦ ((c.symm z.1 : Circle) : ℂ) - 1) p :=
    ((contMDiff_coe_sphere.contMDiffAt.comp p hbase).contDiffAt).sub contDiffAt_const
  have hproj := isSmoothOffZeroGlobalSymbol_circleNonnegativePrincipalSymbol c hc e f
  have hopen := (isOpen_symbolChartDomain FourierCircleLine FourierCircleLine c e f).prod
    (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))))
  have hprojAt := hproj.contDiffAt (hopen.mem_nhds hp)
  have hid := ((isGlobalSymbol_globalSymbolId
    (E := FourierCircleLine) (n := 1) (r := 1)) c hc e f).1
  have hidAt := hid.contDiffAt
    (((isOpen_symbolChartDomain FourierCircleLine FourierCircleLine c e f).prod
      isOpen_univ).mem_nhds ⟨hp.1, Set.mem_univ _⟩)
  -- The original symbol is (z-1) times the smooth projection branch plus the identity.
  apply ContDiffAt.contDiffWithinAt
  apply ((hz.smul hprojAt).add hidAt).congr_of_eventuallyEq
  filter_upwards with w
  ext v
  by_cases hpos : 0 < circleCovectorCoordinate (c.symm w.1)
      (covectorFromChart c (c.symm w.1) w.2)
  · simp [Function.uncurry, globalSymbolInChart, circleFourierPrincipalSymbol,
      circleNonnegativePrincipalSymbol, globalSymbolId, hpos, sub_smul]
  · simp [Function.uncurry, globalSymbolInChart, circleFourierPrincipalSymbol,
      circleNonnegativePrincipalSymbol, globalSymbolId, hpos]

/-- The source-operator symbol has degree zero under positive cotangent scaling. -/
theorem isHomogeneousGlobalSymbol_circleFourierPrincipalSymbol :
    IsHomogeneousGlobalSymbol (n := 1) FourierCircleLine FourierCircleLine 0
      circleFourierPrincipalSymbol := by
  /- Positive scaling preserves the sign of evaluation on the original
  angular vector. The scalar z depends only on the unchanged base point,
  and the required degree-zero real factor is one. -/
  intro z ξ _ t ht
  -- Positive real scaling fixes the branch and leaves the original base coordinate unchanged.
  have hsign : 0 < circleCovectorCoordinate z (t • ξ) ↔
      0 < circleCovectorCoordinate z ξ := by
    change 0 < t * ξ (circleAngularTangent z) ↔ 0 < ξ (circleAngularTangent z)
    exact mul_pos_iff_of_pos_left ht
  simp only [circleFourierPrincipalSymbol, hsign, Real.rpow_zero, Complex.ofReal_one,
    one_smul]

/-- The displayed source symbol in the original degree-zero homogeneous space. -/
def circleFourierHomogeneousSymbol :
    homogeneousGlobalSymbolSpace (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine 0 :=
  ⟨circleFourierPrincipalSymbol, isSmoothOffZeroGlobalSymbol_circleFourierPrincipalSymbol,
    isHomogeneousGlobalSymbol_circleFourierPrincipalSymbol⟩

/-- The actual source operator has precisely the two-branch symbol of ASI equation (8.2). -/
theorem principalSymbol_circleFourierPDO
    (R : QuantizationPresentation (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine) :
    circleFourierPDO.principalSymbol =
      globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0
        (R.regularizedSymbol 0 circleFourierPrincipalSymbol
          isSmoothOffZeroGlobalSymbol_circleFourierPrincipalSymbol
          isHomogeneousGlobalSymbol_circleFourierPrincipalSymbol) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  let Y := EuclideanSpace ℂ (Fin 1)
  -- First identify the actual scalar and identity multipliers in the original bundle frames.
  have hmap (f : Circle → ℂ) (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) :
      IsSmoothBundleMap (n := 1) (r := 1) (q := 1)
        (fun z ↦ f z • (LinearMap.id : FourierCircleLine z →ₗ[ℂ] FourierCircleLine z)) := by
    intro e he g hg j
    let := he
    let := hg
    obtain rfl := Bundle.Trivial.eq_trivialization Circle Y e
    obtain rfl := Bundle.Trivial.eq_trivialization Circle Y g
    have hsmul : ContDiff ℝ ∞ (fun p : ℂ × Y ↦ p.1 • p.2) := contDiff_smul
    have h := hsmul.contMDiff.comp
      (hf.prodMk_space (contMDiff_const (c := EuclideanSpace.single j 1)))
    apply h.contMDiffOn.congr
    intro z _
    rw [Bundle.Trivial.symmL_trivialization]
    rfl
  let f (z : Circle) : ℂ := z
  have hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f := contMDiff_coe_sphere
  let m (z : Circle) : FourierCircleLine z →ₗ[ℂ] FourierCircleLine z :=
    f z • LinearMap.id
  let i (z : Circle) : FourierCircleLine z →ₗ[ℂ] FourierCircleLine z :=
    (1 : ℂ) • LinearMap.id
  let M := smoothBundleMapOperator (μ := fourierCircleMeasure) m (hmap f hf)
  let Q := smoothBundleMapOperator (μ := fourierCircleMeasure) i (hmap (fun _ ↦ 1) contMDiff_const)
  obtain ⟨b, hb, hMb⟩ := exists_homogeneousSymbol_smoothBundleMap
    (μ := fourierCircleMeasure) m (hmap f hf)
  obtain ⟨aId, haId, hQid⟩ := exists_homogeneousSymbol_smoothBundleMap
    (μ := fourierCircleMeasure) i (hmap (fun _ ↦ 1) contMDiff_const)
  have hbval (z : Circle) (ξ : CotangentFiber (n := 1) z) :
      b.val z ξ = (z : ℂ) • ContinuousLinearMap.id ℂ (FourierCircleLine z) := by
    apply ContinuousLinearMap.ext
    intro v
    exact hb z ξ v
  have hidval (z : Circle) (ξ : CotangentFiber (n := 1) z) :
      aId.val z ξ = ContinuousLinearMap.id ℂ (FourierCircleLine z) := by
    apply ContinuousLinearMap.ext
    intro v
    change aId.val z ξ v = v
    simpa only [i, LinearMap.smul_apply, LinearMap.id_apply, one_smul] using haId z ξ v
  -- The specified homogeneous product is computed before applying the exact-order composition law.
  let aComp := circleFourierHomogeneousSymbol + circleNonnegativeHomogeneousSymbol - aId
  let S : PseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0 := {
    toLinearMap := M.toLinearMap.comp circleNonnegativeProjectionPDO.toLinearMap
    isPseudodifferentialOperator := by
      simpa only [zero_add] using IsPseudodifferentialOperator.comp M.toLinearMap
        circleNonnegativeProjectionPDO.toLinearMap M.isPseudodifferentialOperator
        circleNonnegativeProjectionPDO.isPseudodifferentialOperator }
  have hComp : S.principalSymbol = globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0
      (R.regularizedSymbol 0 aComp.val aComp.property.1 aComp.property.2) := by
    apply PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp R R R
      circleNonnegativeHomogeneousSymbol b aComp circleNonnegativeProjectionPDO M S
      (principalSymbol_circleNonnegativeProjectionPDO R) (hMb R) rfl
    intro z ξ _
    change circleFourierPrincipalSymbol z ξ + circleNonnegativePrincipalSymbol z ξ -
      aId.val z ξ = (b.val z ξ).comp (circleNonnegativePrincipalSymbol z ξ)
    rw [hbval, hidval]
    by_cases hpos : 0 < circleCovectorCoordinate z ξ
    · simp [circleFourierPrincipalSymbol, circleNonnegativePrincipalSymbol, hpos]
    · simp [circleFourierPrincipalSymbol, circleNonnegativePrincipalSymbol, hpos]
  -- Reconstruct the very same section operator M_z Π₊ + (I - Π₊), then use symbol additivity.
  have hM : M.toLinearMap = smoothSectionMul FourierCircleLine f hf := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    rfl
  have hQ : Q.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext z
    change (1 : ℂ) • u.val z = u.val z
    exact one_smul _ _
  let T := S.add (Q.add (circleNonnegativeProjectionPDO.smul (-1)))
  have hT : circleFourierPDO.toLinearMap = T.toLinearMap := by
    change circleFourierSmoothOperator = M.toLinearMap.comp circleNonnegativeSmoothProjection +
      (Q.toLinearMap + (-1 : ℂ) • circleNonnegativeSmoothProjection)
    rw [hM, hQ, neg_one_smul]
    rfl
  rw [circleFourierPDO.principalSymbol_eq_of_toLinearMap_eq fourierCircleMeasure T hT]
  change (S.add (Q.add (circleNonnegativeProjectionPDO.smul (-1)))).principalSymbol = _
  rw [PseudodifferentialOperator.principalSymbol_add,
    PseudodifferentialOperator.principalSymbol_add,
    PseudodifferentialOperator.principalSymbol_smul, hComp, hQid R,
    principalSymbol_circleNonnegativeProjectionPDO R]
  -- Linear regularization cancels the auxiliary identity and projection terms in the quotient.
  let reg (a : homogeneousGlobalSymbolSpace (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine 0) :
      globalSymbolSpace (n := 1) (r := 1) (q := 1) FourierCircleLine FourierCircleLine 0 :=
    R.regularizedSymbol 0 a.val a.property.1 a.property.2
  change globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0 (reg aComp) +
    (globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0 (reg aId) +
      (-1 : ℂ) • globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0
        (reg circleNonnegativeHomogeneousSymbol)) =
      globalPrincipalSymbolClass FourierCircleLine FourierCircleLine 0
        (reg circleFourierHomogeneousSymbol)
  rw [← map_smul, ← map_add, ← map_add]
  congr 1
  apply Subtype.ext
  funext z ξ
  change R.regularizedSymbolFunction aComp.val z ξ +
    (R.regularizedSymbolFunction aId.val z ξ + (-1 : ℂ) •
      R.regularizedSymbolFunction circleNonnegativeHomogeneousSymbol.val z ξ) =
    R.regularizedSymbolFunction circleFourierHomogeneousSymbol.val z ξ
  have hlin : aComp.val = circleFourierHomogeneousSymbol.val +
      circleNonnegativeHomogeneousSymbol.val + (-1 : ℂ) • aId.val := by
    simp only [aComp, sub_eq_add_neg, Submodule.coe_add, Submodule.coe_neg, neg_one_smul]
  rw [hlin, R.regularizedSymbolFunction_add, R.regularizedSymbolFunction_add,
    R.regularizedSymbolFunction_smul]
  simp only [neg_one_smul, Pi.add_apply, Pi.neg_apply]
  abel

/-- Both actual symbol branches are invertible on the original complex line. -/
theorem isEllipticGlobalSymbol_circleFourierPrincipalSymbol :
    IsEllipticGlobalSymbol (n := 1) FourierCircleLine FourierCircleLine
      circleFourierPrincipalSymbol := by
  /- A circle point z has complex norm one, hence is nonzero. Multiplication
  by z therefore has inverse multiplication by its complex conjugate. The
  negative branch is the identity. These inverses establish bijectivity on
  every nonzero covector without a chosen K-class or index assumption. -/
  intro z ξ _
  -- Both branches act on the same original line; a circle point is a nonzero scalar.
  by_cases hpos : 0 < circleCovectorCoordinate z ξ
  · change Function.Bijective (fun v : FourierCircleLine z ↦
      (if 0 < circleCovectorCoordinate z ξ then (z : ℂ) else 1) • v)
    simp only [hpos, ite_true]
    exact (LinearEquiv.smulOfNeZero ℂ (FourierCircleLine z) (z : ℂ) z.coe_ne_zero).bijective
  · simp only [circleFourierPrincipalSymbol, hpos, ite_false, one_smul]
    exact Function.bijective_id

/-- The actual Fourier source PDO is elliptic in the preexisting global calculus. -/
theorem isElliptic_circleFourierPDO : circleFourierPDO.IsElliptic := by
  -- The same two-branch representative is invertible on every nonzero original covector.
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := 1) (r := 1) (q := 1)
    (E := FourierCircleLine) (F := FourierCircleLine)
  exact (circleFourierPDO.isElliptic_iff_homogeneous R circleFourierHomogeneousSymbol
    (principalSymbol_circleFourierPDO R)).mpr isEllipticGlobalSymbol_circleFourierPrincipalSymbol

/-- The source PDO has smooth kernel zero and smooth cokernel the constant line, hence index -1. -/
theorem index_circleFourierPDO : circleFourierPDO.toLinearMap.index = -1 := by
  change circleFourierSmoothOperator.index = -1
  classical
  let S := smoothSections (n := 1) (r := 1) FourierCircleLine
  let A : S →ₗ[ℂ] S := circleFourierSmoothOperator
  let P : S →ₗ[ℂ] S := circleNonnegativeSmoothProjection
  let c (u : S) (n : ℤ) : ℂ := fourierCoeff (circleSmoothToFourierL2 u) n
  let scalar (u : S) : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x ↦ u.val (AddCircle.homeomorphCircle' x) 0,
      (contMDiff_fourierCircleSectionCoordinate u).continuous.comp
        AddCircle.homeomorphCircle'.continuous⟩
  have hc (u : S) (n : ℤ) : c u n = fourierCoeff (scalar u) n :=
    fourierCoeff_toLp _ n
  have c_add (u v : S) (n : ℤ) : c (u + v) n = c u n + c v n := by
    dsimp only [c]
    rw [map_add]
    simp only [← fourierBasis_repr, map_add, lp.coeFn_add, Pi.add_apply]
  have c_sub (u v : S) (n : ℤ) : c (u - v) n = c u n - c v n := by
    dsimp only [c]
    rw [map_sub]
    simp only [← fourierBasis_repr, map_sub, lp.coeFn_sub, Pi.sub_apply]
  have hP (u : S) (n : ℤ) : c (P u) n = if 0 ≤ n then c u n else 0 := by
    dsimp only [c, P]
    rw [circleSmoothToFourierL2_nonnegativeProjection,
      circleNonnegativeFourierProjection_fourierCoeff]
  have hA (u : S) (n : ℤ) : c (A u) n =
      if n < 0 then c u n else if n = 0 then 0 else c u (n - 1) := by
    dsimp only [c, A]
    rw [circleSmoothToFourierL2_fourierOperator, circleFourierIndexOperator_fourierCoeff]
  -- The actual smooth inclusion and the original injective Hilbert operator detect the kernel.
  have hker : A.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro u v huv
    apply circleSmoothToFourierL2_injective
    apply LinearMap.ker_eq_bot.mp ker_circleFourierIndexOperator
    change circleFourierIndexOperator (circleSmoothToFourierL2 u) =
      circleFourierIndexOperator (circleSmoothToFourierL2 v)
    rw [← circleSmoothToFourierL2_fourierOperator, ← circleSmoothToFourierL2_fourierOperator]
    exact congrArg circleSmoothToFourierL2 huv
  -- Multiplication by the inverse character shifts the same Fourier coefficients down by one.
  have hneg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle ↦ ((z⁻¹ : Circle) : ℂ)) :=
    contMDiff_coe_sphere.comp
      (contMDiff_inv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞)
  let N : S →ₗ[ℂ] S := smoothSectionMul FourierCircleLine
    (fun z : Circle ↦ ((z⁻¹ : Circle) : ℂ)) hneg
  have hchar (x : AddCircle (2 * Real.pi)) :
      (AddCircle.homeomorphCircle' x : ℂ) = fourier 1 x := by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      rw [AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp, fourier_coe_apply]
      congr 1
      push_cast
      field_simp
  have hN (u : S) (n : ℤ) : c (N u) n = c u (n + 1) := by
    rw [hc, hc]
    apply integral_congr_ae
    filter_upwards with x
    change fourier (-n) x *
      ((((AddCircle.homeomorphCircle' x)⁻¹ : Circle) : ℂ) *
        u.val (AddCircle.homeomorphCircle' x) 0) = _
    rw [Circle.coe_inv_eq_conj, hchar, ← fourier_neg, ← mul_assoc, ← fourier_add]
    have hn : -n + -1 = -(n + 1) := by omega
    rw [hn]
    rfl
  -- A smooth target with zero constant coefficient has an explicit smooth preimage.
  -- Keep its negative modes and shift back its strictly positive modes.
  have hrange : (A.range : Set S) = {u : S | c u 0 = 0} := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      simp [hA]
    · intro hu
      let v := P (N u) + (u - P u)
      refine ⟨v, ?_⟩
      apply circleSmoothToFourierL2_injective
      apply (fourierBasis (T := 2 * Real.pi)).repr.injective
      apply lp.ext
      funext n
      simp only [fourierBasis_repr]
      change c (A v) n = c u n
      have hv (k : ℤ) : c v k = if k < 0 then c u k else c u (k + 1) := by
        dsimp only [v]
        rw [c_add, c_sub, hP, hN, hP]
        by_cases hk : k < 0
        · simp only [ite_eq_right (show ¬ 0 ≤ k by omega), ite_eq_left hk, sub_zero,
            zero_add]
        · simp only [ite_eq_left (show 0 ≤ k by omega), ite_eq_right hk, sub_self,
            add_zero]
      rw [hA]
      by_cases hn : n < 0
      · rw [ite_eq_left hn, hv, ite_eq_left hn]
      · by_cases hz : n = 0
        · subst n
          simpa using hu.symm
        · rw [ite_eq_right hn, ite_eq_right hz, hv,
            ite_eq_right (show ¬ n - 1 < 0 by omega), sub_add_cancel]
  -- The original constant coefficient is a surjective linear functional on smooth sections.
  let ε : S →ₗ[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 0).toLinearMap.comp
    ((fourierBasis (T := 2 * Real.pi)).repr.toLinearMap.comp circleSmoothToFourierL2)
  have hε (u : S) : ε u = c u 0 := by
    exact fourierBasis_repr (circleSmoothToFourierL2 u) 0
  let oneSection : S :=
    ⟨fun _ ↦ EuclideanSpace.single 0 1, by
      intro e he
      let := he
      obtain rfl := Bundle.Trivial.eq_trivialization Circle (EuclideanSpace ℂ (Fin 1)) e
      exact contMDiff_const.contMDiffOn⟩
  have hone : ε oneSection = 1 := by
    rw [hε, hc]
    change fourierCoeff (fun _ : AddCircle (2 * Real.pi) ↦ (1 : ℂ)) 0 = 1
    simp [fourierCoeff]
  have hsurj : Function.Surjective ε := by
    intro z
    refine ⟨z • oneSection, ?_⟩
    rw [map_smul, hone, smul_eq_mul, mul_one]
  have hrangeKer : A.range = ε.ker := by
    apply SetLike.coe_injective
    rw [hrange]
    ext u
    change c u 0 = 0 ↔ ε u = 0
    rw [hε]
  -- The first isomorphism theorem identifies the actual algebraic cokernel with ℂ.
  let e : (S ⧸ ε.ker) ≃ₗ[ℂ] ℂ := ε.quotKerEquivOfSurjective hsurj
  have hdim : Module.finrank ℂ (S ⧸ A.range) = 1 := by
    rw [hrangeKer, e.finrank_eq]
    exact Module.finrank_self ℂ
  change A.index = -1
  rw [LinearMap.index_eq_finrank_sub, hker, hdim]
  simp


/-- The source's actual homogeneous symbol class in the original compact-support K group. -/
def circleFourierSymbolKClass :
    CompactSupportKZero (CotangentTotalSpace (n := 1) (M := Circle)) :=
  homogeneousSymbolKClass 0 circleFourierHomogeneousSymbol
    isEllipticGlobalSymbol_circleFourierPrincipalSymbol

/-- The original analytic-index homomorphism assigns -1 to this actual Fourier symbol class. -/
theorem analyticIndex_circleFourierSymbolKClass :
    analyticIndex fourierCircleMeasure circleFourierSymbolKClass = -1 := by
  -- The same original PDO and its actual homogeneous K class evaluate under the original index map.
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := 1) (r := 1) (q := 1)
    (E := FourierCircleLine) (F := FourierCircleLine)
  have h := circleFourierPDO.analyticIndex_symbolKClassOfHomogeneous fourierCircleMeasure R
    circleFourierHomogeneousSymbol (principalSymbol_circleFourierPDO R) isElliptic_circleFourierPDO
  change analyticIndex fourierCircleMeasure circleFourierSymbolKClass =
    circleFourierPDO.toLinearMap.index at h
  -- The original smooth Fourier kernel and cokernel computation fixes the sign as minus one.
  exact h.trans index_circleFourierPDO

end AtiyahSinger
