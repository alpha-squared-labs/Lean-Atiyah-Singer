/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FourierCircle
public import Mathlib.Analysis.Fourier.PoissonSummation

import Mathlib.Analysis.PSeries

/-!
# Periodization and the original circle Fourier projection

Public module ID: M0325.

Schwartz periodization is identified with the original normalized period-2π
circle coefficients. The actual nonnegative L² projection therefore has the
expected pointwise positive-frequency series on any specified smooth output.
This comparison keeps the positive covering exp(2πit), the original normalized
Haar measure, and the existing Hilbert projection. It does not use the circle
PDO realization, which consumes these local Fourier identities.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory FourierTransform Asymptotics Filter
open scoped Manifold ContDiff SchwartzMap Topology

/-- A function supported in an exponential chart periodizes to its circle zero extension. -/
theorem circle_eq_tsum_of_tsupport_subset_exp_chart
    (b : OpenPartialHomeomorph ℝ Circle)
    (hb : ∀ t : ℝ, b t = Circle.exp (2 * Real.pi * t))
    (f : ℝ → ℂ) (g : Circle → ℂ) (hf : tsupport f ⊆ b.source)
    (heq : ∀ t ∈ b.source, f t = g (b t))
    (hgzero : ∀ z ∉ b.target, g z = 0) (x : ℝ) :
    g (Circle.exp (2 * Real.pi * x)) = ∑' k : ℤ, f (x + (k : ℝ)) := by
  classical
  -- Every integer translate has the same image under the specified positive covering.
  have hperiod (k : ℤ) : Circle.exp (2 * Real.pi * (x + (k : ℝ))) =
      Circle.exp (2 * Real.pi * x) :=
    Circle.exp_eq_exp.mpr ⟨k, by ring⟩
  by_cases hz : Circle.exp (2 * Real.pi * x) ∈ b.target
  · let y : ℝ := b.symm (Circle.exp (2 * Real.pi * x))
    have hy : y ∈ b.source := b.map_target hz
    have hby : b y = Circle.exp (2 * Real.pi * x) := b.right_inv hz
    -- The actual inverse chart supplies the unique potentially nonzero translate.
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp ((hb y).symm.trans hby)
    have hym : x + (m : ℝ) = y := by
      apply mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0)
      calc
        2 * Real.pi * (x + (m : ℝ)) =
            2 * Real.pi * x + (m : ℝ) * (2 * Real.pi) := by ring
        _ = 2 * Real.pi * y := hm.symm
    have hsum : (∑' k : ℤ, f (x + (k : ℝ))) = f (x + (m : ℝ)) := by
      apply tsum_eq_single m
      intro k hkm
      apply image_eq_zero_of_notMem_tsupport
      intro hk
      have hks : x + (k : ℝ) ∈ b.source := hf hk
      have hsame : x + (k : ℝ) = y := b.injOn hks hy (by
        rw [hb, hperiod, hby])
      have hcast : (k : ℝ) = (m : ℝ) := by linarith
      exact hkm (Int.cast_injective hcast)
    rw [hsum, hym, heq y hy, hby]
  · -- Outside the chart target, both the circle zero extension and every term vanish.
    rw [hgzero _ hz]
    symm
    calc
      (∑' k : ℤ, f (x + (k : ℝ))) = ∑' _ : ℤ, (0 : ℂ) := by
        apply tsum_congr
        intro k
        apply image_eq_zero_of_notMem_tsupport
        intro hk
        have htarget := b.map_source (hf hk)
        rw [hb, hperiod] at htarget
        exact hz htarget
      _ = 0 := tsum_zero

/-- The original normalized circle coefficients of a Schwartz periodization are Fourier samples. -/
theorem fourierCoeff_circleSmoothToFourierL2_of_periodization
    (f : 𝓢(ℝ, ℂ)) (u : smoothSections (n := 1) (r := 1) FourierCircleLine)
    (hperiod : ∀ x : ℝ, u.val (Circle.exp (2 * Real.pi * x)) 0 =
      ∑' k : ℤ, f (x + (k : ℝ))) (n : ℤ) :
    fourierCoeff (circleSmoothToFourierL2 u) n = (𝓕 f) (n : ℝ) := by
  classical
  -- Schwartz decay gives one summable coefficient sequence in the original period-2π basis.
  have hcoeffsum : Summable (fun j : ℤ ↦ (𝓕 f) (j : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun z ↦ u.val (AddCircle.homeomorphCircle' z) 0,
      (contMDiff_fourierCircleSectionCoordinate u).continuous.comp
        AddCircle.homeomorphCircle'.continuous⟩
  let a (j : ℤ) : ℂ := (𝓕 f) (j : ℝ)
  have hseries : Summable (fun j : ℤ ↦ a j •
      (fourier j : C(AddCircle (2 * Real.pi), ℂ))) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourier_norm, mul_one] using hcoeffsum.norm
  let G : C(AddCircle (2 * Real.pi), ℂ) := ∑' j : ℤ, a j • fourier j
  have hG (z : AddCircle (2 * Real.pi)) : G z = ∑' j : ℤ, a j * fourier j z :=
    (ContinuousMap.evalCLM ℂ z).map_tsum hseries
  have hsame : F = G := by
    apply ContinuousMap.ext
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      have hperiodne : 2 * Real.pi ≠ 0 := by positivity
      have hcover : 2 * Real.pi * (t / (2 * Real.pi)) = t :=
        mul_div_cancel₀ _ hperiodne
      have hchar (j : ℤ) : fourier j (t : AddCircle (2 * Real.pi)) =
          fourier j ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
        rw [fourier_coe_apply, fourier_coe_apply]
        push_cast
        congr 1
        ring
      change u.val (Circle.exp t) 0 = G (t : AddCircle (2 * Real.pi))
      rw [← hcover, hperiod, f.tsum_eq_tsum_fourier, hG]
      apply tsum_congr
      intro j
      change (𝓕 f) (j : ℝ) * fourier j _ = a j * fourier j _
      rw [hcover, hchar]
  -- The original Fourier basis functionals compute coefficients of the same uniform sum.
  let L : C(AddCircle (2 * Real.pi), ℂ) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 n).comp
      ((fourierBasis (T := 2 * Real.pi)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ))
  have hL (H : C(AddCircle (2 * Real.pi), ℂ)) : L H = fourierCoeff H n := by
    change (fourierBasis (T := 2 * Real.pi)).repr
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ H) n = _
    rw [fourierBasis_repr, fourierCoeff_toLp]
  have hLc (j : ℤ) : L (a j • fourier j) = if j = n then a j else 0 := by
    rw [hL]
    change fourierCoeff (a j • (fourier j : AddCircle (2 * Real.pi) → ℂ)) n = _
    rw [fourierCoeff.const_smul, fourierCoeff_fourier]
    simp only [Pi.single_apply]
    by_cases h : j = n
    · simp [h]
    · simp [h, Ne.symm h]
  have hresult : fourierCoeff G n = a n := by
    rw [← hL, show G = ∑' j : ℤ, a j • fourier j from rfl, L.map_tsum hseries]
    simp only [hLc, tsum_ite_eq]
  change fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F) n = _
  rw [fourierCoeff_toLp, hsame, hresult]

/-- A specified smooth output of the original Hilbert projection has the positive Fourier series. -/
theorem circleFourierProjection_eq_tsum_of_periodization
    (f : 𝓢(ℝ, ℂ)) (u v : smoothSections (n := 1) (r := 1) FourierCircleLine)
    (hperiod : ∀ x : ℝ, u.val (Circle.exp (2 * Real.pi * x)) 0 =
      ∑' k : ℤ, f (x + (k : ℝ)))
    (hprojection : circleSmoothToFourierL2 v =
      circleNonnegativeFourierProjection (circleSmoothToFourierL2 u)) (x : ℝ) :
    v.val (Circle.exp (2 * Real.pi * x)) 0 =
      ∑' n : ℕ, (Real.fourierChar (x * (n : ℝ)) : ℂ) * (𝓕 f) (n : ℝ) := by
  classical
  -- The specified L² equality fixes every coefficient of the actual smooth output.
  let V : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun z ↦ v.val (AddCircle.homeomorphCircle' z) 0,
      (contMDiff_fourierCircleSectionCoordinate v).continuous.comp
        AddCircle.homeomorphCircle'.continuous⟩
  have hvcoeff (n : ℤ) : fourierCoeff V n =
      if 0 ≤ n then (𝓕 f) (n : ℝ) else 0 := by
    have hvc : fourierCoeff (circleSmoothToFourierL2 v) n = fourierCoeff V n :=
      fourierCoeff_toLp V n
    rw [← hvc, hprojection, circleNonnegativeFourierProjection_fourierCoeff,
      fourierCoeff_circleSmoothToFourierL2_of_periodization f u hperiod n]
  -- Schwartz decay makes the projected Fourier series absolutely summable.
  have hcoeffsum : Summable (fun n : ℤ ↦ (𝓕 f) (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have hvsum : Summable (fourierCoeff V) := by
    apply Summable.of_norm_bounded hcoeffsum.norm
    intro n
    rw [hvcoeff]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg ((𝓕 f) (n : ℝ))
  let term (n : ℤ) : ℂ := fourierCoeff V n *
    fourier n ((2 * Real.pi * x : ℝ) : AddCircle (2 * Real.pi))
  have hterms : Summable term := by
    apply Summable.of_norm_bounded hvsum.norm
    intro n
    simp only [term, norm_mul, fourier_apply, Circle.norm_coe, mul_one, le_refl]
  -- Reconstruction is pointwise, and the negative modes vanish in the same series.
  have hneg (n : ℕ) : term (-((n : ℤ) + 1)) = 0 := by
    dsimp only [term]
    rw [hvcoeff, ite_eq_right (by omega : ¬0 ≤ -((n : ℤ) + 1)), zero_mul]
  have hsplit : (∑' n : ℤ, term n) = ∑' n : ℕ, term (n : ℤ) := by
    rw [tsum_of_nat_of_neg_add_one (hterms.comp_injective Nat.cast_injective)
      (by simpa only [hneg] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℂ))))]
    simp only [hneg, tsum_zero, add_zero]
  have hseries := (has_pointwise_sum_fourier_series_of_summable hvsum
    ((2 * Real.pi * x : ℝ) : AddCircle (2 * Real.pi))).tsum_eq.symm
  change v.val (Circle.exp (2 * Real.pi * x)) 0 = ∑' n : ℤ, term n at hseries
  rw [hsplit] at hseries
  -- Convert the original angular basis to the character of the positive period-one cover.
  refine hseries.trans (tsum_congr fun n ↦ ?_)
  have hchar : fourier (n : ℤ) ((2 * Real.pi * x : ℝ) : AddCircle (2 * Real.pi)) =
      (Real.fourierChar (x * (n : ℝ)) : ℂ) := by
    rw [fourier_coe_apply, Real.fourierChar_apply]
    push_cast
    congr 1
    field_simp
  simp only [term, hvcoeff, Int.natCast_nonneg, ite_true, Int.cast_natCast, hchar]
  exact mul_comm _ _

end AtiyahSinger
