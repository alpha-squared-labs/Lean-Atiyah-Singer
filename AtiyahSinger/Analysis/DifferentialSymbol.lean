/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateOperator
public import AtiyahSinger.Analysis.Quantization
public import AtiyahSinger.Analysis.SymbolQuotient

/-!
# The full polynomial symbol of a coordinate differential operator

Public module ID: M0438.

D03/D05/A02: SG III.3, formulas (3.1)-(3.2), with D_j = -i ∂_j.
The full polynomial quantizes to the actual differential expression. Its difference
from the degree-m polynomial has order at most m-1, with real subtraction even
when m=0. Coefficients need only be smooth locally; no global boundedness or
Schwartz-output assertion is made for an arbitrary coefficient family.
These are explicit comparison lemmas, not separately numbered lemmas in SG.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

namespace CoordinateDifferentialOperator

variable {n r q m : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The full coefficient polynomial, retaining every derivative order from zero to m. -/
def totalSymbol (P : CoordinateDifferentialOperator n r q m U) : SymbolFunction n r q :=
  fun x ξ ↦ ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
    (∏ j, ξ (α j)) • P.coefficient k α x

/-- Smooth coefficients give local-in-space symbol estimates for the full polynomial. -/
theorem isSymbol_totalSymbol (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r q m U) :
    IsSymbol U (m : ℝ) P.totalSymbol := by
  /- Each degree summand is the principal polynomial of the corresponding
  truncated expression with the same coefficients. Its established principal-symbol
  theorem gives the degree-k estimates. Since k ≤ m, symbol-order monotonicity
  puts every summand in the order-m submodule; their finite sum is the full symbol.
  The reused estimates are local on compact spatial subsets of U. -/
  classical
  let a (k : Fin (m + 1)) : SymbolFunction n r q :=
    fun x ξ ↦ ∑ α : Fin k.val → Fin n,
      (∏ j, ξ (α j)) • P.coefficient k α x
  -- Realize each degree as the principal polynomial of the same truncated expression.
  have hdegree (k : Fin (m + 1)) : IsSymbol U (k.val : ℝ) (a k) := by
    let Q : CoordinateDifferentialOperator n r q k.val U := {
      coefficient j α := P.coefficient
        ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) k.isLt⟩ α
      smooth_coefficient j α := P.smooth_coefficient
        ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) k.isLt⟩ α }
    exact Q.isSymbol_principalSymbol hU
  -- Every degree is at most m, and the fixed-order symbol class is a submodule.
  have hsum : (∑ k : Fin (m + 1), a k) ∈ symbolSpace U hU (m : ℝ) r q := by
    apply Submodule.sum_mem
    intro k _
    exact (hdegree k).mono (by exact_mod_cast Nat.le_of_lt_succ k.isLt)
  have htotal : P.totalSymbol = ∑ k : Fin (m + 1), a k := by
    funext x ξ
    simp only [totalSymbol, a, Finset.sum_apply]
  rwa [htotal]

/-- Discarding the top degree leaves order m-1; at m=0 the remainder is zero. -/
theorem isSymbol_totalSymbol_sub_principalSymbol (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r q m U) :
    IsSymbol U ((m : ℝ) - 1) (P.totalSymbol - P.principalSymbol) := by
  /- Subtracting the last degree summand cancels the original principal symbol,
  leaving a sum indexed by Fin m. Each remaining degree is realized by the same
  truncated coordinate expression and has degree-k symbol estimates. Monotonicity
  places these summands in order (m : ℝ) - 1. When m = 0 the remaining sum is empty,
  so it is zero in the order -1 space. The subtraction is in ℝ. -/
  classical
  let a (k : Fin (m + 1)) : SymbolFunction n r q :=
    fun x ξ ↦ ∑ α : Fin k.val → Fin n,
      (∏ j, ξ (α j)) • P.coefficient k α x
  -- Keep the identical coefficients and witnesses when passing to each lower degree.
  have hdegree (k : Fin (m + 1)) : IsSymbol U (k.val : ℝ) (a k) := by
    let Q : CoordinateDifferentialOperator n r q k.val U := {
      coefficient j α := P.coefficient
        ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) k.isLt⟩ α
      smooth_coefficient j α := P.smooth_coefficient
        ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) k.isLt⟩ α }
    exact Q.isSymbol_principalSymbol hU
  have hsum : (∑ k : Fin m, a k.castSucc) ∈
      symbolSpace U hU ((m : ℝ) - 1) r q := by
    apply Submodule.sum_mem
    intro k _
    apply (hdegree k.castSucc).mono
    have hle : (k.val : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    exact le_sub_iff_add_le.mpr hle
  -- Splitting off the last summand cancels the original top polynomial exactly.
  have hremainder : P.totalSymbol - P.principalSymbol =
      ∑ k : Fin m, a k.castSucc := by
    funext x ξ
    simp only [Pi.sub_apply, Finset.sum_apply]
    change (∑ k : Fin (m + 1), a k x ξ) - a (Fin.last m) x ξ =
      ∑ k : Fin m, a k.castSucc x ξ
    rw [Fin.sum_univ_castSucc, add_sub_cancel_right]
  -- For m = 0 this is the empty sum in the order -1 symbol space.
  rwa [hremainder]

/-- A zero-order differential expression has no lower-degree polynomial terms. -/
theorem totalSymbol_eq_principalSymbol_zero
    (P : CoordinateDifferentialOperator n r q 0 U) :
    P.totalSymbol = P.principalSymbol := by
  /- The degree index Fin 1 has one element. The empty derivative index has one
  map to Fin n and its empty monomial product is one. Both formulas therefore
  reduce to the same multiplication coefficient, including when n=0. -/
  classical
  funext x ξ
  simp [totalSymbol, principalSymbol]

/-- SG (3.1)-(3.2): polynomial quantization is the original differential expression. -/
theorem quantize_totalSymbol (P : CoordinateDifferentialOperator n r q m U)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) : quantize P.totalSymbol u x = P.apply u x := by
  /- Stage 1: Fourier inversion for Schwartz u can be differentiated any finite
  number of times under the integral. Each D_j=-i∂_j produces the multiplier ξ_j.
  The rescaled fourierSG and the inverse (2π)^(-n) factor cancel as prescribed.
  Stage 2: each polynomial multiple of the Fourier transform is integrable.
  Commute the finite sums and the fixed coefficient maps at x with the integral.
  The resulting terms are exactly those in P.apply. No coefficient derivative is
  taken here, so this pointwise identity even holds outside the smoothness domain U.
  It does not assert that P.apply maps Schwartz functions into Schwartz functions. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by positivity
  -- Fourier differentiation preserves the actual ordered derivatives as Schwartz functions.
  have hiter (k : ℕ) (α : Fin k → Fin n) (η : X) :
      FourierTransform.fourier
        (LineDeriv.iteratedLineDerivOp (fun j ↦ EuclideanSpace.single (α j) (1 : ℝ)) u) η =
        ((c : ℂ) * Complex.I) ^ k • (∏ j, η (α j)) •
          FourierTransform.fourier u η := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left, SchwartzMap.fourier_lineDerivOp_eq]
      simp only [smul_apply]
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      have htail := ih (Fin.tail α)
      change (2 * (Real.pi : ℂ) * Complex.I) •
        inner ℝ η (EuclideanSpace.single (α 0) 1) •
          FourierTransform.fourier
            (LineDeriv.iteratedLineDerivOp
              (fun j ↦ EuclideanSpace.single (Fin.tail α j) (1 : ℝ)) u) η = _
      rw [htail]
      have hcoord := EuclideanSpace.inner_single_right (α 0) (1 : ℝ) η
      simp only [one_mul, conj_trivial] at hcoord
      rw [hcoord]
      simp only [Fin.prod_univ_succ, pow_succ', ← Complex.coe_smul, smul_smul, c,
        Complex.ofReal_mul, Complex.ofReal_ofNat]
      congr 1
      simp only [Fin.tail]
      ring
  let d (k : ℕ) (α : Fin k → Fin n) : 𝓢(X, V) :=
    (-Complex.I) ^ k •
      LineDeriv.iteratedLineDerivOp (fun j ↦ EuclideanSpace.single (α j) (1 : ℝ)) u
  have hd (k : ℕ) (α : Fin k → Fin n) (η : X) :
      FourierTransform.fourier (d k α) η =
        (∏ j, (c • η) (α j)) • FourierTransform.fourier u η := by
    have hprod : (∏ j, (c • η) (α j)) = c ^ k * ∏ j, η (α j) := by
      change (∏ j, c * η (α j)) = _
      rw [Finset.prod_mul_distrib]
      simp
    have hscalar : (-Complex.I) ^ k * ((c : ℂ) * Complex.I) ^ k = (c : ℂ) ^ k := by
      rw [← mul_pow]
      congr 1
      calc
        (-Complex.I) * ((c : ℂ) * Complex.I) =
            (c : ℂ) * (-(Complex.I * Complex.I)) := by ring
        _ = c := by simp
    simp only [d, FourierTransform.fourier_smul, smul_apply]
    rw [hiter, hprod]
    simp only [← Complex.coe_smul, smul_smul, Complex.ofReal_mul, Complex.ofReal_pow]
    congr 1
    rw [← mul_assoc, hscalar]
  -- The scalar change of variables cancels the exact SG inverse normalization.
  have hnormalize : quantize P.totalSymbol u x =
      ∫ η : X, Complex.exp ((↑(c * inner ℝ η x) : ℂ) * Complex.I) •
        P.totalSymbol x (c • η) (FourierTransform.fourier u η) := by
    let g (ξ : X) : EuclideanSpace ℂ (Fin q) :=
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        P.totalSymbol x ξ (fourierSG u ξ)
    have hscale := MeasureTheory.Measure.integral_comp_smul_of_nonneg
      (MeasureTheory.volume : MeasureTheory.Measure X) g c (hR := hc.le)
    calc
      _ = ∫ η : X, g (c • η) := by
        simpa only [X, finrank_euclideanSpace_fin, quantize, g, c] using hscale.symm
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with η
        have hfourier : fourierSG u (c • η) = FourierTransform.fourier u η := by
          change FourierTransform.fourier u (c⁻¹ • (c • η)) = _
          rw [inv_smul_smul₀ (ne_of_gt hc)]
        dsimp only [g]
        rw [hfourier]
        congr 2
        rw [inner_smul_right, real_inner_comm]
        push_cast
        ring
  let phase (η : X) : ℂ := Complex.exp ((↑(c * inner ℝ η x) : ℂ) * Complex.I)
  -- Every derivative is Schwartz, so its oscillatory inverse integral is integrable.
  have hintegrable (w : 𝓢(X, V)) :
      MeasureTheory.Integrable (fun η ↦ phase η • FourierTransform.fourier w η) := by
    have h := (Real.fourierIntegral_convergent_iff
      (μ := (MeasureTheory.volume : MeasureTheory.Measure X))
      (f := (FourierTransform.fourier w : 𝓢(X, V))) (-x)).mpr
        (FourierTransform.fourier w : 𝓢(X, V)).integrable
    simpa only [inner_neg_right, neg_neg, Circle.smul_def, Real.fourierChar_apply,
      c, phase] using h
  have hinversion (w : 𝓢(X, V)) :
      (∫ η : X, phase η • FourierTransform.fourier w η) = w x := by
    calc
      _ = FourierTransform.fourierInv (fun η ↦ FourierTransform.fourier w η) x := by
        symm
        simpa only [c, phase] using
          Real.fourierInv_eq' (fun η ↦ FourierTransform.fourier w η) x
      _ = (FourierTransform.fourierInv (FourierTransform.fourier w) : 𝓢(X, V)) x :=
        congrFun (SchwartzMap.fourierInv_coe (FourierTransform.fourier w)).symm x
      _ = w x := by rw [FourierTransform.fourierInv_fourier_eq]
  let term (k : Fin (m + 1)) (α : Fin k.val → Fin n) (η : X) :
      EuclideanSpace ℂ (Fin q) :=
    P.coefficient k α x (phase η • FourierTransform.fourier (d k.val α) η)
  have hterm (k : Fin (m + 1)) (α : Fin k.val → Fin n) :
      MeasureTheory.Integrable (term k α) :=
    (P.coefficient k α x).integrable_comp (hintegrable (d k.val α))
  have htermIntegral (k : Fin (m + 1)) (α : Fin k.val → Fin n) :
      (∫ η : X, term k α η) = P.coefficient k α x (d k.val α x) := by
    change (∫ η : X, P.coefficient k α x
      (phase η • FourierTransform.fourier (d k.val α) η)) = _
    rw [(P.coefficient k α x).integral_comp_comm (hintegrable (d k.val α)), hinversion]
  -- The same finite coefficient family distributes over the inverse Fourier integral.
  have hsum (η : X) :
      phase η • P.totalSymbol x (c • η) (FourierTransform.fourier u η) =
        ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n, term k α η := by
    simp only [totalSymbol, sum_apply, smul_apply, Finset.smul_sum, term, hd,
      ← Complex.coe_smul, map_smul, smul_smul]
  rw [hnormalize]
  change (∫ η : X, phase η • P.totalSymbol x (c • η)
    (FourierTransform.fourier u η)) = _
  simp_rw [hsum]
  calc
    _ = ∑ k : Fin (m + 1), ∫ η : X, ∑ α : Fin k.val → Fin n, term k α η :=
      MeasureTheory.integral_finsetSum _ (fun k _ ↦
        MeasureTheory.integrable_finsetSum _ (fun α _ ↦ hterm k α))
    _ = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n, ∫ η : X, term k α η := by
      apply Finset.sum_congr rfl
      intro k _
      exact MeasureTheory.integral_finsetSum _ (fun α _ ↦ hterm k α)
    _ = P.apply u x := by
      simp_rw [htermIntegral]
      simp only [apply, d, smul_apply, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

end CoordinateDifferentialOperator

end AtiyahSinger
