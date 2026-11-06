/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Analysis.SmoothSectionMultiplication

/-!
# Uniform scalar bounds in the specified integral section norm

Public module ID: M0724.

Multiplication by a smooth scalar function has L2 norm at most its uniform norm.
The proof integrates the original Hermitian form and leaves every fiber norm,
metric and density unchanged. This estimate transfers uniform approximation
of coefficients to geometric L2 approximation of finite frame expansions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothHermitianMetric

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (h : SmoothHermitianMetric (n := n) (r := r) E) (μ : Measure M)
  [IsSmoothPositiveMeasure (n := n) μ]

/-- A uniform scalar bound gives the same bound in the original metric L2 completion. -/
theorem norm_smoothToL2_mul_le (f : C(M, ℂ))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f)
    (u : smoothSections (n := n) (r := r) E) :
    ‖h.smoothToL2 μ (smoothSectionMul E f hf u)‖ ≤ ‖f‖ * ‖h.smoothToL2 μ u‖ := by
  let v := smoothSectionMul E f hf u
  -- Sesquilinearity makes the scalar multiplier contribute its squared absolute value.
  have hpoint (x : M) : (h.pairing x (v.val x) (v.val x)).re =
      ‖f x‖ ^ 2 * (h.pairing x (u.val x) (u.val x)).re := by
    have hleft (a b : E x) (c : ℂ) :
        h.pairing x (c • a) b = conj c * h.pairing x a b :=
      (h.toCore x).smul_left a b c
    have hconj (a b : E x) : conj (h.pairing x b a) = h.pairing x a b :=
      (h.toCore x).conj_inner_symm a b
    have hright (a b : E x) (c : ℂ) :
        h.pairing x a (c • b) = c * h.pairing x a b := by
      rw [← hconj a (c • b), hleft]
      simp only [map_mul, starRingEnd_self_apply, hconj]
    change (h.pairing x (f x • u.val x) (f x • u.val x)).re = _
    rw [hleft, hright]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  have hintu := (h.integrable_pairing μ u u).re
  have hintv := (h.integrable_pairing μ v v).re
  have hsq : ‖h.smoothToL2 μ v‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖h.smoothToL2 μ u‖ ^ 2 := by
    rw [h.norm_smoothToL2_sq, h.norm_smoothToL2_sq]
    change (∫ x, h.pairing x (v.val x) (v.val x) ∂μ).re ≤
      ‖f‖ ^ 2 * (∫ x, h.pairing x (u.val x) (u.val x) ∂μ).re
    have hre (s : smoothSections (n := n) (r := r) E) :
        (∫ x, h.pairing x (s.val x) (s.val x) ∂μ).re =
          ∫ x, (h.pairing x (s.val x) (s.val x)).re ∂μ := by
      simpa only [RCLike.re_eq_complex_re] using (integral_re (h.integrable_pairing μ s s)).symm
    rw [hre, hre, ← integral_const_mul]
    apply integral_mono hintv (hintu.const_mul (‖f‖ ^ 2))
    intro x
    change (h.pairing x (v.val x) (v.val x)).re ≤
      ‖f‖ ^ 2 * (h.pairing x (u.val x) (u.val x)).re
    rw [hpoint]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm x) 2)
      ((h.toCore x).re_inner_nonneg (u.val x))
  -- Both sides are nonnegative, so the squared estimate determines the norm estimate.
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using hsq

end AtiyahSinger.SmoothHermitianMetric
