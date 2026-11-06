/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LaurentApproximation
public import AtiyahSinger.Analysis.WienerLoop

/-!
# Finite Laurent polynomials inside the Wiener coefficient space

Public module ID: M0779.

KA III.1.17, pp.117–118. This is the actual inclusion of finite coefficients into
bilateral ℓ¹, connecting the polynomial approximation model to the analytic inverse
model. Circle evaluation agrees on the same polynomial; no inverse is required to
have finite support.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The finite-coefficient inclusion into the actual bilateral Wiener space. -/
def laurentPolynomialWiener (p : LaurentPolynomial A) : WienerLoop A :=
  p.coeff.sum (fun n a ↦ lp.single 1 n a)

/-- The Wiener inclusion preserves exactly the coefficients of the specified polynomial. -/
theorem laurentPolynomialWiener_coeff (p : LaurentPolynomial A) (n : ℤ) :
    laurentPolynomialWiener p n = p.coeff n := by
  -- Evaluation of the finite coefficient sum keeps only the nth coordinate.
  classical
  simp only [laurentPolynomialWiener, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    simp [Ne.symm hkn]
  · intro hn
    simp [Finsupp.notMem_support_iff.mp hn]

/-- The finite and absolutely summable models give the same circle map. -/
theorem laurentPolynomialWiener_eval (p : LaurentPolynomial A) (z : Circle) :
    (laurentPolynomialWiener p).eval z = laurentPolynomialCircleValue p z := by
  -- Replace the Wiener coefficients by the original finite Laurent coefficients.
  change (∑' n : ℤ, (z : ℂ) ^ n • laurentPolynomialWiener p n) = _
  simp_rw [laurentPolynomialWiener_coeff]
  -- The infinite sum reduces to the polynomial's actual finite support.
  apply tsum_eq_sum
  intro n hn
  simp only [Finsupp.notMem_support_iff.mp hn, smul_zero]

end AtiyahSinger
