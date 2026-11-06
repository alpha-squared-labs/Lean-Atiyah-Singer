/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Integral expressions for power sums in elementary symmetric functions

Public module ID: M0043.

The fundamental theorem of symmetric polynomials gives the unique integral
polynomial expressing a power sum in elementary symmetric functions. This is
the polynomial usually calculated by Newton's identities. It is constructed
independently of any geometric splitting or descent assertion.

Evaluation works over every commutative ring, in every degree and for an
empty root family. The Chern-character construction applies this polynomial
to actual Chern classes and only then takes the required homogeneous component.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The integral Newton polynomial for the k-th power sum of r roots. -/
def newtonPowerSumPolynomial (r k : ℕ) : MvPolynomial (Fin r) ℤ :=
  (MvPolynomial.esymmAlgEquiv (Fin r) ℤ (Fintype.card_fin r)).symm
    ⟨MvPolynomial.psum (Fin r) ℤ k, MvPolynomial.psum_isSymmetric (Fin r) ℤ k⟩

/-- Substitution of the elementary symmetric polynomials recovers the original power sum. -/
theorem newtonPowerSumPolynomial_esymm (r k : ℕ) :
    MvPolynomial.aeval (fun i : Fin r ↦ MvPolynomial.esymm (Fin r) ℤ (i.val + 1))
        (newtonPowerSumPolynomial r k) = MvPolynomial.psum (Fin r) ℤ k := by
  -- Use the actual inverse of the elementary-symmetric algebra isomorphism.
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact congrArg Subtype.val
    ((MvPolynomial.esymmAlgEquiv (Fin r) ℤ (Fintype.card_fin r)).apply_symm_apply
      ⟨MvPolynomial.psum (Fin r) ℤ k, MvPolynomial.psum_isSymmetric (Fin r) ℤ k⟩)

/-- The same integral polynomial evaluates to the power sum of any specified ring elements. -/
theorem newtonPowerSumPolynomial_eval {A : Type*} [CommRing A]
    (r k : ℕ) (x : Fin r → A) :
    MvPolynomial.aeval (fun i : Fin r ↦ (Finset.univ.val.map x).esymm (i.val + 1))
        (newtonPowerSumPolynomial r k) = ∑ i : Fin r, x i ^ k := by
  -- Evaluate the universal identity; algebra evaluation preserves all finite operations.
  have h := congrArg (MvPolynomial.aeval x) (newtonPowerSumPolynomial_esymm r k)
  rw [MvPolynomial.comp_aeval_apply] at h
  simpa only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_esymm_eq_multiset_esymm,
    MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X] using h

end AtiyahSinger
