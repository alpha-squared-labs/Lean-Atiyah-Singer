/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequence
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Multiplication in the characteristic-series parameter

Public module ID: M0042.

The universal multiplicative sequence also preserves multiplication in its
normalized characteristic-series parameter. Evaluate on the same formal roots,
descend by elementary-symmetric injectivity, then substitute the given finite
coefficient data. This is distinct from multiplication of the input Chern series.
The unit and inverse formulas give finite characteristic-class convolution laws.

Source: the universal symmetric-polynomial construction in SG III.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.MultiplicativeSequence

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Multiplication of normalized characteristic series multiplies their transformed values. -/
theorem transform_mul_left (f g : PowerSeries ℚ)
    (hf : f.constantCoeff = 1) (hg : g.constantCoeff = 1) (b : PowerSeries R) :
    transform (f * g) b = transform f b * transform g b := by
  classical
  -- At a fixed finite root family the parameter identity is ordinary factorwise multiplication.
  have hroots (n : ℕ) : rootProduct (f * g) n = rootProduct f n * rootProduct g n := by
    have hfactor (q : PowerSeries ℚ) (i : Fin n) :
        (PowerSeries.mk fun j : ℕ ↦ MvPolynomial.C (PowerSeries.coeff j q) *
          MvPolynomial.X i ^ j) =
        PowerSeries.rescale (MvPolynomial.X i) (PowerSeries.map MvPolynomial.C q) := by
      apply PowerSeries.ext
      intro j
      simp only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale, PowerSeries.coeff_map]
      exact mul_comm _ _
    simp only [rootProduct, hfactor, map_mul, Finset.prod_mul_distrib]
  apply PowerSeries.ext
  intro k
  let B : PowerSeries (MvPolynomial (Fin k) ℚ) := PowerSeries.mk fun j ↦ match j with
    | 0 => 1
    | j + 1 => if hj : j < k then MvPolynomial.X ⟨j, hj⟩ else 0
  let E : MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin k) ℚ :=
    MvPolynomial.aeval (fun i : Fin k ↦ MvPolynomial.esymm (Fin k) ℚ (i.val + 1))
  -- Independent elementary symmetric variables detect polynomial identities in the coefficients.
  have hinj : Function.Injective E := by
    intro p q hpq
    apply MvPolynomial.esymmAlgHom_fin_injective ℚ (n := k) (m := k) le_rfl
    apply Subtype.ext
    simpa only [MvPolynomial.esymmAlgHom_apply] using hpq
  have hB (j : ℕ) : E (PowerSeries.coeff (j + 1) B) =
      MvPolynomial.esymm (Fin k) ℚ (j + 1) := by
    by_cases hj : j < k
    · simp [B, E, hj]
    · have hlarge : (Finset.univ : Finset (Fin k)).card < j + 1 := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      simp [B, hj, MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr hlarge]
  have hroot (q : PowerSeries ℚ) (hq : q.constantCoeff = 1) :
      PowerSeries.map E.toRingHom (transform q B) = rootProduct q k := by
    apply PowerSeries.ext
    intro j
    simp only [PowerSeries.coeff_map, transform, PowerSeries.coeff_mk]
    change E (MvPolynomial.aeval (fun i : Fin j ↦ PowerSeries.coeff (i.val + 1) B)
      (polynomial q j)) = _
    rw [MvPolynomial.comp_aeval_apply]
    simp_rw [hB]
    exact polynomial_esymm q hq k j
  have hU : transform (f * g) B = transform f B * transform g B := by
    apply PowerSeries.map_injective E.toRingHom hinj
    rw [map_mul, hroot (f * g) (by simp [hf, hg]), hroot f hf, hroot g hg]
    exact hroots k
  -- Substitute the given first k positive coefficients; no input constant term is needed.
  let φ : MvPolynomial (Fin k) ℚ →ₐ[ℚ] R :=
    MvPolynomial.aeval (fun i : Fin k ↦ PowerSeries.coeff (i.val + 1) b)
  let B' := PowerSeries.map φ.toRingHom B
  -- The finite coefficient substitution commutes with the same universal polynomials.
  have hmap (q : PowerSeries ℚ) :
      PowerSeries.map φ.toRingHom (transform q B) = transform q B' := by
    apply PowerSeries.ext
    intro j
    simp only [B', transform, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact MvPolynomial.comp_aeval_apply _ φ _
  have hcoeff (j : ℕ) (hj : 0 < j) (hjk : j ≤ k) :
      PowerSeries.coeff j B' = PowerSeries.coeff j b := by
    cases j with
    | zero => omega
    | succ j =>
      have hlt : j < k := hjk
      simp [B', B, φ, hlt]
  have htrans (q : PowerSeries ℚ) (j : ℕ) (hj : j ≤ k) :
      PowerSeries.coeff j (transform q B') = PowerSeries.coeff j (transform q b) := by
    simp only [transform, PowerSeries.coeff_mk]
    apply congrArg (fun a : Fin j → R ↦ MvPolynomial.aeval a (polynomial q j))
    funext i
    exact hcoeff (i.val + 1) (by omega) ((Nat.succ_le_of_lt i.isLt).trans hj)
  have hU' : transform (f * g) B' = transform f B' * transform g B' := by
    have h := congrArg (PowerSeries.map φ.toRingHom) hU
    simpa only [hmap, map_mul] using h
  -- Coefficient k of the product reads only transformed coefficients through degree k.
  calc
    PowerSeries.coeff k (transform (f * g) b) =
        PowerSeries.coeff k (transform (f * g) B') := (htrans _ k le_rfl).symm
    _ = PowerSeries.coeff k (transform f B' * transform g B') := by rw [hU']
    _ = PowerSeries.coeff k (transform f b * transform g b) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hpk : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
      rw [htrans f p.1 (by omega), htrans g p.2 (by omega)]

/-- The unit characteristic series gives the unit transformed series for every coefficient input. -/
theorem transform_one_left (b : PowerSeries R) : transform 1 b = 1 := by
  -- The transformed unit is idempotent by parameter multiplication and is itself a unit.
  have hmul := transform_mul_left 1 1 (by simp) (by simp) b
  have hu : IsUnit (transform 1 b) := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [constantCoeff_transform]
    exact isUnit_one)
  apply hu.mul_left_cancel
  simpa only [one_mul, mul_one] using hmul.symm

/-- Inverse characteristic series give inverse transformed values on the same coefficient input. -/
theorem transform_mul_inv (f : PowerSeries ℚ) (hf : f.constantCoeff = 1)
    (b : PowerSeries R) : transform f b * transform f⁻¹ b = 1 := by
  have hinv : (f⁻¹).constantCoeff = 1 := by simp [hf]
  rw [← transform_mul_left f f⁻¹ hf hinv,
    PowerSeries.mul_inv_cancel f (by rw [hf]; exact one_ne_zero), transform_one_left]

end AtiyahSinger.MultiplicativeSequence
