/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequenceParameter
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.PowerSeries.Expand

import all AtiyahSinger.Algebra.MultiplicativeSequence

/-!
# Universal multiplicative sequences on paired formal roots

Public module ID: M0041.

A characteristic-series identity on a root and its negative descends to an
identity on the signed even elementary coefficients. The independent variables
are the squared roots; elementary-symmetric injectivity followed by injectivity
of polynomial expansion detects the universal identity. Finite coefficient
substitution then applies it to any commutative rational algebra.

Source: the universal polynomial argument for SG III.11, Proposition 11.14.
No geometric paired-root splitting or orientation is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.MultiplicativeSequence

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A paired characteristic-series square identity holds on every signed even coefficient input. -/
theorem transform_expand_rescale_neg_one_eq_sq (f g : PowerSeries ℚ)
    (hf : f.constantCoeff = 1) (hg : g.constantCoeff = 1)
    (hfg : f * PowerSeries.evalNegHom f = (PowerSeries.expand 2 (by decide) g) ^ 2)
    (b : PowerSeries R) :
    transform f (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) b)) =
      (PowerSeries.expand 2 (by decide) (transform g b)) ^ 2 := by
  classical
  -- First prove the identity on the same finite free roots and their negatives.
  have hformal (n : ℕ) :
      let Θ := MvPolynomial.expand (σ := Fin n) (R := ℚ) 2
      let B := rootProduct (1 + PowerSeries.X) n
      transform f (PowerSeries.expand 2 (by decide)
          (PowerSeries.rescale (-1) (PowerSeries.map Θ.toRingHom B))) =
        (PowerSeries.expand 2 (by decide)
          (transform g (PowerSeries.map Θ.toRingHom B))) ^ 2 := by
    let Θ := MvPolynomial.expand (σ := Fin n) (R := ℚ) 2
    let N : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
      MvPolynomial.aeval (fun i ↦ -MvPolynomial.X i)
    let B := rootProduct (1 + PowerSeries.X) n
    have hroot (q : PowerSeries ℚ) (hq : q.constantCoeff = 1) :
        transform q B = rootProduct q n := by
      apply PowerSeries.ext
      intro j
      simp only [B, transform, PowerSeries.coeff_mk, coeff_rootProduct_one_add_X]
      exact polynomial_esymm q hq n j
    have hmul (q₁ q₂ : PowerSeries ℚ) (h₁ : q₁.constantCoeff = 1)
        (h₂ : q₂.constantCoeff = 1) :
        rootProduct (q₁ * q₂) n = rootProduct q₁ n * rootProduct q₂ n := by
      rw [← hroot (q₁ * q₂) (by simp [h₁, h₂]), transform_mul_left q₁ q₂ h₁ h₂,
        hroot q₁ h₁, hroot q₂ h₂]
    have hscale (q : PowerSeries ℚ) :
        rootProduct (PowerSeries.rescale (-1) q) n =
          PowerSeries.rescale (-1) (rootProduct q n) := by
      have hfactor (i : Fin n) :
          (PowerSeries.mk fun j ↦ MvPolynomial.C
            (PowerSeries.coeff j (PowerSeries.rescale (-1) q)) * MvPolynomial.X i ^ j) =
          PowerSeries.rescale (-1) (PowerSeries.mk fun j ↦
            MvPolynomial.C (PowerSeries.coeff j q) * MvPolynomial.X i ^ j) := by
        apply PowerSeries.ext
        intro j
        simp [PowerSeries.coeff_rescale, mul_assoc]
      simpa only [rootProduct, map_prod] using congrArg (fun F ↦ ∏ i : Fin n, F i)
        (funext hfactor)
    have hnegative (q : PowerSeries ℚ) :
        PowerSeries.map N.toRingHom (rootProduct q n) =
          PowerSeries.rescale (-1) (rootProduct q n) := by
      have hfactor (i : Fin n) : PowerSeries.map N.toRingHom
          (PowerSeries.mk fun j ↦ MvPolynomial.C (PowerSeries.coeff j q) *
            MvPolynomial.X i ^ j) =
          PowerSeries.rescale (-1) (PowerSeries.mk fun j ↦
            MvPolynomial.C (PowerSeries.coeff j q) * MvPolynomial.X i ^ j) := by
        apply PowerSeries.ext
        intro j
        simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
          N, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, map_pow,
          MvPolynomial.aeval_C, MvPolynomial.aeval_X]
        change MvPolynomial.C (PowerSeries.coeff j q) * (-MvPolynomial.X i) ^ j = _
        rw [neg_pow (MvPolynomial.X i : MvPolynomial (Fin n) ℚ) j]
        ring
      simpa only [rootProduct, map_prod] using congrArg (fun F ↦ ∏ i : Fin n, F i)
        (funext hfactor)
    have hexpand (q : PowerSeries ℚ) :
        rootProduct (PowerSeries.expand 2 (by decide) q) n =
          PowerSeries.expand 2 (by decide) (PowerSeries.map Θ.toRingHom (rootProduct q n)) := by
      have hfactor (i : Fin n) :
          (PowerSeries.mk fun j ↦ MvPolynomial.C
            (PowerSeries.coeff j (PowerSeries.expand 2 (by decide) q)) *
              MvPolynomial.X i ^ j) =
          PowerSeries.expand 2 (by decide) (PowerSeries.map Θ.toRingHom
            (PowerSeries.mk fun j ↦ MvPolynomial.C (PowerSeries.coeff j q) *
              MvPolynomial.X i ^ j)) := by
        apply PowerSeries.ext
        intro j
        by_cases hj : 2 ∣ j
        · obtain ⟨m, rfl⟩ := hj
          simp [PowerSeries.coeff_expand_mul, Θ, MvPolynomial.expand_X, pow_mul]
        · simp [PowerSeries.coeff_expand_of_not_dvd _ _ _ hj, PowerSeries.coeff_mk]
      simpa only [rootProduct, map_prod] using congrArg (fun F ↦ ∏ i : Fin n, F i)
        (funext hfactor)
    have hlinear : (1 + (PowerSeries.X : PowerSeries ℚ)) *
        PowerSeries.rescale (-1) (1 + PowerSeries.X) =
        PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) (1 + PowerSeries.X)) := by
      simp only [map_add, map_one, PowerSeries.rescale_neg_one_X, map_neg, PowerSeries.expand_X]
      ring
    have hinput : B * PowerSeries.rescale (-1) B =
        PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1)
          (PowerSeries.map Θ.toRingHom B)) := by
      calc
        _ = rootProduct ((1 + PowerSeries.X) *
            PowerSeries.rescale (-1) (1 + PowerSeries.X)) n := by
          rw [hmul _ _ (by simp) (by simp), hscale]
        _ = rootProduct (PowerSeries.expand 2 (by decide)
            (PowerSeries.rescale (-1) (1 + PowerSeries.X))) n :=
          congrArg (fun q ↦ rootProduct q n) hlinear
        _ = _ := by
          rw [hexpand, hscale, ← PowerSeries.rescale_map, map_neg, map_one]
    have houtput : rootProduct f n * PowerSeries.rescale (-1) (rootProduct f n) =
        (PowerSeries.expand 2 (by decide) (PowerSeries.map Θ.toRingHom (rootProduct g n))) ^ 2 := by
      calc
        _ = rootProduct (f * PowerSeries.evalNegHom f) n := by
          rw [hmul _ _ hf (by
            simpa only [PowerSeries.evalNegHom, ← PowerSeries.coeff_zero_eq_constantCoeff,
              PowerSeries.coeff_rescale, pow_zero, one_mul] using hf)]
          exact congrArg (rootProduct f n * ·) (hscale f).symm
        _ = rootProduct ((PowerSeries.expand 2 (by decide) g) ^ 2) n :=
          congrArg (fun q ↦ rootProduct q n) hfg
        _ = _ := by
          rw [pow_two, hmul _ _ (by simpa using hg) (by simpa using hg), hexpand, pow_two]
    have hB : B.constantCoeff = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_rootProduct_one_add_X]
      simp
    calc
      _ = transform f (B * PowerSeries.rescale (-1) B) := congrArg _ hinput.symm
      _ = transform f B * transform f (PowerSeries.rescale (-1) B) :=
        transform_mul f hf B _ hB (by
          simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
            pow_zero, one_mul] using hB)
      _ = rootProduct f n * PowerSeries.rescale (-1) (rootProduct f n) := by
        rw [← hnegative (1 + PowerSeries.X), ← map_transform, hroot f hf, hnegative]
      _ = (PowerSeries.expand 2 (by decide)
          (PowerSeries.map Θ.toRingHom (rootProduct g n))) ^ 2 := houtput
      _ = _ := by rw [← hroot g hg, map_transform]
  apply PowerSeries.ext
  intro k
  let B : PowerSeries (MvPolynomial (Fin k) ℚ) := PowerSeries.mk fun j ↦ match j with
    | 0 => 1
    | j + 1 => if hj : j < k then MvPolynomial.X ⟨j, hj⟩ else 0
  let Θ := MvPolynomial.expand (σ := Fin k) (R := ℚ) 2
  let S : MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin k) ℚ :=
    MvPolynomial.aeval (fun i ↦ MvPolynomial.esymm (Fin k) ℚ (i.val + 1))
  let E := Θ.comp S
  -- Elementary symmetric variables in squared independent roots still detect polynomial identities.
  have hinjS : Function.Injective S := by
    intro p q hpq
    apply MvPolynomial.esymmAlgHom_fin_injective ℚ (n := k) (m := k) le_rfl
    apply Subtype.ext
    simpa only [MvPolynomial.esymmAlgHom_apply] using hpq
  have hinj : Function.Injective E :=
    (MvPolynomial.expand_injective (R := ℚ) (σ := Fin k) (by decide : 0 < 2)).comp hinjS
  have hB (j : ℕ) : S (PowerSeries.coeff (j + 1) B) =
      MvPolynomial.esymm (Fin k) ℚ (j + 1) := by
    by_cases hj : j < k
    · simp [B, S, hj]
    · have hlarge : (Finset.univ : Finset (Fin k)).card < j + 1 := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      simp [B, hj, MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr hlarge]
  have himage : PowerSeries.map E.toRingHom B =
      PowerSeries.map Θ.toRingHom (rootProduct (1 + PowerSeries.X) k) := by
    apply PowerSeries.ext
    intro j
    cases j with
    | zero => simp [B, E, coeff_rootProduct_one_add_X]
    | succ j =>
      simp only [PowerSeries.coeff_map, coeff_rootProduct_one_add_X]
      change Θ (S (PowerSeries.coeff (j + 1) B)) = Θ _
      rw [hB]
  have hU : transform f (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) B)) =
      (PowerSeries.expand 2 (by decide) (transform g B)) ^ 2 := by
    apply PowerSeries.map_injective E.toRingHom hinj
    simp only [map_transform, PowerSeries.map_expand, map_pow]
    rw [← PowerSeries.rescale_map, map_neg, map_one]
    simpa only [himage] using hformal k
  -- Substitute only the first k positive coefficients of the supplied series.
  let φ : MvPolynomial (Fin k) ℚ →ₐ[ℚ] R :=
    MvPolynomial.aeval (fun i ↦ PowerSeries.coeff (i.val + 1) b)
  let B' := PowerSeries.map φ.toRingHom B
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
  have hencoded (j : ℕ) (hj : 0 < j) (hjk : j ≤ k) :
      PowerSeries.coeff j (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) B')) =
        PowerSeries.coeff j (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) b)) := by
    rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
    split_ifs with hd
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale,
        hcoeff (j / 2) (by omega) (by omega)]
    · rfl
  have htransEncoded (j : ℕ) (hj : j ≤ k) :
      PowerSeries.coeff j (transform f
          (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) B'))) =
        PowerSeries.coeff j (transform f
          (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) b))) := by
    simp only [transform, PowerSeries.coeff_mk]
    apply congrArg (fun a : Fin j → R ↦ MvPolynomial.aeval a (polynomial f j))
    funext i
    exact hencoded (i.val + 1) (by omega) ((Nat.succ_le_of_lt i.isLt).trans hj)
  have hexpanded (j : ℕ) (hj : j ≤ k) :
      PowerSeries.coeff j (PowerSeries.expand 2 (by decide) (transform g B')) =
        PowerSeries.coeff j (PowerSeries.expand 2 (by decide) (transform g b)) := by
    rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
    split_ifs
    · exact htrans g (j / 2) (by omega)
    · rfl
  have hU' : transform f (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) B')) =
      (PowerSeries.expand 2 (by decide) (transform g B')) ^ 2 := by
    have hm := congrArg (PowerSeries.map φ.toRingHom) hU
    simp only [map_transform, PowerSeries.map_expand, map_pow] at hm
    rw [← PowerSeries.rescale_map, map_neg, map_one] at hm
    exact hm
  calc
    _ = PowerSeries.coeff k (transform f
        (PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) B'))) :=
      (htransEncoded k le_rfl).symm
    _ = PowerSeries.coeff k ((PowerSeries.expand 2 (by decide) (transform g B')) ^ 2) :=
      congrArg (PowerSeries.coeff k) hU'
    _ = _ := by
      simp only [pow_two, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hpk : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
      rw [hexpanded p.1 (by omega), hexpanded p.2 (by omega)]

end AtiyahSinger.MultiplicativeSequence
