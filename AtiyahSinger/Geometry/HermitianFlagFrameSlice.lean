/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothInverseChart
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Local unitary frame slices for Hermitian flags

Public module ID: M1263.

Unitary frames with positive real diagonal entries fix the independent phases
near the standard frame. The Gram equations and diagonal imaginary parts,
together with the strict lower entries, have an invertible real derivative.
The inverse function theorem then supplies the actual local flag parameters.

Source: the standard local slice description of U(r)/U(1)^r, used for the
projection flag model of Spin Geometry III.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped ComplexConjugate BigOperators ContDiff Matrix.Norms.Elementwise

local notation "Pair" r:arg => {p : Fin r × Fin r // Prod.fst p < Prod.snd p}
local notation "Mat" r:arg => Matrix (Fin r) (Fin r) ℂ
local notation "Coordinates" r:arg => ((Fin r → ℂ) × (Pair r → ℂ)) × (Pair r → ℂ)

-- The first two blocks are the linearized constraints; the last block is free.
private def flagFrameLinearEquiv (r : ℕ) : Mat r ≃ₗ[ℝ] Coordinates r where
  toFun A := ((fun i ↦ A i i, fun p ↦ A p.val.1 p.val.2 + conj (A p.val.2 p.val.1)),
    fun p ↦ A p.val.2 p.val.1)
  invFun z i j := if hij : i = j then z.1.1 i else
    if hlt : i < j then z.1.2 ⟨(i, j), hlt⟩ - conj (z.2 ⟨(i, j), hlt⟩)
    else z.2 ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)⟩
  map_add' A B := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext p
        change (A _ _ + B _ _) + conj (A _ _ + B _ _) = _ + _
        rw [map_add]
        ring
    · rfl
  map_smul' c A := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext p
        change c • A _ _ + conj (c • A _ _) = c • (A _ _ + conj (A _ _))
        simp [smul_add]
    · rfl
  left_inv A := by
    funext i j
    dsimp only
    split_ifs with hij hlt
    · subst j
      rfl
    · exact add_sub_cancel_right _ _
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · funext i
        simp
      · funext p
        have hne : p.val.1 ≠ p.val.2 := ne_of_lt p.property
        have hnot : ¬ p.val.2 < p.val.1 := not_lt.mpr (le_of_lt p.property)
        simp only [dite_eq_right hne, dite_eq_left p.property,
          dite_eq_right (Ne.symm hne), dite_eq_right hnot, sub_add_cancel]
    · funext p
      have hne : p.val.2 ≠ p.val.1 := Ne.symm (ne_of_lt p.property)
      have hnot : ¬ p.val.2 < p.val.1 := not_lt.mpr (le_of_lt p.property)
      simp only [dite_eq_right hne, dite_eq_right hnot]

-- All formulas are on the original entries; the diagonal Gram value is real.
private def flagFrameCoordinateMap (r : ℕ) (A : Mat r) : Coordinates r :=
  ((fun i ↦ ((∑ k : Fin r, conj (A k i) * A k i) - 1) / 2 +
      Complex.I * (A i i).im,
    fun p ↦ ∑ k : Fin r, conj (A k p.val.1) * A k p.val.2),
    fun p ↦ A p.val.2 p.val.1)

private theorem flagFrameCoordinateMap_contDiff (r : ℕ) :
    ContDiff ℝ ∞ (flagFrameCoordinateMap r) := by
  unfold flagFrameCoordinateMap
  have hconj : ContDiff ℝ ∞ (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have hreal : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
  have him : ContDiff ℝ ∞ Complex.im := Complex.imCLM.contDiff
  fun_prop

private theorem flagFrameCoordinateMap_hasFDerivAt (r : ℕ) :
    HasFDerivAt (flagFrameCoordinateMap r)
      ((flagFrameLinearEquiv r).toContinuousLinearEquiv : Mat r →L[ℝ] Coordinates r)
      (1 : Mat r) := by
  let e (i j : Fin r) : Mat r →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A ↦ A i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  let conjL : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have he (i j : Fin r) : HasFDerivAt (fun A : Mat r ↦ A i j) (e i j) (1 : Mat r) :=
    (e i j).hasFDerivAt
  -- At the identity, the Gram differential is A + A*, in the original column order.
  have hgram (i j : Fin r) :
      HasFDerivAt (fun A : Mat r ↦ ∑ k : Fin r, conj (A k i) * A k j)
        (e i j + conjL.comp (e j i)) (1 : Mat r) := by
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
      ((conjL.hasFDerivAt.comp (1 : Mat r) (he k i)).mul (he k j)))
    refine h.congr_fderiv ?_
    ext A
    simp only [sum_apply]
    change (∑ k : Fin r,
      (conj ((1 : Mat r) k i) * A k j + (1 : Mat r) k j * conj (A k i))) =
        A i j + conj (A j i)
    simp [Matrix.one_apply, Finset.sum_add_distrib]
  have hdiag (i : Fin r) :
      HasFDerivAt (fun A : Mat r ↦ ((∑ k : Fin r, conj (A k i) * A k i) - 1) / 2 +
          Complex.I * (A i i).im) (e i i) (1 : Mat r) := by
    have him := (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt.comp (1 : Mat r) (he i i)
    have h := (((hgram i i).sub_const 1).mul_const (2⁻¹ : ℂ)).add (him.const_mul Complex.I)
    refine h.congr_fderiv ?_
    ext A
    change (2⁻¹ : ℂ) * (A i i + conj (A i i)) + Complex.I * (A i i).im = A i i
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  have h := ((hasFDerivAt_pi.mpr hdiag).prodMk
    (hasFDerivAt_pi.mpr (fun p : Pair r ↦ hgram p.val.1 p.val.2))).prodMk
      (hasFDerivAt_pi.mpr (fun p : Pair r ↦ he p.val.2 p.val.1))
  convert! h using 1

private theorem flagFrameCoordinateMap_zero_iff (r : ℕ) (A : Mat r) :
    (flagFrameCoordinateMap r A).1 = 0 ↔
      (∀ i j : Fin r, (∑ k : Fin r, conj (A k i) * A k j) = if i = j then 1 else 0) ∧
        ∀ i : Fin r, (A i i).im = 0 := by
  classical
  let gram (i j : Fin r) : ℂ := ∑ k : Fin r, conj (A k i) * A k j
  have hconj (i j : Fin r) : conj (gram i j) = gram j i := by
    simp [gram, map_sum, map_mul, mul_comm]
  have hreal (i : Fin r) : (gram i i).im = 0 := by
    have h := congrArg Complex.im (hconj i i)
    simp only [Complex.conj_im] at h
    linarith
  constructor
  · intro h
    have hd (i : Fin r) : (gram i i - 1) / 2 + Complex.I * (A i i).im = 0 :=
      congrArg (fun z : (Fin r → ℂ) × (Pair r → ℂ) ↦ z.1 i) h
    have ho (p : Pair r) : gram p.val.1 p.val.2 = 0 :=
      congrArg (fun z : (Fin r → ℂ) × (Pair r → ℂ) ↦ z.2 p) h
    have hi (i : Fin r) : (A i i).im = 0 := by
      have h := congrArg Complex.im (hd i)
      simpa [Complex.div_im, Complex.mul_im, hreal] using h
    refine ⟨?_, hi⟩
    intro i j
    change gram i j = _
    rcases lt_trichotomy i j with hij | hij | hij
    · simpa [ne_of_lt hij] using ho ⟨(i, j), hij⟩
    · subst j
      rw [ite_eq_left rfl]
      apply Complex.ext
      · have h := congrArg Complex.re (hd i)
        simp [Complex.mul_re] at h
        change (gram i i).re = 1
        linarith
      · simpa using hreal i
    · have h := (hconj j i).symm.trans (congrArg (starRingEnd ℂ) (ho ⟨(j, i), hij⟩))
      simpa [Ne.symm (ne_of_lt hij)] using h
  · rintro ⟨hgram, him⟩
    apply Prod.ext
    · funext i
      change (gram i i - 1) / 2 + Complex.I * (A i i).im = 0
      simp [gram, hgram, him]
    · funext p
      change gram p.val.1 p.val.2 = 0
      simpa [gram, ne_of_lt p.property] using hgram p.val.1 p.val.2

/-- The genuine Gram constraints admit smooth local coordinates near the identity frame. -/
theorem exists_hermitianFlagFrameSlice (r : ℕ) :
    ∃ e : OpenPartialHomeomorph (Mat r) (Coordinates r),
      (1 : Mat r) ∈ e.source ∧ e 1 = 0 ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
        (∀ A ∈ e.source, ∀ i : Fin r, 0 < (A i i).re) ∧
        (∀ A : Mat r, (e A).1 = 0 ↔
          (∀ i j : Fin r, (∑ k : Fin r, conj (A k i) * A k j) =
            if i = j then 1 else 0) ∧ ∀ i : Fin r, (A i i).im = 0) ∧
        ∀ A : Mat r, (e A).2 = fun p : Pair r ↦ A p.val.2 p.val.1 := by
  classical
  obtain ⟨e₀, hx, he, hs, ht⟩ := exists_smoothInverseChart (flagFrameCoordinateMap r)
    (flagFrameCoordinateMap_contDiff r) 1 (flagFrameLinearEquiv r).toContinuousLinearEquiv
      (flagFrameCoordinateMap_hasFDerivAt r)
  let U : Set (Mat r) := {A | ∀ i : Fin r, 0 < (A i i).re}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (Complex.continuous_re.comp
      ((continuous_apply i).comp (continuous_apply i)))
  let e := e₀.restrOpen U hU
  have he' : (e : Mat r → Coordinates r) = flagFrameCoordinateMap r := he
  refine ⟨e, ⟨hx, ?_⟩, ?_, hs.mono (fun _ h ↦ h.1), ?_, ?_, ?_, ?_⟩
  · intro i
    simp
  · rw [he']
    apply Prod.ext
    · apply Prod.ext
      · funext i
        simp [flagFrameCoordinateMap, Matrix.one_apply]
      · funext p
        simp [flagFrameCoordinateMap, Matrix.one_apply, Ne.symm (ne_of_lt p.property)]
    · funext p
      simp [flagFrameCoordinateMap, Matrix.one_apply, Ne.symm (ne_of_lt p.property)]
  · exact ht.mono (fun _ h ↦ h.1)
  · intro A hA
    exact hA.2
  · intro A
    rw [he']
    exact flagFrameCoordinateMap_zero_iff r A
  · intro A
    rw [he']
    rfl

end AtiyahSinger.ComplexBundle
