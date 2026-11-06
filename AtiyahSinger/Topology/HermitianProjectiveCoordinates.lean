/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveBundle
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Vector representatives and affine coordinates for orthogonal projective space

Public module ID: M1895.

A nonzero vector determines its actual orthogonal rank-one projector.
Uniqueness follows from self-adjointness and the one-dimensional range.
Normalization of the projected reference vector gives the affine hyperplane
where its inner product is one. For a unit reference vector, translation
identifies this hyperplane with its orthogonal complement.

Source: the usual affine charts of complex projective space, expressed in
the original orthogonal-projection model. No choice of a global unit-vector
representative is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The orthogonal projector represented by a nonzero vector. -/
def ofVector (v : V) (hv : v ≠ 0) : HermitianProjectiveSpace V InnerProductSpace.toCore := by
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  exact ⟨InnerProductSpace.rankOne ℂ w w,
    InnerProductSpace.isIdempotentElem_rankOne_self hw,
    Module.rank_eq_one_iff_finrank_eq_one.mp (InnerProductSpace.rank_rankOne hwne hwne),
    InnerProductSpace.isSymmetric_rankOne_self w⟩

/-- A unit vector in the range determines the complete rank-one orthogonal projection formula. -/
theorem apply_eq_inner_smul (P : HermitianProjectiveSpace V InnerProductSpace.toCore)
    (v : V) (hv : ‖v‖ = 1) (hPv : P.val v = v) (w : V) :
    P.val w = inner ℂ v w • v := by
  -- The range has dimension one, so every projected vector is a scalar multiple of v.
  let v' : LinearMap.range P.val.toLinearMap := ⟨v, ⟨v, hPv⟩⟩
  have hv' : v' ≠ 0 := by
    intro hzero
    have hz : v = 0 := congrArg Subtype.val hzero
    rw [hz, norm_zero] at hv
    exact zero_ne_one hv
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one P.property.2.1 hv'
    (⟨P.val w, LinearMap.mem_range_self _ w⟩ : LinearMap.range P.val.toLinearMap)
  have haw : a • v = P.val w := congrArg Subtype.val ha
  -- Self-adjointness and the unit norm recover that scalar as the specified inner product.
  have hinner : inner ℂ v w = a := by
    calc
      inner ℂ v w = inner ℂ v (P.val w) := by
        rw [← P.property.2.2, hPv]
      _ = a := by rw [← haw, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]; simp
  rw [hinner]
  exact haw.symm

/-- Two orthogonal rank-one projectors fixing the same nonzero vector are equal. -/
theorem eq_of_fixed_nonzero (P Q : HermitianProjectiveSpace V InnerProductSpace.toCore)
    (v : V) (hv : v ≠ 0) (hPv : P.val v = v) (hQv : Q.val v = v) : P = Q := by
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  have hPw : P.val w = w := by
    change P.val (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
    exact ((P.val.restrictScalars ℝ).map_smul ‖v‖⁻¹ v).trans
      (congrArg (fun z ↦ ‖v‖⁻¹ • z) hPv)
  have hQw : Q.val w = w := by
    change Q.val (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
    exact ((Q.val.restrictScalars ℝ).map_smul ‖v‖⁻¹ v).trans
      (congrArg (fun z ↦ ‖v‖⁻¹ • z) hQv)
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro z
  rw [apply_eq_inner_smul P w hw hPw, apply_eq_inner_smul Q w hw hQw]

/-- The orthogonal projector of a nonzero vector fixes that original vector. -/
theorem ofVector_apply_self (v : V) (hv : v ≠ 0) : (ofVector v hv).val v = v := by
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  have hvw : ‖v‖ • w = v := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hfix : (ofVector v hv).val w = w := by
    change inner ℂ w w • w = w
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  calc
    (ofVector v hv).val v = (ofVector v hv).val (‖v‖ • w) :=
      congrArg (ofVector v hv).val hvw.symm
    _ = ‖v‖ • (ofVector v hv).val w :=
      ((ofVector v hv).val.restrictScalars ℝ).map_smul ‖v‖ w
    _ = v := (congrArg (fun z ↦ ‖v‖ • z) hfix).trans hvw

/-- Every nonzero fixed vector gives the same original projector. -/
theorem ofVector_eq (P : HermitianProjectiveSpace V InnerProductSpace.toCore)
    (v : V) (hv : v ≠ 0) (hPv : P.val v = v) : ofVector v hv = P :=
  eq_of_fixed_nonzero _ P v hv (ofVector_apply_self v hv) hPv

/-- The projector depends continuously on the nonzero vector before passing to projective space. -/
theorem continuous_ofVector :
    Continuous (fun v : {v : V // v ≠ 0} ↦ ofVector v.val v.property) := by
  have hw : Continuous (fun v : {v : V // v ≠ 0} ↦ ‖v.val‖⁻¹ • v.val) :=
    (continuous_subtype_val.norm.inv₀ (fun v ↦ norm_ne_zero_iff.mpr v.property)).smul
      continuous_subtype_val
  apply Continuous.subtype_mk
  change Continuous (fun v : {v : V // v ≠ 0} ↦
    (innerSL ℂ (‖v.val‖⁻¹ • v.val)).smulRight (‖v.val‖⁻¹ • v.val))
  exact ((ContinuousLinearMap.smulRightL ℂ V V).continuous.comp
    ((innerSL ℂ).continuous.comp hw)).clm_apply hw

/-- The affine chart normalizes the actual projection of its reference vector.
The zero reference vector gives the homeomorphism between the two empty subspaces. -/
def affineChart (e : V) :
    {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P.val e ≠ 0} ≃ₜ
      {v : V // inner ℂ e v = 1} := by
  let D := {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P.val e ≠ 0}
  let A := {v : V // inner ℂ e v = 1}
  have hden (P : D) : inner ℂ e (P.val.val e) ≠ 0 := by
    intro hz
    have hid : P.val.val (P.val.val e) = P.val.val e :=
      congrArg (fun f : V →L[ℂ] V ↦ f e) P.val.property.1
    have hi : inner ℂ (P.val.val e) (P.val.val e) = 0 := by
      rw [P.val.property.2.2, hid, hz]
    exact P.property (inner_self_eq_zero.mp hi)
  have hne (v : A) : v.val ≠ 0 := by
    intro hv
    have h := v.property
    rw [hv, inner_zero_right] at h
    exact zero_ne_one h
  let φ (P : D) : A :=
    ⟨(inner ℂ e (P.val.val e))⁻¹ • P.val.val e, by
      rw [inner_smul_right, inv_mul_cancel₀ (hden P)]⟩
  have hsource (v : A) : (ofVector v.val (hne v)).val e ≠ 0 := by
    intro hzero
    have hs := (ofVector v.val (hne v)).property.2.2 e v.val
    rw [ofVector_apply_self, hzero, inner_zero_left, v.property] at hs
    exact zero_ne_one hs
  let ψ (v : A) : D := ⟨ofVector v.val (hne v), hsource v⟩
  -- Normalization preserves the original one-dimensional range in both directions.
  have hleft (P : D) : ψ (φ P) = P := by
    apply Subtype.ext
    apply ofVector_eq P.val (φ P).val (hne (φ P))
    change P.val.val ((inner ℂ e (P.val.val e))⁻¹ • P.val.val e) = _
    rw [map_smul]
    exact congrArg (fun z ↦ (inner ℂ e (P.val.val e))⁻¹ • z)
      (congrArg (fun f : V →L[ℂ] V ↦ f e) P.val.property.1)
  have hright (v : A) : φ (ψ v) = v := by
    let P := ofVector v.val (hne v)
    let w : LinearMap.range P.val.toLinearMap := ⟨v.val, ⟨v.val, ofVector_apply_self _ _⟩⟩
    have hw : w ≠ 0 := fun h ↦ hne v (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one P.property.2.1 hw
      (⟨P.val e, LinearMap.mem_range_self _ e⟩ : LinearMap.range P.val.toLinearMap)
    have hav : a • v.val = P.val e := congrArg Subtype.val ha
    have hane : a ≠ 0 := by
      intro hz
      apply hsource v
      rw [← hav, hz, zero_smul]
    have hcoeff : inner ℂ e (P.val e) = a := by
      rw [← hav, inner_smul_right, v.property, mul_one]
    apply Subtype.ext
    change (inner ℂ e (P.val e))⁻¹ • P.val e = v.val
    rw [hcoeff, ← hav, smul_smul, inv_mul_cancel₀ hane, one_smul]
  -- Continuity is checked on the same nonzero projected vector, without choosing its phase.
  have hPe : Continuous (fun P : D ↦ P.val.val e) :=
    (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    exact ((continuous_const.inner hPe).inv₀ hden).smul hPe
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    change Continuous (fun v : A ↦ ofVector v.val (hne v))
    apply Continuous.subtype_mk
    have hw : Continuous (fun v : A ↦ ‖v.val‖⁻¹ • v.val) :=
      (continuous_subtype_val.norm.inv₀ (fun v ↦ norm_ne_zero_iff.mpr (hne v))).smul
        continuous_subtype_val
    change Continuous (fun v : A ↦
      (innerSL ℂ (‖v.val‖⁻¹ • v.val)).smulRight (‖v.val‖⁻¹ • v.val))
    exact ((ContinuousLinearMap.smulRightL ℂ V V).continuous.comp
      ((innerSL ℂ).continuous.comp hw)).clm_apply hw
  exact
    { toEquiv := { toFun := φ, invFun := ψ, left_inv := hleft, right_inv := hright }
      continuous_toFun := hφ
      continuous_invFun := hψ }

/-- The domain of the affine chart is open in the original projector subspace topology. -/
theorem isOpen_affineChart_source (e : V) :
    IsOpen {P : HermitianProjectiveSpace V InnerProductSpace.toCore | P.val e ≠ 0} :=
  isOpen_ne_fun (continuous_subtype_val.clm_apply continuous_const) continuous_const

/-- Translation by a unit reference vector identifies the affine chart with its orthogonal space. -/
def affineHyperplaneHomeomorph (e : V) (he : ‖e‖ = 1) :
    (innerSL ℂ e).ker ≃ₜ {v : V // inner ℂ e v = 1} := by
  have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
  refine
    { toFun := fun w ↦ ⟨e + w.val, by
        rw [inner_add_right, hee, show inner ℂ e w.val = 0 from w.property, add_zero]⟩
      invFun := fun v ↦ ⟨v.val - e, by
        change inner ℂ e (v.val - e) = 0
        rw [inner_sub_right, v.property, hee, sub_self]⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_const.add continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.sub continuous_const }
  · intro w
    apply Subtype.ext
    simp
  · intro v
    apply Subtype.ext
    simp

/-- The actual affine projective chart takes values in the orthogonal complement. -/
def chart (e : V) (he : ‖e‖ = 1) :
    {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P.val e ≠ 0} ≃ₜ
      (innerSL ℂ e).ker :=
  (affineChart e).trans (affineHyperplaneHomeomorph e he).symm

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
