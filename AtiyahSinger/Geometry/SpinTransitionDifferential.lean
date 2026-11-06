/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinInfinitesimalAction
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The differential of the original spin transition

Public module ID: M1461.

The right logarithmic derivative of a differentiable map into the native spin
group is the bivector determined by the right logarithmic derivative of its
actual vector representation. The spin derivative takes values in the fixed Clifford
algebra; the vector derivative uses its given Euclidean model. This supplies the
differential identity in the local spin gauge law.

Source: Spin Geometry I.2 and II.4. The normalization and sign follow by
differentiating parity, the unit equation and the original conjugation formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

attribute [local instance] euclideanSpinCliffordNormedAddCommGroup
  euclideanSpinCliffordNormedSpace

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native spin transition and its vector matrix have the standard logarithmic derivatives. -/
theorem euclideanSpin_right_logarithmic_derivative (r : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → spinGroup (euclideanSpinQuadraticForm r)) (x X : E)
    (df : E →L[ℝ] CliffordAlgebra (euclideanSpinQuadraticForm r))
    (dG : E →L[ℝ] (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)))
    (hf : HasFDerivAt (fun y ↦ (f y).val) df x)
    (hG : HasFDerivAt
      (fun y ↦ (euclideanSpinVectorRepresentation r (f y)).toLinearMap.toContinuousLinearMap)
      dG x) :
    df X * ((f x)⁻¹ : spinGroup (euclideanSpinQuadraticForm r)).val =
      (1 / 4 : ℝ) • ∑ i : Fin r, ∑ j : Fin r,
        inner ℝ (dG X ((euclideanSpinVectorRepresentation r (f x)).symm
          (EuclideanSpace.basisFun (Fin r) ℝ i)))
          (EuclideanSpace.basisFun (Fin r) ℝ j) •
            (CliffordAlgebra.ι (euclideanSpinQuadraticForm r)
              (EuclideanSpace.basisFun (Fin r) ℝ i) *
              CliffordAlgebra.ι (euclideanSpinQuadraticForm r)
                (EuclideanSpace.basisFun (Fin r) ℝ j)) := by
  let V := EuclideanSpace ℝ (Fin r)
  let Q := euclideanSpinQuadraticForm r
  let C := CliffordAlgebra Q
  let : FiniteDimensional ℝ C :=
    FiniteDimensional.of_injective (euclideanSpinCliffordCoordinates r).toLinearMap
      (euclideanSpinCliffordCoordinates r).injective
  let product : C →L[ℝ] C →L[ℝ] C :=
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mul ℝ C)).toContinuousLinearMap
  let conjugate : C →L[ℝ] C :=
    (CliffordAlgebra.reverse.comp CliffordAlgebra.involute.toLinearMap).toContinuousLinearMap
  let involution : C →L[ℝ] C := CliffordAlgebra.involute.toLinearMap.toContinuousLinearMap
  let q : C := (f x).val
  let qi : C := ((f x)⁻¹ : spinGroup Q).val
  let δ : C := df X
  let G := euclideanSpinVectorRepresentation r (f x)
  let A : V →ₗ[ℝ] V := (dG X).toLinearMap.comp G.symm.toLinearMap
  have hleft : qi * q = 1 := spinGroup.star_mul_self_of_mem (f x).property
  -- Differentiating parity preserves evenness of the actual tangent Clifford element.
  have hevenδ : CliffordAlgebra.involute δ = δ := by
    have hd := involution.hasFDerivAt.comp x hf
    have heq : (fun y ↦ involution (f y).val) = fun y ↦ (f y).val := by
      funext y
      exact spinGroup.involute_eq (f y).property
    change HasFDerivAt (fun y ↦ involution (f y).val) (involution.comp df) x at hd
    rw [heq] at hd
    exact congrArg (fun L ↦ L X) (hd.unique hf)
  have heven : CliffordAlgebra.involute (δ * qi) = δ * qi := by
    rw [map_mul, hevenδ, spinGroup.involute_eq ((f x)⁻¹).property]
  -- The differentiated original inverse identity fixes the reversion-skew condition.
  have hnorm : q * conjugate δ + δ * qi = 0 := by
    have hd := product.hasFDerivAt_of_bilinear hf (conjugate.hasFDerivAt.comp x hf)
    have heq : (fun y ↦ product (f y).val (conjugate (f y).val)) = fun _ : E ↦ (1 : C) := by
      funext y
      exact spinGroup.mul_star_self_of_mem (f y).property
    change HasFDerivAt (fun y ↦ product (f y).val (conjugate (f y).val)) _ x at hd
    rw [heq] at hd
    exact congrArg (fun L ↦ L X) (hd.unique (hasFDerivAt_const (1 : C) x))
  have hreverse : CliffordAlgebra.reverse (δ * qi) = -(δ * qi) := by
    have hreverseqi : CliffordAlgebra.reverse qi = q := by
      change CliffordAlgebra.reverse (CliffordAlgebra.reverse (CliffordAlgebra.involute q)) = q
      rw [CliffordAlgebra.reverse_reverse, spinGroup.involute_eq (f x).property]
    have hreverseδ : CliffordAlgebra.reverse δ = conjugate δ := by
      change CliffordAlgebra.reverse δ = CliffordAlgebra.reverse (CliffordAlgebra.involute δ)
      rw [hevenδ]
    rw [CliffordAlgebra.reverse.map_mul, hreverseqi, hreverseδ]
    exact eq_neg_of_add_eq_zero_left hnorm
  -- Differentiate the same vector representation and its preserved inner product.
  have hvector (v : V) : HasFDerivAt
      (fun y ↦ euclideanSpinVectorRepresentation r (f y) v)
      ((ContinuousLinearMap.apply ℝ V v).comp dG) x :=
    (ContinuousLinearMap.apply ℝ V v).hasFDerivAt.comp x hG
  have hskew : ∀ v w : V, inner ℝ (A v) w = -inner ℝ v (A w) := by
    intro v w
    have hd := (hvector (G.symm v)).inner ℝ (hvector (G.symm w))
    have heq : (fun y ↦ inner ℝ
        (euclideanSpinVectorRepresentation r (f y) (G.symm v))
        (euclideanSpinVectorRepresentation r (f y) (G.symm w))) =
          fun _ : E ↦ inner ℝ (G.symm v) (G.symm w) := by
      funext y
      let L : V →ₗᵢ[ℝ] V :=
        { toLinearMap := (euclideanSpinVectorRepresentation r (f y)).toLinearMap
          norm_map' := fun z ↦ (euclideanSpinVectorRepresentation_properties r (f y) z).2.1 }
      exact L.inner_map_map _ _
    rw [heq] at hd
    have h := congrArg (fun L ↦ L X)
      (hd.unique (hasFDerivAt_const (inner ℝ (G.symm v) (G.symm w)) x))
    change inner ℝ (G (G.symm v)) (dG X (G.symm w)) +
      inner ℝ (dG X (G.symm v)) (G (G.symm w)) = 0 at h
    rw [G.apply_symm_apply, G.apply_symm_apply] at h
    exact eq_neg_of_add_eq_zero_right h
  -- The original conjugation identity gives the commutator with every vector.
  have hcomm : ∀ v : V,
      (δ * qi) * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * (δ * qi) =
        CliffordAlgebra.ι Q (A v) := by
    intro v
    let w := G.symm v
    let j : V →L[ℝ] C := (CliffordAlgebra.ι Q).toContinuousLinearMap
    have hd := j.hasFDerivAt.comp x (hvector w)
    have hc := product.hasFDerivAt_of_bilinear
      ((product.flip (j w)).hasFDerivAt.comp x hf) (conjugate.hasFDerivAt.comp x hf)
    have heq : (fun y ↦ j (euclideanSpinVectorRepresentation r (f y) w)) =
        fun y ↦ product (product (f y).val (j w)) (conjugate (f y).val) := by
      funext y
      exact (euclideanSpinVectorRepresentation_properties r (f y) w).1
    change HasFDerivAt (fun y ↦ j (euclideanSpinVectorRepresentation r (f y) w)) _ x at hd
    rw [heq] at hd
    have h := congrArg (fun L ↦ L X) (hd.unique hc)
    change j (dG X w) = (q * j w) * conjugate δ + (δ * j w) * qi at h
    have hw : q * j w * qi = j v := by
      have hformula := (euclideanSpinVectorRepresentation_properties r (f x) w).1
      change j (G (G.symm v)) = q * j w * qi at hformula
      rw [G.apply_symm_apply] at hformula
      exact hformula.symm
    have hfirst : (q * j w) * conjugate δ = -(j v * (δ * qi)) := by
      calc
        (q * j w) * conjugate δ = (q * j w * qi) * (q * conjugate δ) := by
          simp only [mul_assoc]
          rw [← mul_assoc qi q, hleft, one_mul]
        _ = j v * (-(δ * qi)) := by rw [hw, eq_neg_of_add_eq_zero_left hnorm]
        _ = _ := mul_neg _ _
    have hsecond : (δ * j w) * qi = (δ * qi) * j v := by
      rw [← hw]
      simp only [mul_assoc]
      rw [← mul_assoc qi q, hleft, one_mul]
    change (δ * qi) * j v - j v * (δ * qi) = j (dG X w)
    rw [h, hfirst, hsecond]
    abel
  exact euclideanSpin_eq_bivector_of_commutator r (δ * qi) A hskew heven hreverse hcomm

end AtiyahSinger
