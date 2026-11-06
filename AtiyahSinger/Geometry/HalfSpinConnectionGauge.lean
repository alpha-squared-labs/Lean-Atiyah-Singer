/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HalfSpinBivector
public import AtiyahSinger.Geometry.SpinBivectorCovariance
public import AtiyahSinger.Geometry.SpinTransitionDifferential

/-!
# The actual half-spin representation in the connection gauge law

Public module ID: M1262.

The differential of the original parity representation is the prescribed
one-quarter Clifford bivector. The comparison uses the actual Clifford algebra
and Spin group equivalences induced by the fixed interleaved coordinate isometry.
No equality of the two original Spin group carriers is assumed.

Source: Spin Geometry I.2 and II.4, with the project's negative quadratic form.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

attribute [local instance] realSpinorCliffordNormedAddCommGroup
  realSpinorCliffordNormedSpace euclideanSpinCliffordNormedAddCommGroup
  euclideanSpinCliffordNormedSpace exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Ambient differentiability of a Spin map gives differentiability of its parity operators. -/
theorem differentiableAt_complexSpinParityContRepresentation (m : ℕ) (i : ZMod 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → spinGroup (realSpinorQuadraticForm m)) (x : E)
    (hf : DifferentiableAt ℝ (fun y ↦ (f y).val) x) :
    DifferentiableAt ℝ (fun y ↦ complexSpinParityContRepresentation m i (f y)) x := by
  let C := CliffordAlgebra (realSpinorQuadraticForm m)
  let S := ComplexSpinor m
  let p := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let : FiniteDimensional ℝ C :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  -- Any linear retraction only extends the operator off the parity subspace.
  -- Its restriction to Spin is exactly the original action, independent of that choice.
  obtain ⟨q, hq⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  let L : C →ₗ[ℝ] (p →ₗ[ℂ] p) :=
    { toFun := fun a ↦ q.comp ((realSpinorRepresentation m a).comp p.subtype)
      map_add' := by intro a b; ext s; simp
      map_smul' := by intro a b; ext s; simp }
  let T : C →L[ℝ] (p →L[ℂ] p) :=
    (((LinearMap.toContinuousLinearMap.toLinearMap :
      (p →ₗ[ℂ] p) →ₗ[ℂ] (p →L[ℂ] p)).restrictScalars ℝ).comp L).toContinuousLinearMap
  have hT (g : spinGroup (realSpinorQuadraticForm m)) :
      T g.val = complexSpinParityContRepresentation m i g := by
    apply ContinuousLinearMap.ext
    intro s
    have h := congrArg (fun L ↦ L (complexSpinParityContRepresentation m i g s)) hq
    exact h
  have hd := T.differentiableAt.comp x hf
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y ↦ (hT (f y)).symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem halfSpinDerivative_apply (m : ℕ) (i : ZMod 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → spinGroup (realSpinorQuadraticForm m)) (x X : E)
    (df : E →L[ℝ] CliffordAlgebra (realSpinorQuadraticForm m))
    (dR : E →L[ℝ] ((CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)))
    (hf : HasFDerivAt (fun y ↦ (f y).val) df x)
    (hR : HasFDerivAt (fun y ↦ complexSpinParityContRepresentation m i (f y)) dR x)
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    (dR X s).val = realSpinorRepresentation m (df X) s.val := by
  let C := CliffordAlgebra (realSpinorQuadraticForm m)
  let p := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let : FiniteDimensional ℝ C :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  let U : C →ₗ[ℝ] ComplexSpinor m :=
    { toFun := fun a ↦ realSpinorRepresentation m a s.val
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp }
  let Q : (p →L[ℂ] p) →L[ℝ] ComplexSpinor m :=
    (p.subtypeL.restrictScalars ℝ).comp ((ContinuousLinearMap.apply ℂ p s).restrictScalars ℝ)
  have hleft := Q.hasFDerivAt.comp x hR
  have hright := U.toContinuousLinearMap.hasFDerivAt.comp x hf
  change HasFDerivAt (fun y ↦ realSpinorRepresentation m (f y).val s.val) _ x at hleft
  exact congrArg (fun L ↦ L X) (hleft.unique hright)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem halfSpinClifford_right_logarithmic_derivative (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → spinGroup (realSpinorQuadraticForm m)) (x X : E)
    (df : E →L[ℝ] CliffordAlgebra (realSpinorQuadraticForm m))
    (dG : E →L[ℝ] (EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * m))))
    (hf : HasFDerivAt (fun y ↦ (f y).val) df x)
    (hG : HasFDerivAt (fun y ↦ (euclideanSpinVectorRepresentation (2 * m)
      ((euclideanSpinEvenEquiv m).symm (f y))).toLinearMap.toContinuousLinearMap) dG x) :
    let G := euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f x))
    df X * ((f x)⁻¹ : spinGroup (realSpinorQuadraticForm m)).val =
      euclideanSpinCliffordEvenEquiv m
        ((1 / 4 : ℝ) • ∑ a : Fin (2 * m), ∑ b : Fin (2 * m),
          inner ℝ (dG X (G.symm (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a)))
            (EuclideanSpace.basisFun (Fin (2 * m)) ℝ b) •
              (CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
                (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a) *
                CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
                  (EuclideanSpace.basisFun (Fin (2 * m)) ℝ b))) := by
  let C := CliffordAlgebra (realSpinorQuadraticForm m)
  let : FiniteDimensional ℝ C :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  let T := (euclideanSpinCliffordEvenEquiv m).symm.toLinearMap.toContinuousLinearMap
  let F := fun y ↦ (euclideanSpinEvenEquiv m).symm (f y)
  have hF : HasFDerivAt (fun y ↦ (F y).val) (T.comp df) x := T.hasFDerivAt.comp x hf
  have h := congrArg (euclideanSpinCliffordEvenEquiv m)
    (euclideanSpin_right_logarithmic_derivative (2 * m) F x X (T.comp df) dG hF hG)
  have hinv : euclideanSpinCliffordEvenEquiv m (F x)⁻¹.val =
      ((f x)⁻¹ : spinGroup (realSpinorQuadraticForm m)).val := by
    exact congrArg Subtype.val (((euclideanSpinEvenEquiv m).map_inv (F x)).trans
      (congrArg Inv.inv ((euclideanSpinEvenEquiv m).apply_symm_apply (f x))))
  change euclideanSpinCliffordEvenEquiv m
    ((euclideanSpinCliffordEvenEquiv m).symm (df X) * (F x)⁻¹.val) = _ at h
  rw [map_mul, AlgEquiv.apply_symm_apply, hinv] at h
  exact h

private theorem halfSpinContraction_eq (m : ℕ)
    (A : EuclideanSpace ℝ (Fin (2 * m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    let j := CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
    (∑ a : Fin (2 * m), ∑ k : Fin (2 * m), inner ℝ (A (b a)) (b k) • (j (b a) * j (b k))) =
      ∑ a : Fin (2 * m), j (b a) * j (A (b a)) := by
  dsimp only
  let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  apply Finset.sum_congr rfl
  intro a _
  have hvec : A (b a) = ∑ k : Fin (2 * m), inner ℝ (A (b a)) (b k) • b k := by
    simpa only [real_inner_comm] using (b.sum_repr' (A (b a))).symm
  nth_rw 2 [hvec]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rfl

private theorem halfSpinBivector_double_apply (m : ℕ) (i : ZMod 2)
    (ω : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    realSpinorRepresentation m (euclideanSpinCliffordEvenEquiv m
      ((1 / 4 : ℝ) • ∑ a : Fin (2 * m), ∑ b : Fin (2 * m), ω a b •
        (CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
          (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a) *
          CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
            (EuclideanSpace.basisFun (Fin (2 * m)) ℝ b)))) s.val =
      (halfSpinBivector m i ω s).val := by
  have hj (v : EuclideanSpace ℝ (Fin (2 * m))) :
      euclideanSpinCliffordEvenEquiv m
          (CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m)) v) =
        CliffordAlgebra.ι (realSpinorQuadraticForm m) (realSpinorCoordinateIsometry m v) :=
    CliffordAlgebra.map_apply_ι _ v
  rw [halfSpinBivector_apply]
  simp only [map_smul, map_sum, map_mul, hj, realSpinorRepresentation_ι,
    LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
  simp only [Complex.coe_smul]

private theorem halfSpinBivector_contraction_apply (m : ℕ) (i : ZMod 2)
    (A : EuclideanSpace ℝ (Fin (2 * m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m)))
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    let j := CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
    realSpinorRepresentation m (euclideanSpinCliffordEvenEquiv m
      ((1 / 4 : ℝ) • ∑ a : Fin (2 * m), j (b a) * j (A (b a)))) s.val =
      (halfSpinBivector m i (fun a k ↦ inner ℝ (A (b a)) (b k)) s).val := by
  dsimp only
  rw [← halfSpinContraction_eq m A]
  exact halfSpinBivector_double_apply m i _ s

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem halfSpinBivector_covariant (m : ℕ) (i : ZMod 2)
    (g : spinGroup (realSpinorQuadraticForm m))
    (A : EuclideanSpace ℝ (Fin (2 * m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m)))
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    let G := euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm g)
    complexSpinParityContRepresentation m i g
        (halfSpinBivector m i (fun a k ↦ inner ℝ (A (b a)) (b k)) s) =
      halfSpinBivector m i (fun a k ↦ inner ℝ (G (A (G.symm (b a)))) (b k))
        (complexSpinParityContRepresentation m i g s) := by
  dsimp only
  let q := (euclideanSpinEvenEquiv m).symm g
  let G := euclideanSpinVectorRepresentation (2 * m) q
  let C := G.toLinearMap.comp (A.comp G.symm.toLinearMap)
  let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let j := CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
  let B (T : EuclideanSpace ℝ (Fin (2 * m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :=
    (1 / 4 : ℝ) • ∑ a : Fin (2 * m), j (b a) * j (T (b a))
  have hconj : q.val * B A * (q⁻¹ : spinGroup (euclideanSpinQuadraticForm (2 * m))).val =
      B C := by
    have h := congrArg (fun z ↦ (1 / 4 : ℝ) • z)
      (euclideanSpin_conjugate_bivector (2 * m) q A)
    simpa only [B, C, b, j, G, LinearMap.comp_apply, LinearEquiv.coe_coe,
      mul_smul_comm, smul_mul_assoc] using h
  have hinv : (q⁻¹ : spinGroup (euclideanSpinQuadraticForm (2 * m))).val * q.val = 1 :=
    spinGroup.star_mul_self_of_mem q.property
  have hmul : q.val * B A = B C * q.val := by
    have h := congrArg (fun z ↦ z * q.val) hconj
    simpa only [mul_assoc, hinv, mul_one] using h
  have hg : euclideanSpinCliffordEvenEquiv m q.val = g.val :=
    congrArg Subtype.val ((euclideanSpinEvenEquiv m).apply_symm_apply g)
  have h := congrArg (fun z ↦ realSpinorRepresentation m (euclideanSpinCliffordEvenEquiv m z)
    s.val) hmul
  simp only [map_mul, Module.End.mul_apply, hg] at h
  have hA := halfSpinBivector_contraction_apply m i A s
  have hC := halfSpinBivector_contraction_apply m i C
    (complexSpinParityContRepresentation m i g s)
  apply Subtype.ext
  change realSpinorRepresentation m g.val
    (halfSpinBivector m i (fun a k ↦ inner ℝ (A (b a)) (b k)) s).val =
      (halfSpinBivector m i (fun a k ↦ inner ℝ (C (b a)) (b k))
        (complexSpinParityContRepresentation m i g s)).val
  exact (congrArg (realSpinorRepresentation m g.val) hA.symm).trans (h.trans hC)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The derivative of the actual parity operator is the prescribed right-logarithmic bivector. -/
theorem complexSpinParityContRepresentation_derivative (m : ℕ) (i : ZMod 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → spinGroup (realSpinorQuadraticForm m)) (x X : E)
    (df : E →L[ℝ] CliffordAlgebra (realSpinorQuadraticForm m))
    (dG : E →L[ℝ] (EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * m))))
    (dR : E →L[ℝ] ((CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)))
    (hf : HasFDerivAt (fun y ↦ (f y).val) df x)
    (hG : HasFDerivAt (fun y ↦ (euclideanSpinVectorRepresentation (2 * m)
      ((euclideanSpinEvenEquiv m).symm (f y))).toLinearMap.toContinuousLinearMap) dG x)
    (hR : HasFDerivAt (fun y ↦ complexSpinParityContRepresentation m i (f y)) dR x)
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    let G := euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f x))
    dR X s = halfSpinBivector m i
      (fun a k ↦ inner ℝ (dG X (G.symm (b a))) (b k))
      (complexSpinParityContRepresentation m i (f x) s) := by
  dsimp only
  let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let G := euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f x))
  let ω := fun a k ↦ inner ℝ (dG X (G.symm (b a))) (b k)
  let j := CliffordAlgebra.ι (euclideanSpinQuadraticForm (2 * m))
  let a := euclideanSpinCliffordEvenEquiv m
    ((1 / 4 : ℝ) • ∑ v : Fin (2 * m), ∑ w : Fin (2 * m), ω v w • (j (b v) * j (b w)))
  -- Multiply the original right logarithmic identity by the same Spin element.
  have hlog : df X * ((f x)⁻¹ : spinGroup (realSpinorQuadraticForm m)).val = a :=
    halfSpinClifford_right_logarithmic_derivative m f x X df dG hf hG
  have hinv : ((f x)⁻¹ : spinGroup (realSpinorQuadraticForm m)).val * (f x).val = 1 :=
    spinGroup.star_mul_self_of_mem (f x).property
  have hdf : df X = a * (f x).val := by
    have h := congrArg (fun z ↦ z * (f x).val) hlog
    simpa only [mul_assoc, hinv, mul_one] using h
  have h := congrArg (fun z ↦ realSpinorRepresentation m z s.val) hdf
  rw [map_mul, Module.End.mul_apply] at h
  apply Subtype.ext
  exact (halfSpinDerivative_apply m i f x X df dR hf hR s).trans
    (h.trans (halfSpinBivector_double_apply m i ω
      (complexSpinParityContRepresentation m i (f x) s)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original vector gauge law induces the same gauge law on the actual half-spin operators. -/
theorem halfSpinBivector_gauge (m : ℕ) (i : ZMod 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → spinGroup (realSpinorQuadraticForm m)) (x X : E)
    (df : E →L[ℝ] CliffordAlgebra (realSpinorQuadraticForm m))
    (dG : E →L[ℝ] (EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * m))))
    (dR : E →L[ℝ] ((CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)))
    (hf : HasFDerivAt (fun y ↦ (f y).val) df x)
    (hG : HasFDerivAt (fun y ↦ (euclideanSpinVectorRepresentation (2 * m)
      ((euclideanSpinEvenEquiv m).symm (f y))).toLinearMap.toContinuousLinearMap) dG x)
    (hR : HasFDerivAt (fun y ↦ complexSpinParityContRepresentation m i (f y)) dR x)
    (Aa Ab : EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    let G := euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f x))
    (∀ v, Ab (G v) + dG X v = G (Aa v)) →
    ∀ s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i,
      halfSpinBivector m i (fun a k ↦ inner ℝ (Ab (b a)) (b k))
          (complexSpinParityContRepresentation m i (f x) s) + dR X s =
        complexSpinParityContRepresentation m i (f x)
          (halfSpinBivector m i (fun a k ↦ inner ℝ (Aa (b a)) (b k)) s) := by
  dsimp only
  intro hgauge s
  let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let G := euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f x))
  let L := (dG X).comp G.symm.toLinearMap.toContinuousLinearMap
  let C := G.toLinearMap.toContinuousLinearMap.comp
    (Aa.comp G.symm.toLinearMap.toContinuousLinearMap)
  let matrix (T : EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :=
    fun a k ↦ inner ℝ (T (b a)) (b k)
  -- The vector identity is conjugation plus the same right logarithmic derivative.
  have hlinear : Ab + L = C := by
    apply ContinuousLinearMap.ext
    intro v
    change Ab v + dG X (G.symm v) = G (Aa (G.symm v))
    have h := hgauge (G.symm v)
    change Ab (G (G.symm v)) + dG X (G.symm v) = G (Aa (G.symm v)) at h
    rw [G.apply_symm_apply] at h
    exact h
  have hmatrix : matrix Ab + matrix L = matrix C := by
    funext a k
    change inner ℝ (Ab (b a)) (b k) + inner ℝ (L (b a)) (b k) =
      inner ℝ (C (b a)) (b k)
    rw [← inner_add_left]
    exact congrArg (fun T ↦ inner ℝ (T (b a)) (b k)) hlinear
  have hB : halfSpinBivector m i (matrix Ab) + halfSpinBivector m i (matrix L) =
      halfSpinBivector m i (matrix C) :=
    (map_add (halfSpinBivector m i) (matrix Ab) (matrix L)).symm.trans
      (congrArg (halfSpinBivector m i) hmatrix)
  have hder : dR X s = halfSpinBivector m i (matrix L)
      (complexSpinParityContRepresentation m i (f x) s) :=
    complexSpinParityContRepresentation_derivative m i f x X df dG dR hf hG hR s
  have hconj := halfSpinBivector_covariant m i (f x) Aa.toLinearMap s
  calc
    _ = (halfSpinBivector m i (matrix Ab) + halfSpinBivector m i (matrix L))
        (complexSpinParityContRepresentation m i (f x) s) := by rw [hder]; rfl
    _ = halfSpinBivector m i (matrix C)
        (complexSpinParityContRepresentation m i (f x) s) :=
      congrArg (fun T ↦ T (complexSpinParityContRepresentation m i (f x) s)) hB
    _ = _ := hconj.symm

end AtiyahSinger
