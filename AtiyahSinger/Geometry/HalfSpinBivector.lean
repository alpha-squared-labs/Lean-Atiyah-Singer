/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinCoordinates
public import AtiyahSinger.Geometry.SpinorHermitianMetric

/-!
# The standard bivector action on the original half-spin spaces

Public module ID: M1261.

The one-quarter double Clifford sum is a real-linear function of the coefficient
matrix and a complex-linear endomorphism of each original parity space. A real
skew coefficient matrix gives a skew endomorphism for the original Fock pairing.
These are the model operators in the Levi-Civita spin connection.

Source: Spin Geometry II.4, with the original negative quadratic form and
the fixed interleaved real coordinate isometry from SpinCoordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators ComplexConjugate

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

/-- The standard one-quarter Clifford action of a real coefficient matrix on one parity space. -/
def halfSpinBivector (m : ℕ) (i : ZMod 2) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ →ₗ[ℝ]
      ((CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)) := by
  let V := EuclideanSpace ℂ (Fin m)
  let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let e (a : Fin (2 * m)) :=
    realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a)
  let K (a b : Fin (2 * m)) : W →ₗ[ℂ] W :=
    { toFun := fun s ↦ ⟨cliffordSymbol (e a) (cliffordSymbol (e b) s.val), by
        have h := cliffordSymbol_mem_evenOdd (e a) (i + 1)
          (cliffordSymbol (e b) s.val) (cliffordSymbol_mem_evenOdd (e b) i s.val s.property)
        simpa only [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero] using h⟩
      map_add' := by
        intro s t
        apply Subtype.ext
        change cliffordSymbol (e a) (cliffordSymbol (e b) (s.val + t.val)) =
          cliffordSymbol (e a) (cliffordSymbol (e b) s.val) +
            cliffordSymbol (e a) (cliffordSymbol (e b) t.val)
        simp only [map_add]
      map_smul' := by
        intro c s
        apply Subtype.ext
        change cliffordSymbol (e a) (cliffordSymbol (e b) (c • s.val)) =
          c • cliffordSymbol (e a) (cliffordSymbol (e b) s.val)
        simp only [map_smul] }
  let entry (a b : Fin (2 * m)) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun ω ↦ ω a b
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (1 / 4 : ℝ) • ∑ a : Fin (2 * m), ∑ b : Fin (2 * m),
    (entry a b).smulRight (K a b).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The parity endomorphism has precisely the original full-exterior double-sum formula. -/
theorem halfSpinBivector_apply (m : ℕ) (i : ZMod 2)
    (ω : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    (halfSpinBivector m i ω s).val =
      (1 / 4 : ℂ) • ∑ a : Fin (2 * m), ∑ b : Fin (2 * m), (ω a b : ℂ) •
        cliffordSymbol
          (realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a))
          (cliffordSymbol
            (realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ b))
            s.val) := by
  simp only [halfSpinBivector, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply,
    smul_apply, sum_apply, LinearMap.coe_toContinuousLinearMap']
  simp only [Complex.coe_smul]
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
  simp only [Submodule.coe_smul_of_tower, Submodule.coe_sum]
  rfl

/-- Real skew connection coefficients act skewly for the original Fock pairing. -/
theorem spinorFockPairing_halfSpinBivector (m : ℕ) (i : ZMod 2)
    (ω : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hω : ∀ a b, ω a b = -ω b a)
    (s t : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    spinorFockPairing m (halfSpinBivector m i ω s).val t.val =
      -spinorFockPairing m s.val (halfSpinBivector m i ω t).val := by
  classical
  let Q := spinorFockPairing m
  let e (a : Fin (2 * m)) :=
    realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a)
  let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
  let E : ComplexSpinor m ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
    b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
  have hQ (u v : ComplexSpinor m) : Q u v = inner ℂ (E u) (E v) := by
    simp [Q, spinorFockPairing, E, b, PiLp.inner_apply, mul_comm]
  have hblock (a b : Fin (2 * m)) :
      Q (cliffordSymbol (e a) (cliffordSymbol (e b) s.val)) t.val =
        Q s.val (cliffordSymbol (e b) (cliffordSymbol (e a) t.val)) := by
    dsimp only [Q]
    rw [spinorFockPairing_cliffordSymbol, spinorFockPairing_cliffordSymbol, neg_neg]
  -- Taking the adjoint reverses the two Clifford factors; transpose then negates ω.
  have hleft : Q (halfSpinBivector m i ω s).val t.val =
      (1 / 4 : ℂ) * ∑ a : Fin (2 * m), ∑ b : Fin (2 * m),
        (ω a b : ℂ) * Q (cliffordSymbol (e a) (cliffordSymbol (e b) s.val)) t.val := by
    rw [halfSpinBivector_apply]
    simp only [hQ, map_smul, map_sum, inner_smul_left, sum_inner,
      map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Finset.mul_sum]
    rfl
  have hright : Q s.val (halfSpinBivector m i ω t).val =
      (1 / 4 : ℂ) * ∑ a : Fin (2 * m), ∑ b : Fin (2 * m),
        (ω a b : ℂ) * Q s.val (cliffordSymbol (e a) (cliffordSymbol (e b) t.val)) := by
    rw [halfSpinBivector_apply]
    simp only [hQ, map_smul, map_sum, inner_smul_right, inner_sum, Finset.mul_sum]
    rfl
  change Q (halfSpinBivector m i ω s).val t.val = -Q s.val (halfSpinBivector m i ω t).val
  rw [hleft, hright]
  simp_rw [hblock]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, 2, a, 2, b]
    rw [hω b a, Complex.ofReal_neg, neg_mul]
  simp only [Finset.sum_neg_distrib, mul_neg]

end AtiyahSinger
