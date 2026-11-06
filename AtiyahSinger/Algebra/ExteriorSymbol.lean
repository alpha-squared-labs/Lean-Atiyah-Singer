/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Exterior multiplication, contraction and the Bott symbol

Public module ID: M0022.

KL07 and the linear algebra part of D10/SC01. These are actual endomorphisms of
mathlib's exterior algebra, not unspecified operations satisfying Clifford relations.
The Hermitian inner product is conjugate-linear in its first variable. The norm sign
in the Clifford action is fixed by `cliffordSymbol = exteriorMultiplication - contraction`.
The algebraic identities below are proved without finite-dimensionality or completeness assumptions.
The even/odd bundle triple and its compactly supported K-class still require separate gluing.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Left exterior multiplication by a vector. -/
def exteriorMultiplication (v : V) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
  Algebra.lmul ℂ (ExteriorAlgebra ℂ V) (ExteriorAlgebra.ι ℂ v)

/-- Contraction by the linear functional w ↦ ⟪v,w⟫. -/
def contraction (v : V) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ V)) (innerₛₗ ℂ v)

/-- Clifford multiplication in the negative-square convention used by Spin Geometry. -/
def cliffordSymbol (v : V) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
  exteriorMultiplication v - contraction v

/-- KL07: exterior multiplication squares to zero. -/
theorem exteriorMultiplication_sq (v : V) : exteriorMultiplication v ^ 2 = 0 := by
  -- Evaluate on a multivector and bring the two copies of v together.
  ext x
  change ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ v * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- KL07: contraction squares to zero. -/
theorem contraction_sq (v : V) : contraction v ^ 2 = 0 := by
  -- Mathlib proves nilpotence for contraction by every linear functional.
  ext x
  exact CliffordAlgebra.contractLeft_contractLeft (innerₛₗ ℂ v) x

/-- KL07: the anticommutator is the Hermitian squared length. -/
theorem exteriorMultiplication_contraction_add (v : V) :
    exteriorMultiplication v * contraction v + contraction v * exteriorMultiplication v =
      (‖v‖ ^ 2 : ℂ) • (1 : Module.End ℂ (ExteriorAlgebra ℂ V)) := by
  -- Apply the contraction rule to v ∧ x; its second term cancels the first summand.
  ext x
  change ExteriorAlgebra.ι ℂ v * contraction v x +
      CliffordAlgebra.contractLeft (innerₛₗ ℂ v) (ExteriorAlgebra.ι ℂ v * x) =
    (‖v‖ ^ 2 : ℂ) • x
  rw [CliffordAlgebra.contractLeft_ι_mul]
  -- The remaining coefficient is the Hermitian squared norm.
  simp [contraction, inner_self_eq_norm_sq_to_K]

/-- KL07: wedge plus contraction has positive square. -/
theorem exteriorMultiplication_add_contraction_sq (v : V) :
    (exteriorMultiplication v + contraction v) ^ 2 =
      (‖v‖ ^ 2 : ℂ) • (1 : Module.End ℂ (ExteriorAlgebra ℂ V)) := by
  -- Expand in the noncommutative endomorphism ring and remove the two square terms.
  rw [pow_two, add_mul, mul_add, mul_add]
  rw [← pow_two, exteriorMultiplication_sq, ← pow_two, contraction_sq, zero_add, add_zero]
  exact exteriorMultiplication_contraction_add v

/-- D10/SC01: wedge minus contraction has negative square. -/
theorem cliffordSymbol_sq (v : V) :
    cliffordSymbol v ^ 2 = -(‖v‖ ^ 2 : ℂ) • (1 : Module.End ℂ (ExteriorAlgebra ℂ V)) := by
  -- The mixed terms have negative signs in the Clifford convention.
  rw [cliffordSymbol, pow_two, sub_mul, mul_sub, mul_sub]
  rw [← pow_two, exteriorMultiplication_sq, ← pow_two, contraction_sq, zero_sub, sub_zero]
  rw [sub_eq_add_neg, ← neg_add, exteriorMultiplication_contraction_add]
  exact (neg_smul (‖v‖ ^ 2 : ℂ) (1 : Module.End ℂ (ExteriorAlgebra ℂ V))).symm

/-- KL07: the phase-family square formula, for arbitrary phase parameter and vector. -/
theorem exteriorMultiplication_phase_contraction_sq (v : V) (z : ℂ) :
    (exteriorMultiplication v + z • contraction v) ^ 2 =
      (z * (‖v‖ ^ 2 : ℂ)) • (1 : Module.End ℂ (ExteriorAlgebra ℂ V)) := by
  -- Scalars commute with these linear endomorphisms, so both mixed terms carry z.
  rw [pow_two, add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, ← pow_two (exteriorMultiplication v),
    ← pow_two (contraction v), exteriorMultiplication_sq, contraction_sq, smul_zero,
    zero_add, add_zero]
  -- Combine the two mixed terms using the anticommutator identity.
  rw [← smul_add, exteriorMultiplication_contraction_add, smul_smul]

/-- D10/SC01: the inverse off the zero vector is exactly -c(v)/‖v‖². -/
theorem cliffordSymbol_inverse (v : V) (hv : v ≠ 0) :
    cliffordSymbol v * (-(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol v) = 1 := by
  -- The scalar denominator is nonzero precisely away from the zero vector.
  have hnorm : (‖v‖ ^ 2 : ℂ) ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))
  -- Substitute the negative-square identity and cancel its nonzero coefficient.
  rw [mul_smul_comm, ← pow_two, cliffordSymbol_sq, smul_smul]
  rw [neg_mul_neg, inv_mul_cancel₀ hnorm, one_smul]

end AtiyahSinger
