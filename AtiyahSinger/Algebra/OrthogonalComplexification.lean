/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LowSphereHodgeIndex
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic

/-!
# Complexification of the standard real orthogonal representation

Public module ID: M0045.

AL01 uses the complexification of the real standard representation. Its carrier
here is the native Euclidean space `EuclideanSpace ℂ (Fin r)`, with the real
matrix entries included in ℂ. These are the canonical coordinates of
`ℂ ⊗[ℝ] (Fin r → ℝ)`: a pure tensor z ⊗ w has coordinates z * w i.
In particular, the real two-plane has complex dimension two, rather than one.

Conjugation acts on each coordinate, hence fixes the real subspace and reverses
its imaginary copy. It is a proper real-linear base map; complex linearity of
the base map is neither asserted nor needed for equivariant K-theory pullback.
The special orthogonal action is the literal restriction of the same real
matrix action along the existing native SO(r) inclusion.

Source: Atiyah--Singer I, Lemma (2.8), p.496. The matrix coordinate adapters and
construction certificates are project-supplied implementations of these standard
objects. The proofs below retain those original matrices and Euclidean structures.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option maxSynthPendingDepth 25

/-- The real matrix action extended complex-linearly on the native Euclidean carrier. -/
def orthogonalComplexificationRepresentation (r : ℕ) :
    Matrix.orthogonalGroup (Fin r) ℝ →*
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) where
  toFun A := Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (A.val.map Complex.ofReal)
  map_one' := by
    change Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)
      (Complex.ofRealHom.mapMatrix (1 : Matrix _ _ ℝ)) = 1
    rw [map_one, map_one]
  map_mul' A B := by
    change Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)
      (Complex.ofRealHom.mapMatrix (A.val * B.val)) =
      Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix A.val) *
        Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (Complex.ofRealHom.mapMatrix B.val)
    rw [map_mul, map_mul]

/-- The specified matrix action, without changing the Euclidean norm or topology. -/
instance orthogonalComplexificationDistribMulAction (r : ℕ) :
    DistribMulAction (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℂ (Fin r)) where
  smul A z := orthogonalComplexificationRepresentation r A z
  one_smul z := by
    change orthogonalComplexificationRepresentation r 1 z = z
    rw [map_one]
    rfl
  mul_smul A B z := by
    change orthogonalComplexificationRepresentation r (A * B) z =
      orthogonalComplexificationRepresentation r A
        (orthogonalComplexificationRepresentation r B z)
    rw [map_mul]
    rfl
  smul_zero A := map_zero (orthogonalComplexificationRepresentation r A)
  smul_add A z w := map_add (orthogonalComplexificationRepresentation r A) z w

/-- The complexified real action commutes with the original complex scalars. -/
instance orthogonalComplexification_smulCommClass (r : ℕ) :
    SMulCommClass (Matrix.orthogonalGroup (Fin r) ℝ) ℂ (EuclideanSpace ℂ (Fin r)) where
  smul_comm A c z := (orthogonalComplexificationRepresentation r A).map_smul c z

/-- Joint continuity uses the native matrix and Euclidean topologies. -/
instance orthogonalComplexification_continuousSMul (r : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℂ (Fin r)) where
  continuous_smul := by
    have hval : Continuous (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦
        (A.val : Matrix (Fin r) (Fin r) ℝ)) := continuous_subtype_val
    have hf : Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ ×
        EuclideanSpace ℂ (Fin r) ↦ p.1.val) := hval.comp continuous_fst
    have hm : Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ ×
        EuclideanSpace ℂ (Fin r) ↦ p.1.val.map Complex.ofReal) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact Complex.continuous_ofReal.comp
        ((continuous_apply j).comp ((continuous_apply i).comp
          hf))
    have hp : Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ ×
        EuclideanSpace ℂ (Fin r) ↦ (p.1.val.map Complex.ofReal, p.2)) :=
      hm.prodMk continuous_snd
    have h := (Matrix.continuous_uncurry_toEuclideanCLM (n := Fin r) (𝕜 := ℂ)).comp
      (X := Matrix.orthogonalGroup (Fin r) ℝ × EuclideanSpace ℂ (Fin r)) hp
    exact h

/-- Complexification of a real orthogonal matrix preserves the Hermitian inner product. -/
theorem orthogonalComplexification_unitary (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (u v : EuclideanSpace ℂ (Fin r)) :
    inner ℂ (A • u) (A • v) = inner ℂ u v := by
  /- Real matrix coefficients turn transpose(A) A = 1 into the complex
  unitary identity. Transport that identity through the matrix-to-operator
  map, then apply preservation of the Hermitian inner product by a
  unitary operator on the same Euclidean space. -/
  -- Real entrywise inclusion carries the original orthogonality identity to unitarity.
  let B : Matrix (Fin r) (Fin r) ℂ := A.val.map Complex.ofReal
  have hstar : star B = A.val.transpose.map Complex.ofReal := by
    ext i j
    simp [B, Matrix.star_apply]
  have hB : B ∈ Matrix.unitaryGroup (Fin r) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [hstar]
    change Complex.ofRealHom.mapMatrix A.val.transpose *
      Complex.ofRealHom.mapMatrix A.val = 1
    rw [← map_mul, (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).mp A.property, map_one]
  -- The original matrix-to-operator equivalence preserves the adjoint and the inner product.
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary
    (Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)) hB) u v

/-- Coordinatewise conjugation on the actual complexification. -/
def orthogonalComplexificationConjugation (r : ℕ) :
    C(EuclideanSpace ℂ (Fin r), EuclideanSpace ℂ (Fin r)) where
  toFun z := WithLp.toLp 2 (fun i ↦ star (z i))
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
    (continuous_pi (fun i ↦ (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i).star))

/-- Real matrix coefficients make the actual conjugation equivariant. -/
theorem orthogonalComplexificationConjugation_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)) :
    orthogonalComplexificationConjugation r (A • z) =
      A • orthogonalComplexificationConjugation r z := by
  /- In each coordinate, conjugate the finite sum of real coefficients times
  the vector entries. Conjugation fixes every real coefficient and distributes
  over that sum. This identifies the two actual vectors coordinate by coordinate. -/
  -- Conjugation fixes every real matrix entry in the original finite coordinate sum.
  ext i
  change star (∑ j, (A.val i j : ℂ) * z j) =
    ∑ j, (A.val i j : ℂ) * star (z j)
  simp

/-- The involutive Euclidean isometry is proper, including in dimension zero. -/
theorem orthogonalComplexificationConjugation_isProperMap (r : ℕ) :
    IsProperMap (orthogonalComplexificationConjugation r) := by
  /- Coordinatewise conjugation is continuous and is its own inverse. Package
  that same map as a homeomorphism; its inverse sends compact sets to compact
  sets, so the original continuous map is proper. No compactness of the base
  or positive dimension assumption is needed. -/
  -- The specified map is its own inverse, on the same Euclidean coordinates.
  have hinv : Function.Involutive (orthogonalComplexificationConjugation r) := by
    intro z
    ext i
    exact star_star (z i)
  let e : EuclideanSpace ℂ (Fin r) ≃ₜ EuclideanSpace ℂ (Fin r) :=
    { toEquiv := ⟨orthogonalComplexificationConjugation r,
        orthogonalComplexificationConjugation r, hinv, hinv⟩
      continuous_toFun := (orthogonalComplexificationConjugation r).continuous
      continuous_invFun := (orthogonalComplexificationConjugation r).continuous }
  -- Properness applies to that same map, including the zero-dimensional carrier.
  exact e.isProperMap

/-- The SO(r) complexified action is the original action precomposed by inclusion. -/
instance specialOrthogonalComplexificationDistribMulAction (r : ℕ) :
    DistribMulAction (Matrix.specialOrthogonalGroup (Fin r) ℝ)
      (EuclideanSpace ℂ (Fin r)) :=
  DistribMulAction.compHom _ (specialOrthogonalGroupInclusion r).toMonoidHom

/-- Complex scalar commutation for the same restricted action. -/
instance specialOrthogonalComplexification_smulCommClass (r : ℕ) :
    SMulCommClass (Matrix.specialOrthogonalGroup (Fin r) ℝ) ℂ
      (EuclideanSpace ℂ (Fin r)) where
  smul_comm A c z := smul_comm (specialOrthogonalGroupInclusion r A) c z

/-- Joint continuity for the same restricted action. -/
instance specialOrthogonalComplexification_continuousSMul (r : ℕ) :
    ContinuousSMul (Matrix.specialOrthogonalGroup (Fin r) ℝ)
      (EuclideanSpace ℂ (Fin r)) :=
  MulAction.continuousSMul_compHom (specialOrthogonalGroupInclusion r).continuous

end AtiyahSinger
