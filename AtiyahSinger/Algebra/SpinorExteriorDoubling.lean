/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CliffordExteriorDoubling
public import AtiyahSinger.Algebra.SpinorCliffordDoubling
public import AtiyahSinger.Algebra.SpinorComplexification

/-!
# Self-tensor spinors and the actual exterior comparison

Public module ID: M0069.

Compose the corrected self-tensor map with the inverse of the original
complex Clifford representation and mathlib's existing form-change map.
The resulting exterior space is on the complex real/imaginary coordinate
space of that original Clifford algebra. Both the doubled symbol and its
parity are computed for this very composite, before transporting these
coordinates to the native scalar-extension bundle.

Source: SG I.5, Chevalley's exterior Clifford module and spinor doubling.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

/-- The actual self-tensor spinors identified with the exterior algebra of Clifford coordinates. -/
def complexSpinorDoublingExteriorEquiv (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m)) :
    ComplexSpinor m ⊗[ℂ] ComplexSpinor m ≃ₗ[ℂ]
      ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  (complexSpinorDoublingEndEquiv m e).trans
    ((complexSpinorEquiv m).symm.toLinearEquiv.trans
      (CliffordAlgebra.equivExterior (complexSpinorQuadraticForm m)))

/-- The composed exterior comparison retains the original self-tensor parity shift. -/
theorem complexSpinorDoublingExteriorEquiv_chirality (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    complexSpinorDoublingExteriorEquiv m e
        (TensorProduct.map (complexSpinorChirality m) (complexSpinorChirality m) z) =
      (-1 : ℂ) ^ m • CliffordAlgebra.involute (complexSpinorDoublingExteriorEquiv m e z) := by
  let a := (complexSpinorEquiv m).symm (complexSpinorDoublingEndEquiv m e z)
  have ha : complexSpinorRepresentation m a = complexSpinorDoublingEndEquiv m e z :=
    (complexSpinorEquiv m).apply_symm_apply _
  have hgrade : complexSpinorChirality m * complexSpinorDoublingEndEquiv m e z *
      complexSpinorChirality m = complexSpinorRepresentation m (CliffordAlgebra.involute a) := by
    rw [← ha]
    apply LinearMap.ext
    intro s
    change complexSpinorChirality m
      (complexSpinorRepresentation m a (complexSpinorChirality m s)) = _
    rw [complexSpinorChirality_representation,
      show complexSpinorChirality m (complexSpinorChirality m s) = s from
        LinearMap.congr_fun (complexSpinorChirality_sq m) s]
  change CliffordAlgebra.equivExterior (complexSpinorQuadraticForm m)
    ((complexSpinorEquiv m).symm (complexSpinorDoublingEndEquiv m e
      (TensorProduct.map (complexSpinorChirality m) (complexSpinorChirality m) z))) = _
  rw [complexSpinorDoublingEndEquiv_chirality m e he, hgrade, map_smul, map_smul]
  change (-1 : ℂ) ^ m • CliffordAlgebra.equivExterior (complexSpinorQuadraticForm m)
    ((complexSpinorEquiv m).symm ((complexSpinorEquiv m) (CliffordAlgebra.involute a))) = _
  rw [AlgEquiv.symm_apply_apply, CliffordAlgebra.equivExterior_involute]
  rfl

/-- The doubled symbol creates by v+iw and contracts by the associated form at v minus i times w. -/
theorem complexSpinorDoublingExteriorEquiv_symbol (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (v w : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    complexSpinorDoublingExteriorEquiv m e
        ((TensorProduct.map (complexSpinorGenerator m v)
            (LinearMap.id : Module.End ℂ (ComplexSpinor m)) +
          TensorProduct.map (complexSpinorChirality m) (complexSpinorGenerator m w)) z) =
      ExteriorAlgebra.ι ℂ (v + Complex.I • w) * complexSpinorDoublingExteriorEquiv m e z -
        CliffordAlgebra.contractLeft
          (QuadraticMap.associated (-(complexSpinorQuadraticForm m)) v -
            Complex.I • QuadraticMap.associated (-(complexSpinorQuadraticForm m)) w)
          (complexSpinorDoublingExteriorEquiv m e z) := by
  let Q := complexSpinorQuadraticForm m
  let B := QuadraticMap.associated (-Q)
  let a := (complexSpinorEquiv m).symm (complexSpinorDoublingEndEquiv m e z)
  have ha : complexSpinorRepresentation m a = complexSpinorDoublingEndEquiv m e z :=
    (complexSpinorEquiv m).apply_symm_apply _
  have hgen (u : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
      complexSpinorRepresentation m (CliffordAlgebra.ι Q u) = complexSpinorGenerator m u :=
    CliffordAlgebra.lift_ι_apply _ _ _
  have hgrade : complexSpinorChirality m * complexSpinorDoublingEndEquiv m e z *
      complexSpinorChirality m = complexSpinorRepresentation m (CliffordAlgebra.involute a) := by
    rw [← ha]
    apply LinearMap.ext
    intro s
    change complexSpinorChirality m
      (complexSpinorRepresentation m a (complexSpinorChirality m s)) = _
    rw [complexSpinorChirality_representation,
      show complexSpinorChirality m (complexSpinorChirality m s) = s from
        LinearMap.congr_fun (complexSpinorChirality_sq m) s]
  -- The corrected second action is the actual graded right multiplication in the Clifford algebra.
  have hsymbol : complexSpinorDoublingEndEquiv m e
      ((TensorProduct.map (complexSpinorGenerator m v)
          (LinearMap.id : Module.End ℂ (ComplexSpinor m)) +
        TensorProduct.map (complexSpinorChirality m) (complexSpinorGenerator m w)) z) =
      complexSpinorRepresentation m
        (CliffordAlgebra.ι Q v * a +
          Complex.I • (CliffordAlgebra.involute a * CliffordAlgebra.ι Q w)) := by
    rw [complexSpinorDoublingEndEquiv_symbol m e he, hgrade, ← ha]
    simp only [map_add, map_smul, map_mul, hgen]
  change CliffordAlgebra.equivExterior Q ((complexSpinorEquiv m).symm
    (complexSpinorDoublingEndEquiv m e _)) = _
  rw [hsymbol]
  change CliffordAlgebra.equivExterior Q ((complexSpinorEquiv m).symm
    ((complexSpinorEquiv m)
      (CliffordAlgebra.ι Q v * a +
        Complex.I • (CliffordAlgebra.involute a * CliffordAlgebra.ι Q w)))) = _
  rw [AlgEquiv.symm_apply_apply, map_add, map_smul, CliffordAlgebra.equivExterior_involute_mul_ι]
  -- The form-change recurrence gives opposite contraction signs on the two coordinate copies.
  change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
      (CliffordAlgebra.ι Q v * a) + Complex.I •
        (ExteriorAlgebra.ι ℂ w * CliffordAlgebra.equivExterior Q a +
          CliffordAlgebra.contractLeft (B w) (CliffordAlgebra.equivExterior Q a)) = _
  rw [CliffordAlgebra.changeForm_ι_mul]
  change ExteriorAlgebra.ι ℂ v * CliffordAlgebra.equivExterior Q a -
      CliffordAlgebra.contractLeft (B v) (CliffordAlgebra.equivExterior Q a) + Complex.I •
        (ExteriorAlgebra.ι ℂ w * CliffordAlgebra.equivExterior Q a +
          CliffordAlgebra.contractLeft (B w) (CliffordAlgebra.equivExterior Q a)) =
    ExteriorAlgebra.ι ℂ (v + Complex.I • w) * CliffordAlgebra.equivExterior Q a -
      CliffordAlgebra.contractLeft (B v - Complex.I • B w) (CliffordAlgebra.equivExterior Q a)
  simp only [map_add, map_smul, map_sub, LinearMap.sub_apply, LinearMap.smul_apply,
    add_mul, smul_mul_assoc]
  module

/-- The same exterior comparison is equivariant for the original Spin action in both factors. -/
theorem complexSpinorDoublingExteriorEquiv_spin (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (g : spinGroup (realSpinorQuadraticForm m))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    complexSpinorDoublingExteriorEquiv m e
        (TensorProduct.map (complexSpinRepresentation m g).toLinearMap
          (complexSpinRepresentation m g).toLinearMap z) =
      ExteriorAlgebra.map (complexSpinVectorComplexification m g).toLinearMap
        (complexSpinorDoublingExteriorEquiv m e z) := by
  let f := complexSpinVectorComplexificationIsometry m g
  let c := (complexSpinRepresentation m g).conjAlgEquiv ℂ
  have hrep (a : CliffordAlgebra (complexSpinorQuadraticForm m)) :
      complexSpinorRepresentation m (CliffordAlgebra.map f a) =
        c (complexSpinorRepresentation m a) := by
    induction a using CliffordAlgebra.induction with
    | algebraMap r => simp only [AlgHom.commutes, AlgEquiv.commutes]
    | ι v =>
      rw [CliffordAlgebra.map_apply_ι]
      change complexSpinorRepresentation m
        (CliffordAlgebra.ι _ (complexSpinVectorComplexification m g v)) = _
      simpa only [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply, c] using
        complexSpinVectorComplexification_generator m g v
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul a b ha hb => simp only [map_mul, ha, hb]
  let a := (complexSpinorEquiv m).symm (complexSpinorDoublingEndEquiv m e z)
  have ha : complexSpinorRepresentation m a = complexSpinorDoublingEndEquiv m e z :=
    (complexSpinorEquiv m).apply_symm_apply _
  have hconj : (complexSpinRepresentation m g).toLinearMap *
      complexSpinorDoublingEndEquiv m e z * (complexSpinRepresentation m g).symm.toLinearMap =
        complexSpinorRepresentation m (CliffordAlgebra.map f a) := by
    rw [hrep, ha]
    rfl
  -- Conjugation by the original Spin action agrees on every Clifford generator, hence everywhere.
  change CliffordAlgebra.equivExterior (complexSpinorQuadraticForm m)
    ((complexSpinorEquiv m).symm (complexSpinorDoublingEndEquiv m e _)) = _
  rw [complexSpinorDoublingEndEquiv_spin m e he, hconj]
  change CliffordAlgebra.equivExterior (complexSpinorQuadraticForm m)
    ((complexSpinorEquiv m).symm ((complexSpinorEquiv m) (CliffordAlgebra.map f a))) = _
  rw [AlgEquiv.symm_apply_apply, CliffordAlgebra.equivExterior_map]
  rfl

end AtiyahSinger
