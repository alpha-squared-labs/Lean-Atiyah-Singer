/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorExteriorDoubling
public import AtiyahSinger.Topology.ComplexificationHermitianMetric

/-!
# The doubled spin symbol on the native complexification

Public module ID: M1448.

The self-tensor intertwiner carries the actual two real Clifford
actions to the exterior symbol at `1 tensor v + i tensor w`. The contraction
uses the canonical extension of the original real metric. Thus the result
identifies the actual exterior Thom symbol, including its Hermitian sign,
before it is transported through the supplied spin frames.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct ComplexConjugate

set_option maxHeartbeats 600000 in
-- Retain the native scalar-extension structures while comparing both contraction recurrences.
/-- The native complexification comparison intertwines the entire original doubled symbol. -/
theorem complexSpinorDoublingExteriorEquiv_complexification_symbol (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (v w : EuclideanSpace ℂ (Fin m)) (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    letI := (complexificationHermitianCore (EuclideanSpace ℂ (Fin m))).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore
      (complexificationHermitianCore (EuclideanSpace ℂ (Fin m))).toCore
    ExteriorAlgebra.map (complexSpinorComplexificationEquiv m).symm.toLinearMap
        (complexSpinorDoublingExteriorEquiv m e
          ((TensorProduct.map (cliffordSymbol v) (LinearMap.id : Module.End ℂ (ComplexSpinor m)) +
            TensorProduct.map (complexSpinorChirality m) (cliffordSymbol w)) z)) =
      cliffordSymbol ((1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w)
        (ExteriorAlgebra.map (complexSpinorComplexificationEquiv m).symm.toLinearMap
          (complexSpinorDoublingExteriorEquiv m e z)) := by
  let V := EuclideanSpace ℂ (Fin m)
  let U := V × V
  let C := complexSpinorComplexificationEquiv m
  let r := complexSpinorRealEmbedding m
  let Q := complexSpinorQuadraticForm m
  let B := QuadraticMap.associated (-Q)
  let Φ := complexSpinorDoublingExteriorEquiv m e
  let L := ExteriorAlgebra.map C.symm.toLinearMap
  let core := complexificationHermitianCore V
  let := core.toNormedAddCommGroup
  let := InnerProductSpace.ofCore core.toCore
  let ξ : ℂ ⊗[ℝ] V := (1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w
  -- Polarization identifies the real restriction of the original complex bilinear form.
  have hB (u t : V) : B (r u) (r t) = (inner ℝ u t : ℂ) := by
    have hQ (a : V) : Q (r a) = -(‖a‖ ^ 2 : ℂ) := complexSpinorQuadraticForm_real m a
    change QuadraticMap.associatedHom ℂ (-Q) (r u) (r t) = _
    rw [QuadraticMap.associated_apply]
    simp only [neg_apply, ← map_add r, hQ,
      neg_neg, Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul,
      smul_eq_mul, invOf_eq_inv]
    have hnorm : (‖u + t‖ : ℂ) ^ 2 =
        (‖u‖ : ℂ) ^ 2 + 2 * (inner ℝ u t : ℂ) + (‖t‖ : ℂ) ^ 2 := by
      exact_mod_cast norm_add_sq_real u t
    rw [hnorm]
    ring
  -- The contraction functional is the same Hermitian pairing on the native scalar extension.
  have hpair (u : U) :
      inner ℂ ξ (C.symm u) = (B (r v) - Complex.I • B (r w)) u := by
    obtain ⟨a, rfl⟩ := C.surjective u
    rw [LinearEquiv.symm_apply_apply]
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | tmul a t =>
      change inner ℂ ((1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w) (a ⊗ₜ[ℝ] t) = _
      rw [inner_add_left, complexSpinorComplexificationEquiv_tmul]
      change core.inner ((1 : ℂ) ⊗ₜ[ℝ] v) (a ⊗ₜ[ℝ] t) +
        core.inner (Complex.I ⊗ₜ[ℝ] w) (a ⊗ₜ[ℝ] t) = _
      rw [complexificationHermitianCore_tmul, complexificationHermitianCore_tmul]
      simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, map_one, Complex.conj_I]
      change 1 * a * (inner ℝ v t : ℂ) + -Complex.I * a * (inner ℝ w t : ℂ) =
        a * (B (r v) (r t) - Complex.I * B (r w) (r t))
      rw [hB, hB]
      ring
  -- Exterior functoriality transports contraction by this actual functional, degree by degree.
  have hcontract (a : ExteriorAlgebra ℂ U) :
      L (CliffordAlgebra.contractLeft (B (r v) - Complex.I • B (r w)) a) =
        CliffordAlgebra.contractLeft (innerₛₗ ℂ ξ) (L a) := by
    induction a using CliffordAlgebra.left_induction with
    | algebraMap a => simp [L]
    | add a b ha hb => simp only [map_add, ha, hb]
    | ι_mul a u ha =>
      rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul]
      change (B (r v) - Complex.I • B (r w)) u • L a -
        L (ExteriorAlgebra.ι ℂ u) * L (CliffordAlgebra.contractLeft _ a) =
          CliffordAlgebra.contractLeft (innerₛₗ ℂ ξ) (L (ExteriorAlgebra.ι ℂ u * a))
      rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul, ha]
      change _ = inner ℂ ξ (C.symm u) • L a -
        ExteriorAlgebra.ι ℂ (C.symm u) * CliffordAlgebra.contractLeft (innerₛₗ ℂ ξ) (L a)
      rw [hpair]
      rfl
  have hreal (u : V) : complexSpinorGenerator m (r u) = cliffordSymbol u := by
    have h := complexSpinorRepresentation_real m u
    rwa [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply] at h
  have hvector : C.symm (r v + Complex.I • r w) = ξ := by
    apply C.injective
    rw [LinearEquiv.apply_symm_apply, map_add, complexSpinorComplexificationEquiv_tmul,
      complexSpinorComplexificationEquiv_tmul, one_smul]
  -- Apply the self-tensor calculation, retaining its creation-minus-contraction convention.
  have h := complexSpinorDoublingExteriorEquiv_symbol m e he (r v) (r w) z
  rw [hreal, hreal] at h
  change L (Φ _) = _
  rw [h, map_sub, map_mul, ExteriorAlgebra.map_apply_ι]
  change ExteriorAlgebra.ι ℂ (C.symm (r v + Complex.I • r w)) * L (Φ z) -
    L (CliffordAlgebra.contractLeft (B (r v) - Complex.I • B (r w)) (Φ z)) = _
  rw [hvector, hcontract]
  rfl

end AtiyahSinger
