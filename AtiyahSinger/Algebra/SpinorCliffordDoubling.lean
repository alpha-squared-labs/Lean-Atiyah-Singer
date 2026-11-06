/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorDuality
public import Mathlib.LinearAlgebra.Contraction

/-!
# The self-tensor spinor model for the doubled Clifford symbol

Public module ID: M0065.

The invariant bilinear duality identifies two copies of the original spinor
module with its endomorphisms. Right multiplication by `1 + i γ` corrects
the second Clifford action to the graded right action. Thus the two factors
are the same original spinor symbol, rather than a symbol and its dual.
The parity comparison retains the shift by the half-dimension modulo two.

Source: the standard Clifford-module doubling argument, with the original
interleaved volume and negative-square convention of SG I.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

/-- The original normalized chirality is an involution on the actual spinor space. -/
theorem complexSpinorChirality_sq (m : ℕ) :
    complexSpinorChirality m * complexSpinorChirality m = 1 := by
  apply LinearMap.ext
  intro s
  rw [complexSpinorChirality_eq_involute]
  exact CliffordAlgebra.involute_involute s

/-- Chirality implements the original Clifford grading on the same spinor representation. -/
theorem complexSpinorChirality_representation (m : ℕ)
    (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s : ComplexSpinor m) :
    complexSpinorChirality m (complexSpinorRepresentation m a s) =
      complexSpinorRepresentation m (CliffordAlgebra.involute a)
        (complexSpinorChirality m s) := by
  -- Contraction and creation both anticommute with the actual exterior grading.
  have hc (l : Module.Dual ℂ (EuclideanSpace ℂ (Fin m))) (t : ComplexSpinor m) :
      CliffordAlgebra.involute (CliffordAlgebra.contractLeft l t) =
        -CliffordAlgebra.contractLeft l (CliffordAlgebra.involute t) := by
    induction t using CliffordAlgebra.left_induction with
    | algebraMap z => simp
    | add t u ht hu => simp only [map_add, ht, hu, neg_add]
    | ι_mul t v ht =>
      simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
        CliffordAlgebra.involute_ι, ht, neg_mul, map_neg]
      simp
  have hw (v : EuclideanSpace ℂ (Fin m)) (t : ComplexSpinor m) :
      complexSpinorChirality m (exteriorMultiplication v t) =
        -exteriorMultiplication v (complexSpinorChirality m t) := by
    rw [complexSpinorChirality_eq_involute]
    exact (map_mul CliffordAlgebra.involute _ _).trans (by
      rw [CliffordAlgebra.involute_ι, neg_mul]
      rfl)
  have hc' (v : EuclideanSpace ℂ (Fin m)) (t : ComplexSpinor m) :
      complexSpinorChirality m (contraction v t) =
        -contraction v (complexSpinorChirality m t) := by
    simpa only [complexSpinorChirality_eq_involute, contraction,
      AlgHom.toLinearMap_apply] using hc (innerₛₗ ℂ v) t
  have hg (v : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m))
      (t : ComplexSpinor m) :
      complexSpinorChirality m (complexSpinorGenerator m v t) =
        -complexSpinorGenerator m v (complexSpinorChirality m t) := by
    simp only [complexSpinorGenerator, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
      map_sum, map_add, map_smul, map_sub, hw, hc']
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    module
  -- Extend the generator relation in the actual Clifford algebra, including complex scalars.
  induction a using CliffordAlgebra.induction generalizing s with
  | algebraMap z => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι v =>
    simpa only [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply,
      CliffordAlgebra.involute_ι, map_neg, LinearMap.neg_apply] using hg v s
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]

/-- The corrected self-tensor equivalence, using a supplied bilinear spinor duality. -/
def complexSpinorDoublingEndEquiv (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m)) :
    ComplexSpinor m ⊗[ℂ] ComplexSpinor m ≃ₗ[ℂ] Module.End ℂ (ComplexSpinor m) := by
  let γ := complexSpinorChirality m
  have hγ : γ * γ = 1 := complexSpinorChirality_sq m
  let A : (Module.End ℂ (ComplexSpinor m))ˣ :=
    { val := 1 + Complex.I • γ
      inv := (2 : ℂ)⁻¹ • (1 - Complex.I • γ)
      val_inv := by
        simp only [mul_smul_comm, add_mul, mul_sub, one_mul, mul_one,
          smul_mul_assoc, hγ]
        match_scalars <;> norm_num [Complex.I_sq]
      inv_val := by
        simp only [smul_mul_assoc, sub_mul, mul_add, one_mul, mul_one,
          mul_smul_comm, smul_smul, hγ]
        match_scalars <;> ring_nf
        norm_num [Complex.I_sq] }
  let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
  exact (TensorProduct.comm ℂ _ _).trans
    ((TensorProduct.congr e (LinearEquiv.refl ℂ _)).trans
      ((dualTensorHomEquivOfBasis b).trans (A.mulRightLinearEquiv ℂ)))

/-- The corrected map acts by the same bilinear pairing and the explicit chirality phase. -/
theorem complexSpinorDoublingEndEquiv_tmul_apply (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (s t x : ComplexSpinor m) :
    complexSpinorDoublingEndEquiv m e (s ⊗ₜ[ℂ] t) x =
      e t (x + Complex.I • complexSpinorChirality m x) • s := by
  rfl

/-- The self-tensor graded sum becomes left Clifford action plus graded right Clifford action. -/
theorem complexSpinorDoublingEndEquiv_symbol (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (v w : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    complexSpinorDoublingEndEquiv m e
        ((TensorProduct.map (complexSpinorGenerator m v)
            (LinearMap.id : Module.End ℂ (ComplexSpinor m)) +
          TensorProduct.map (complexSpinorChirality m) (complexSpinorGenerator m w)) z) =
      complexSpinorGenerator m v * complexSpinorDoublingEndEquiv m e z +
        Complex.I • (complexSpinorChirality m * complexSpinorDoublingEndEquiv m e z *
          complexSpinorChirality m * complexSpinorGenerator m w) := by
  have hpair (t x : ComplexSpinor m) :
      e (complexSpinorGenerator m w t) x = -e t (complexSpinorGenerator m w x) := by
    simpa only [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply,
      CliffordAlgebra.star_ι, map_neg, LinearMap.neg_apply] using
      he (CliffordAlgebra.ι (complexSpinorQuadraticForm m) w) t x
  have hodd (x : ComplexSpinor m) :
      complexSpinorChirality m (complexSpinorGenerator m w x) =
        -complexSpinorGenerator m w (complexSpinorChirality m x) := by
    simpa only [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply,
      CliffordAlgebra.involute_ι, map_neg, LinearMap.neg_apply] using
      complexSpinorChirality_representation m
        (CliffordAlgebra.ι (complexSpinorQuadraticForm m) w) x
  have hinv (x : ComplexSpinor m) :
      complexSpinorChirality m (complexSpinorChirality m x) = x :=
    LinearMap.congr_fun (complexSpinorChirality_sq m) x
  -- Check actual pure tensors; linearity then covers their finite sums.
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', mul_add, add_mul, smul_add]; abel
  | tmul s t =>
    apply LinearMap.ext
    intro x
    simp only [LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      map_add, LinearMap.add_apply, complexSpinorDoublingEndEquiv_tmul_apply,
      Module.End.mul_apply, LinearMap.smul_apply, map_smul, hpair, hodd, map_neg,
      hinv]
    match_scalars <;> ring_nf
    norm_num [Complex.I_sq]

/-- The same map transports tensor chirality with the original half-dimensional parity shift. -/
theorem complexSpinorDoublingEndEquiv_chirality (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    complexSpinorDoublingEndEquiv m e
        (TensorProduct.map (complexSpinorChirality m) (complexSpinorChirality m) z) =
      (-1 : ℂ) ^ m • (complexSpinorChirality m * complexSpinorDoublingEndEquiv m e z *
        complexSpinorChirality m) := by
  -- Conjugation of the original volume gives exactly (-1)^m, including odd m.
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', mul_add, add_mul, smul_add]
  | tmul s t =>
    apply LinearMap.ext
    intro x
    simp only [TensorProduct.map_tmul, complexSpinorDoublingEndEquiv_tmul_apply,
      complexSpinor_invariantDuality_chirality m e he, Module.End.mul_apply,
      LinearMap.smul_apply, map_smul, map_add]
    module

/-- The corrected self-tensor map is equivariant for the same native Spin action. -/
theorem complexSpinorDoublingEndEquiv_spin (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (g : spinGroup (realSpinorQuadraticForm m))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    complexSpinorDoublingEndEquiv m e
        (TensorProduct.map (complexSpinRepresentation m g).toLinearMap
          (complexSpinRepresentation m g).toLinearMap z) =
      (complexSpinRepresentation m g).toLinearMap * complexSpinorDoublingEndEquiv m e z *
        (complexSpinRepresentation m g).symm.toLinearMap := by
  -- Restriction through the original real embedding preserves the same Clifford grading.
  have hreal (a : CliffordAlgebra (realSpinorQuadraticForm m)) (s : ComplexSpinor m) :
      complexSpinorChirality m (realSpinorRepresentation m a s) =
        realSpinorRepresentation m (CliffordAlgebra.involute a) (complexSpinorChirality m s) := by
    induction a using CliffordAlgebra.induction generalizing s with
    | algebraMap r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply,
        LinearMap.map_smul_of_tower]
      rfl
    | ι v =>
      have h := complexSpinorChirality_representation m
        (CliffordAlgebra.ι _ (complexSpinorRealEmbedding m v)) s
      simpa only [realSpinorRepresentation, complexSpinorRepresentation,
        CliffordAlgebra.lift_ι_apply, CliffordAlgebra.involute_ι, map_neg,
        LinearMap.neg_apply, realSpinorGenerator, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply] using h
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  have hcomm (s : ComplexSpinor m) :
      complexSpinorChirality m (complexSpinRepresentation m g s) =
        complexSpinRepresentation m g (complexSpinorChirality m s) := by
    change complexSpinorChirality m (realSpinorRepresentation m g.val s) = _
    rw [hreal, CliffordAlgebra.involute_eq_of_mem_even (spinGroup.mem_even g.property)]
    rfl
  -- Invariance uses g in both tensor factors; the End action is conjugation by that same g.
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', mul_add, add_mul]
  | tmul s t =>
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (complexSpinRepresentation m g).surjective x
    simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      complexSpinorDoublingEndEquiv_tmul_apply, Module.End.mul_apply,
      LinearEquiv.symm_apply_apply, hcomm]
    have hphase : complexSpinRepresentation m g y +
        Complex.I • complexSpinRepresentation m g (complexSpinorChirality m y) =
        complexSpinRepresentation m g (y + Complex.I • complexSpinorChirality m y) := by
      simp only [map_add, map_smul]
    rw [hphase, complexSpinor_invariantDuality_spin m e he, map_smul]

end AtiyahSinger
