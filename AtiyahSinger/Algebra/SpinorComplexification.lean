/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.Complexification
public import AtiyahSinger.Algebra.RealSpinor
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# The original Clifford coordinates as a native complexification

Public module ID: M0066.

Extend the original real/imaginary vector embedding by complex scalars.
Recovering real and imaginary parts in each coordinate gives explicit
preimages; equality of dimensions gives injectivity. The resulting
equivalence identifies the actual scalar extension with the
coordinate space of the original complex Clifford algebra. No unrelated
vector space with the same dimension is substituted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

/-- The complex extension of the original real Clifford-coordinate embedding is bijective. -/
theorem complexSpinorRealEmbedding_liftBaseChange_bijective (m : ℕ) :
    Function.Bijective ((complexSpinorRealEmbedding m).liftBaseChange ℂ) := by
  let V := EuclideanSpace ℂ (Fin m)
  let U := V × V
  let L : (ℂ ⊗[ℝ] V) →ₗ[ℂ] U := (complexSpinorRealEmbedding m).liftBaseChange ℂ
  -- Every coordinate pair is the sum of a real embedded vector and i times another one.
  have hsurj : Function.Surjective L := by
    intro x
    let v : V := WithLp.toLp 2 (fun j ↦ (x.1 j).re + Complex.I * (x.2 j).re)
    let w : V := WithLp.toLp 2 (fun j ↦ (x.1 j).im + Complex.I * (x.2 j).im)
    refine ⟨(1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w, ?_⟩
    simp only [L, map_add, LinearMap.liftBaseChange_tmul, one_smul]
    apply Prod.ext
    · ext j
      change ((v j).re : ℂ) + Complex.I * (w j).re = x.1 j
      simp only [v, w, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, sub_zero, mul_zero, add_zero]
      simpa only [mul_comm] using Complex.re_add_im (x.1 j)
    · ext j
      change ((v j).im : ℂ) + Complex.I * (w j).im = x.2 j
      simp only [v, w, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        one_mul, mul_zero, zero_add]
      simpa only [mul_comm] using Complex.re_add_im (x.2 j)
  -- Equal finite dimensions make this very scalar-extension map injective as well.
  let : FiniteDimensional ℝ (ℂ ⊗[ℝ] V) :=
    Module.Finite.equiv (complexificationReIm V).symm
  let : FiniteDimensional ℂ (ℂ ⊗[ℝ] V) := Module.Finite.of_restrictScalars_finite ℝ ℂ _
  have hdim : Module.finrank ℂ (ℂ ⊗[ℝ] V) = Module.finrank ℂ U := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℝ ℂ V]
    simp [V, U, Module.finrank_prod, Complex.finrank_real_complex, two_mul]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- The native scalar extension in the actual complex Clifford coordinates. -/
def complexSpinorComplexificationEquiv (m : ℕ) :
    (ℂ ⊗[ℝ] EuclideanSpace ℂ (Fin m)) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  LinearEquiv.ofBijective ((complexSpinorRealEmbedding m).liftBaseChange ℂ)
    (complexSpinorRealEmbedding_liftBaseChange_bijective m)

/-- The coordinate equivalence retains the specified vector on every original pure tensor. -/
theorem complexSpinorComplexificationEquiv_tmul (m : ℕ) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    complexSpinorComplexificationEquiv m (z ⊗ₜ[ℝ] v) = z • complexSpinorRealEmbedding m v :=
  rfl

/-- The native real Spin vector action extended to the original complex Clifford coordinates. -/
def complexSpinVectorComplexification (m : ℕ)
    (g : spinGroup (realSpinorQuadraticForm m)) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  (complexSpinorComplexificationEquiv m).symm.trans
    (((realSpinVectorRepresentation m g).baseChange ℝ ℂ).trans
      (complexSpinorComplexificationEquiv m))

/-- Complexification retains the original Spin vector action on the original real embedding. -/
theorem complexSpinVectorComplexification_realEmbedding (m : ℕ)
    (g : spinGroup (realSpinorQuadraticForm m)) (v : EuclideanSpace ℂ (Fin m)) :
    complexSpinVectorComplexification m g (complexSpinorRealEmbedding m v) =
      complexSpinorRealEmbedding m (realSpinVectorRepresentation m g v) := by
  have hreal (w : EuclideanSpace ℂ (Fin m)) :
      complexSpinorComplexificationEquiv m ((1 : ℂ) ⊗ₜ[ℝ] w) =
        complexSpinorRealEmbedding m w := by
    rw [complexSpinorComplexificationEquiv_tmul, one_smul]
  rw [← hreal]
  change complexSpinorComplexificationEquiv m
    ((realSpinVectorRepresentation m g).baseChange ℝ ℂ _ _
      ((complexSpinorComplexificationEquiv m).symm
        (complexSpinorComplexificationEquiv m ((1 : ℂ) ⊗ₜ[ℝ] v)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul, hreal]

/-- The complexified vector action is implemented by conjugation in the original spinor module. -/
theorem complexSpinVectorComplexification_generator (m : ℕ)
    (g : spinGroup (realSpinorQuadraticForm m))
    (u : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    complexSpinorGenerator m (complexSpinVectorComplexification m g u) =
      (complexSpinRepresentation m g).conjAlgEquiv ℂ (complexSpinorGenerator m u) := by
  have hreal (v : EuclideanSpace ℂ (Fin m)) :
      complexSpinorGenerator m (complexSpinorRealEmbedding m (realSpinVectorRepresentation m g v)) =
        (complexSpinRepresentation m g).conjAlgEquiv ℂ
          (complexSpinorGenerator m (complexSpinorRealEmbedding m v)) := by
    have hg (w : EuclideanSpace ℂ (Fin m)) :
        complexSpinorGenerator m (complexSpinorRealEmbedding m w) = cliffordSymbol w := by
      have h := complexSpinorRepresentation_real m w
      rwa [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply] at h
    rw [hg, hg]
    apply LinearMap.ext
    intro s
    obtain ⟨t, rfl⟩ := (complexSpinRepresentation m g).surjective s
    simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      complexSpinRepresentation_cliffordSymbol m g v t
  -- Pure tensors span the native scalar extension; both generator expressions are complex linear.
  obtain ⟨z, rfl⟩ := (complexSpinorComplexificationEquiv m).surjective u
  change complexSpinorGenerator m (complexSpinorComplexificationEquiv m
    ((realSpinVectorRepresentation m g).baseChange ℝ ℂ _ _
      ((complexSpinorComplexificationEquiv m).symm (complexSpinorComplexificationEquiv m z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z v =>
    rw [LinearEquiv.baseChange_tmul, complexSpinorComplexificationEquiv_tmul,
      complexSpinorComplexificationEquiv_tmul, map_smul, map_smul, hreal, map_smul]

/-- The original complex quadratic form is preserved by that same complexified Spin action. -/
theorem complexSpinVectorComplexification_quadraticForm (m : ℕ)
    (g : spinGroup (realSpinorQuadraticForm m))
    (u : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    complexSpinorQuadraticForm m (complexSpinVectorComplexification m g u) =
      complexSpinorQuadraticForm m u := by
  -- Square the actual intertwined generators and use faithful scalar multiplication.
  apply (algebraMap ℂ (Module.End ℂ (ComplexSpinor m))).injective
  rw [← complexSpinorGenerator_sq, complexSpinVectorComplexification_generator,
    ← map_mul, complexSpinorGenerator_sq]
  exact AlgEquiv.commutes _ _

/-- The complexified native Spin action as a quadratic isometry for form-change naturality. -/
def complexSpinVectorComplexificationIsometry (m : ℕ)
    (g : spinGroup (realSpinorQuadraticForm m)) :
    complexSpinorQuadraticForm m →qᵢ complexSpinorQuadraticForm m where
  toLinearMap := (complexSpinVectorComplexification m g).toLinearMap
  map_app' := complexSpinVectorComplexification_quadraticForm m g

end AtiyahSinger
