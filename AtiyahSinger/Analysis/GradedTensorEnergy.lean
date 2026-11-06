/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorCompletion
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Energy of the original graded tensor core

Public module ID: M0712.

For finite sums of tensors in the two original operator domains, factor
adjunction cancels the mixed terms of the graded matrix. The statement allows
arbitrary finite tensor sums in both parity components. Extending this identity
to a closed domain requires graph convergence and is a separate argument.

This is the algebraic calculation in SG III.13.5, (13.12)--(13.14).
-/

@[expose] public noncomputable section

namespace LinearPMap

open UniformSpace
open scoped TensorProduct

variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]

/-- The two original tensor columns have no mixed contribution to the graded squared norm. -/
theorem graded_tensor_core_energy (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)
    (hP : Dense (P.domain : Set H₀)) (hQ : Dense (Q.domain : Set K₀))
    (x : P.domain ⊗[ℂ] Q.domain) (y : P.adjoint.domain ⊗[ℂ] Q.adjoint.domain) :
    let a : Completion (H₁ ⊗[ℂ] K₀) :=
      ↑(TensorProduct.map P.toFun Q.domain.subtype x)
    let b : Completion (H₀ ⊗[ℂ] K₁) :=
      ↑(TensorProduct.map P.domain.subtype Q.toFun x)
    let c : Completion (H₀ ⊗[ℂ] K₁) :=
      ↑(TensorProduct.map P.adjoint.toFun Q.adjoint.domain.subtype y)
    let d : Completion (H₁ ⊗[ℂ] K₀) :=
      ↑(TensorProduct.map P.adjoint.domain.subtype Q.adjoint.toFun y)
    ‖a - d‖ ^ 2 + ‖b + c‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
  -- Tensor induction extends the two original adjunction identities to finite sums.
  have hcross (x : P.domain ⊗[ℂ] Q.domain)
      (y : P.adjoint.domain ⊗[ℂ] Q.adjoint.domain) :
      inner ℂ (TensorProduct.map P.toFun Q.domain.subtype x)
          (TensorProduct.map P.adjoint.domain.subtype Q.adjoint.toFun y) =
        inner ℂ (TensorProduct.map P.domain.subtype Q.toFun x)
          (TensorProduct.map P.adjoint.toFun Q.adjoint.domain.subtype y) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      induction y using TensorProduct.inductionOn with
      | tmul u' v' =>
        simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, Submodule.subtype_apply]
        exact congrArg₂ (· * ·) ((P.adjoint_isFormalAdjoint hP).symm u u')
          ((Q.adjoint_isFormalAdjoint hQ).symm v v').symm
      | add y z hy hz => simp only [_root_.map_add, inner_add_right, hy, hz]
    | add x z hx hz => simp only [_root_.map_add, inner_add_left, hx, hz]
  -- Completion preserves these inner products, so the two real cross terms cancel.
  dsimp only
  rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ),
    Completion.inner_coe, Completion.inner_coe, hcross]
  ring

end LinearPMap
