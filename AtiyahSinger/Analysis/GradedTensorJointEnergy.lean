/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorJointGraph

/-!
# Energy on the closures of the simultaneous tensor cores

Public module ID: M0715.

Adjunction cancels the cross term on pure tensors, then on their spans and both
joint graph closures. All unbounded factor images are retained as coordinates
of those closures; no passage from ambient convergence alone is used.
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

/-- The original graded energy identity extends to the two closed joint tensor cores. -/
theorem graded_tensor_joint_energy (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)
    (hP : Dense (P.domain : Set H₀)) (hQ : Dense (Q.domain : Set K₀))
    (x : Completion (H₀ ⊗[ℂ] K₀) ×
      Completion (H₁ ⊗[ℂ] K₀) × Completion (H₀ ⊗[ℂ] K₁))
    (y : Completion (H₁ ⊗[ℂ] K₁) ×
      Completion (H₀ ⊗[ℂ] K₁) × Completion (H₁ ⊗[ℂ] K₀))
    (hx : x ∈ (TensorProduct.jointGraph P Q).topologicalClosure)
    (hy : y ∈ (TensorProduct.jointGraph P.adjoint Q.adjoint).topologicalClosure) :
    ‖x.2.1 - y.2.2‖ ^ 2 + ‖x.2.2 + y.2.1‖ ^ 2 =
      ‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2 + ‖y.2.1‖ ^ 2 + ‖y.2.2‖ ^ 2 := by
  have hcross : inner ℂ x.2.1 y.2.2 = inner ℂ x.2.2 y.2.1 := by
    have hclosed : _root_.IsClosed {y : Completion (H₁ ⊗[ℂ] K₁) ×
        Completion (H₀ ⊗[ℂ] K₁) × Completion (H₁ ⊗[ℂ] K₀) |
        inner ℂ x.2.1 y.2.2 = inner ℂ x.2.2 y.2.1} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hclosed.closure_subset_iff.mpr ?_ hy
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨u', v'⟩, rfl⟩ := hy
      -- First extend in the first graph while keeping an actual adjoint-domain pure test.
      have hclosed' : _root_.IsClosed {x : Completion (H₀ ⊗[ℂ] K₀) ×
          Completion (H₁ ⊗[ℂ] K₀) × Completion (H₀ ⊗[ℂ] K₁) |
          inner ℂ x.2.1 (↑((u' : H₁) ⊗ₜ[ℂ] Q.adjoint v')) =
            inner ℂ x.2.2 (↑(P.adjoint u' ⊗ₜ[ℂ] (v' : K₁)))} :=
        isClosed_eq (by fun_prop) (by fun_prop)
      apply hclosed'.closure_subset_iff.mpr ?_ hx
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨u, v⟩, rfl⟩ := hx
        simp only [Set.mem_ofPred_eq, Completion.inner_coe, TensorProduct.inner_tmul]
        exact congrArg₂ (· * ·) ((P.adjoint_isFormalAdjoint hP).symm u u')
          ((Q.adjoint_isFormalAdjoint hQ).symm v v').symm
      | zero => simp
      | add x z hx hz h₁ h₂ =>
        simpa only [Set.mem_ofPred_eq, Prod.snd_add, Prod.fst_add, inner_add_left] using
          congrArg₂ (· + ·) h₁ h₂
      | smul a x hx h₁ =>
        simpa only [Set.mem_ofPred_eq, Prod.smul_snd, Prod.smul_fst, inner_smul_left] using
          congrArg (fun b : ℂ ↦ starRingEnd ℂ a * b) h₁
    | zero => simp
    | add y z hy hz h₁ h₂ =>
      simpa only [Set.mem_ofPred_eq, Prod.snd_add, Prod.fst_add, inner_add_right] using
        congrArg₂ (· + ·) h₁ h₂
    | smul a y hy h₁ =>
      simpa only [Set.mem_ofPred_eq, Prod.smul_snd, Prod.smul_fst, inner_smul_right] using
        congrArg (fun b : ℂ ↦ a * b) h₁
  -- Continuity of both graph-coordinate pairings has preserved the cancelling cross terms.
  rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hcross]
  ring

end LinearPMap
