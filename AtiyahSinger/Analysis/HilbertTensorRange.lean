/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedOperatorRange
public import AtiyahSinger.Analysis.HilbertTensorCompletion

/-!
# The tensor estimate away from the two factor kernels

Public module ID: M0737.

Bounded generalized inverses of closed-range operators express the complement of
the tensor kernel projection in terms of the two actual factor images. The estimate
is proved on the original finite domain tensors, ready for passage to a closed graph.
-/

@[expose] public noncomputable section

namespace TensorProduct

open UniformSpace
open scoped TensorProduct

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']

/-- The two original factor images control the complement of the tensor kernel projection. -/
theorem exists_bound_sub_kernelProjection (P : E →ₗ.[ℂ] E') (Q : F →ₗ.[ℂ] F')
    [P.ker.HasOrthogonalProjection] [Q.ker.HasOrthogonalProjection]
    (hP : Dense (P.domain : Set E)) (hQ : Dense (Q.domain : Set F))
    (hPc : P.IsClosed) (hQc : Q.IsClosed)
    (hPr : IsClosed (P.toFun.range : Set E')) (hQr : IsClosed (Q.toFun.range : Set F')) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : P.domain ⊗[ℂ] Q.domain,
      ‖(↑(map P.domain.subtype Q.domain.subtype x) : Completion (E ⊗[ℂ] F)) -
        (mapL P.ker.starProjection Q.ker.starProjection).completion
          (↑(map P.domain.subtype Q.domain.subtype x))‖ ≤
      C * (‖(↑(map P.toFun Q.domain.subtype x) : Completion (E' ⊗[ℂ] F))‖ +
        ‖(↑(map P.domain.subtype Q.toFun x) : Completion (E ⊗[ℂ] F'))‖) := by
  obtain ⟨S, hSorth, hSgraph⟩ := P.exists_bounded_generalizedInverse hP hPc hPr
  obtain ⟨T, hTorth, hTgraph⟩ := Q.exists_bounded_generalizedInverse hQ hQc hQr
  -- These bounded inverses give exactly the original orthogonal kernel complements.
  have hS (u : P.domain) : S (P u) = (u : E) - P.ker.starProjection u := by
    obtain ⟨v, hv, hPv⟩ := P.mem_graph_iff.mp (hSgraph (P u) ⟨u, rfl⟩)
    have hk : (u : E) - S (P u) ∈ P.ker := by
      apply P.mem_ker_iff.mpr
      refine ⟨u - v, ?_, ?_⟩
      · change (u : E) - S (P u) = (u : E) - v
        rw [hv]
      · rw [P.map_sub, hPv, sub_self]
    have heq := P.ker.eq_starProjection_of_mem_orthogonal hk
      (show (u : E) - ((u : E) - S (P u)) ∈ P.ker.orthogonal by
        simpa only [sub_sub_cancel] using hSorth (P u))
    rw [heq, sub_sub_cancel]
  have hT (v : Q.domain) : T (Q v) = (v : F) - Q.ker.starProjection v := by
    obtain ⟨w, hw, hQw⟩ := Q.mem_graph_iff.mp (hTgraph (Q v) ⟨v, rfl⟩)
    have hk : (v : F) - T (Q v) ∈ Q.ker := by
      apply Q.mem_ker_iff.mpr
      refine ⟨v - w, ?_, ?_⟩
      · change (v : F) - T (Q v) = (v : F) - w
        rw [hw]
      · rw [Q.map_sub, hQw, sub_self]
    have heq := Q.ker.eq_starProjection_of_mem_orthogonal hk
      (show (v : F) - ((v : F) - T (Q v)) ∈ Q.ker.orthogonal by
        simpa only [sub_sub_cancel] using hTorth (Q v))
    rw [heq, sub_sub_cancel]
  let A := (mapL S (ContinuousLinearMap.id ℂ F)).completion
  let B := (mapL P.ker.starProjection T).completion
  refine ⟨‖A‖ + ‖B‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  intro x
  -- Remove the first orthogonal component, then the second, without changing the tensor norm.
  have hdecomp :
      (↑(map P.domain.subtype Q.domain.subtype x) : Completion (E ⊗[ℂ] F)) -
        (mapL P.ker.starProjection Q.ker.starProjection).completion
          (↑(map P.domain.subtype Q.domain.subtype x)) =
      A (↑(map P.toFun Q.domain.subtype x)) +
        B (↑(map P.domain.subtype Q.toFun x)) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [map_tmul, Submodule.subtype_apply,
        ContinuousLinearMap.completion_apply_coe, mapL_tmul,
        ContinuousLinearMap.id_apply, A, B]
      change _ = (↑(S (P u) ⊗ₜ[ℂ] (v : F)) : Completion (E ⊗[ℂ] F)) +
        (↑(P.ker.starProjection u ⊗ₜ[ℂ] T (Q v)))
      rw [hS, hT, sub_tmul, tmul_sub, Completion.coe_sub, Completion.coe_sub]
      abel
    | add x y hx hy =>
      simp only [_root_.map_add, Completion.coe_add] at hx hy ⊢
      rw [add_sub_add_comm, hx, hy]
      abel
  rw [hdecomp]
  calc
    _ ≤ ‖A (↑(map P.toFun Q.domain.subtype x))‖ +
        ‖B (↑(map P.domain.subtype Q.toFun x))‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖(↑(map P.toFun Q.domain.subtype x) : Completion (E' ⊗[ℂ] F))‖ +
        ‖B‖ * ‖(↑(map P.domain.subtype Q.toFun x) : Completion (E ⊗[ℂ] F'))‖ :=
      add_le_add (A.le_opNorm _) (B.le_opNorm _)
    _ ≤ _ := by
      nlinarith [mul_nonneg (norm_nonneg A)
        (norm_nonneg (↑(map P.domain.subtype Q.toFun x) : Completion (E ⊗[ℂ] F'))),
        mul_nonneg (norm_nonneg B)
          (norm_nonneg (↑(map P.toFun Q.domain.subtype x) : Completion (E' ⊗[ℂ] F)))]

end TensorProduct
