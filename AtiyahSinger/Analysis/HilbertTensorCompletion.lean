/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Subspace inclusions in completed Hilbert tensor products

Public module ID: M0732.

Completion preserves the actual tensor maps and their compositions. In particular,
the tensor of two isometric subspace inclusions is still isometric, and its image
is the fixed space of the tensor of the original orthogonal projections.

These standard Hilbert space facts are used for the kernel summands of the graded
tensor operator. They concern the specified maps, including infinite dimensional
subspaces; no dimension comparison or algebraic tensor completeness is used.
-/

@[expose] public noncomputable section

namespace TensorProduct

open UniformSpace
open scoped TensorProduct

variable {E E' E'' F F' F'' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
  [NormedAddCommGroup F''] [InnerProductSpace ℂ F'']

/-- Completing the tensor of the two given isometries preserves its norm exactly. -/
theorem isometry_completion_mapL (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F') :
    Isometry ((mapL f.toContinuousLinearMap g.toContinuousLinearMap).completion) := by
  -- Identify the existing continuous tensor map with its isometric construction.
  have h : (mapIsometry f g).toContinuousLinearMap =
      mapL f.toContinuousLinearMap g.toContinuousLinearMap := by
    ext x
    simp only [LinearIsometry.coe_toContinuousLinearMap, mapIsometry_apply, mapL_apply,
      LinearIsometry.toLinearMap_toContinuousLinearMap]
  rw [← h]
  exact (mapIsometry f g).completion.isometry

/-- The completed tensor maps compose in the same order as both original factor maps. -/
theorem completion_mapL_comp (f : E' →L[ℂ] E'') (f' : E →L[ℂ] E')
    (g : F' →L[ℂ] F'') (g' : F →L[ℂ] F') :
    (mapL (f.comp f') (g.comp g')).completion =
      (mapL f g).completion.comp (mapL f' g').completion := by
  -- Continuous maps on the completion agree once they agree on its dense algebraic tensor.
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.completion_apply_coe]
    congr 1
    exact congrArg (fun T ↦ T x) (mapL_comp f f' g g')

/-- The original identity tensor map completes to the identity of the Hilbert tensor product. -/
theorem completion_mapL_id :
    (mapL (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F)).completion =
      ContinuousLinearMap.id ℂ (Completion (E ⊗[ℂ] F)) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp

/-- The actual completed subspace inclusion has the fixed space of the two projections as image. -/
theorem mem_range_completion_mapL_subtype_iff
    (S : Submodule ℂ E) (T : Submodule ℂ F)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (u : Completion (E ⊗[ℂ] F)) :
    u ∈ (mapL S.subtypeL T.subtypeL).completion.range ↔
      (mapL S.starProjection T.starProjection).completion u = u := by
  let ι := (mapL S.subtypeL T.subtypeL).completion
  let π := (mapL S.orthogonalProjectionOnto T.orthogonalProjectionOnto).completion
  let P := (mapL S.starProjection T.starProjection).completion
  -- Inclusion followed by projection is the same tensor of the original factor projections.
  have hιπ : ι.comp π = P := by
    exact (completion_mapL_comp S.subtypeL S.orthogonalProjectionOnto
      T.subtypeL T.orthogonalProjectionOnto).symm
  have hS : S.starProjection.comp S.subtypeL = S.subtypeL := by
    ext x
    exact S.starProjection_mem_subspace_eq_self x
  have hT : T.starProjection.comp T.subtypeL = T.subtypeL := by
    ext x
    exact T.starProjection_mem_subspace_eq_self x
  have hPι : P.comp ι = ι := by
    dsimp only [P, ι]
    rw [← completion_mapL_comp, hS, hT]
  constructor
  · rintro ⟨v, rfl⟩
    exact congrArg (fun f ↦ f v) hPι
  · intro hu
    -- Project into the two original subspaces; the given fixed-point equation recovers u.
    refine ⟨π u, ?_⟩
    exact (congrArg (fun f ↦ f u) hιπ).trans hu

/-- Inner products against original pure tensors determine a vector in the Hilbert completion. -/
theorem completion_ext_inner_tmul {u v : Completion (E ⊗[ℂ] F)}
    (h : ∀ (x : E) (y : F),
      inner ℂ u (↑(x ⊗ₜ[ℂ] y)) = inner ℂ v (↑(x ⊗ₜ[ℂ] y))) : u = v := by
  apply ext_inner_right ℂ
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simp only [Completion.coe_add, inner_add_right, hx, hy]

/-- The completed tensor map retains the adjunction identity on every pure test tensor. -/
theorem inner_completion_mapL_tmul [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace E'] [CompleteSpace F']
    (f : E →L[ℂ] E') (g : F →L[ℂ] F') (u : Completion (E ⊗[ℂ] F))
    (x : E') (y : F') :
    inner ℂ ((mapL f g).completion u) (↑(x ⊗ₜ[ℂ] y)) =
      inner ℂ u (↑(f.adjoint x ⊗ₜ[ℂ] g.adjoint y)) := by
  -- First pass to the dense algebraic tensor, then use factor adjunction on its generators.
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    rw [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe, Completion.inner_coe]
    induction u using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [mapL_tmul, inner_tmul, ContinuousLinearMap.adjoint_inner_right]
    | add a b ha hb => simp only [_root_.map_add, inner_add_left, ha, hb]

end TensorProduct
