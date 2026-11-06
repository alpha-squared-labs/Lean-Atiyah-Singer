/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorCompletion

/-!
# Kernels of bounded Hilbert tensor amplifications

Public module ID: M0735.

The kernel of a bounded map tensored with the identity is the completed tensor
of its actual kernel with the other factor. This remains true when its range is
not closed. The proof uses the closure of the adjoint range, rather than an
inverse or a positive spectral gap. Applied to coordinate maps of a closed graph,
this identifies the kernels of unbounded tensor amplifications.
-/

@[expose] public noncomputable section

namespace TensorProduct

open UniformSpace
open scoped TensorProduct

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Annihilation of the two orthogonal factor directions detects the completed subspace tensor. -/
theorem mem_range_completion_mapL_subtype_of_orthogonal
    (S : Submodule ℂ E) (T : Submodule ℂ F)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (u : Completion (E ⊗[ℂ] F))
    (hS : ∀ x ∈ S.orthogonal, ∀ y : F, inner ℂ u (↑(x ⊗ₜ[ℂ] y)) = 0)
    (hT : ∀ y ∈ T.orthogonal, ∀ x : E, inner ℂ u (↑(x ⊗ₜ[ℂ] y)) = 0) :
    u ∈ (mapL S.subtypeL T.subtypeL).completion.range := by
  apply (mem_range_completion_mapL_subtype_iff S T u).mpr
  apply completion_ext_inner_tmul
  intro x y
  have hSadj : S.starProjection.adjoint = S.starProjection :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      S.starProjection_isSymmetric).star_eq
  have hTadj : T.starProjection.adjoint = T.starProjection :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      T.starProjection_isSymmetric).star_eq
  rw [inner_completion_mapL_tmul, hSadj, hTadj]
  -- Remove one orthogonal component at a time, using the same two original projections.
  have hx := hS (x - S.starProjection x) (S.sub_starProjection_mem_orthogonal x) y
  rw [sub_tmul, Completion.coe_sub, inner_sub_right, sub_eq_zero] at hx
  have hy := hT (y - T.starProjection y) (T.sub_starProjection_mem_orthogonal y)
    (S.starProjection x)
  rw [tmul_sub, Completion.coe_sub, inner_sub_right, sub_eq_zero] at hy
  exact hy.symm.trans hx.symm

/-- The kernel of a bounded left tensor amplification is the image of the original kernel tensor. -/
theorem ker_completion_mapL_id (f : E →L[ℂ] F) :
    (mapL f (ContinuousLinearMap.id ℂ K)).completion.ker =
      (mapL f.ker.subtypeL (ContinuousLinearMap.id ℂ K)).completion.range := by
  let S := f.ker
  let I := ContinuousLinearMap.id ℂ K
  let A := (mapL f I).completion
  let ι := (mapL S.subtypeL I).completion
  let π := (mapL S.orthogonalProjectionOnto I).completion
  let P := (mapL S.starProjection I).completion
  have hιπ : ι.comp π = P := by
    dsimp only [ι, π, P]
    rw [← completion_mapL_comp]
    rfl
  have hstar : S.starProjection.adjoint = S.starProjection :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      S.starProjection_isSymmetric).star_eq
  apply le_antisymm
  · intro u hu
    have hu0 : A u = 0 := hu
    -- The vanished amplified image makes u annihilate every tensor from range(f adjoint).
    have hann (y : F) (k : K) : inner ℂ u (↑(f.adjoint y ⊗ₜ[ℂ] k)) = 0 := by
      have h := inner_completion_mapL_tmul f I u y k
      change inner ℂ (A u) _ = _ at h
      rw [hu0] at h
      simpa only [I, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
        inner_zero_left] using h.symm
    have hclosed (k : K) (z : E) (hz : z ∈ S.orthogonal) :
        inner ℂ u (↑(z ⊗ₜ[ℂ] k)) = 0 := by
      rw [f.orthogonal_ker] at hz
      -- Continuity extends annihilation to the full closure of the adjoint range.
      apply closure_minimal (t := {z : E | inner ℂ u (↑(z ⊗ₜ[ℂ] k)) = 0}) ?_ ?_ hz
      · rintro _ ⟨y, rfl⟩
        exact hann y k
      · exact isClosed_eq (by fun_prop) continuous_const
    have hPu : P u = u := by
      apply completion_ext_inner_tmul
      intro x k
      have h := inner_completion_mapL_tmul S.starProjection I u x k
      rw [hstar] at h
      simp only [I, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] at h
      rw [h]
      have hz := hclosed k (x - S.starProjection x) (S.sub_starProjection_mem_orthogonal x)
      rw [sub_tmul, Completion.coe_sub, inner_sub_right, sub_eq_zero] at hz
      exact hz.symm
    -- The fixed-point identity gives an explicit preimage under the original inclusion.
    refine ⟨π u, ?_⟩
    exact (congrArg (fun T ↦ T u) hιπ).trans hPu
  · rintro u ⟨v, rfl⟩
    -- Each actual kernel tensor is killed, and density gives the same assertion after completion.
    change A (ι v) = 0
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_const
    | ih v =>
      dsimp only [A, ι]
      rw [ContinuousLinearMap.completion_apply_coe,
        ContinuousLinearMap.completion_apply_coe, ← ContinuousLinearMap.comp_apply,
        ← mapL_comp]
      have hfS : f.comp S.subtypeL = 0 := by
        ext x
        exact x.property
      simp only [hfS, mapL_zero_left, zero_apply, Completion.coe_zero]

end TensorProduct
