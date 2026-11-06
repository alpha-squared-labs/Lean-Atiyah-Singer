/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteRepresentationTensor
public import AtiyahSinger.Analysis.HilbertTensorOperator

/-!
# Finite representation coordinates in the original Hilbert tensor completion

Public module ID: M0624.

The specified finite coordinates identify the actual Hilbert tensor product
with the representation ring's ordered tensor coordinates. The intertwiner
retains both original factor actions. This applies to the four finite kernel
and adjoint-kernel pairs in the graded product operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open UniformSpace
open scoped TensorProduct

variable {G E F : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite tensor coordinates intertwine the original completed tensor action. -/
theorem exists_hilbertTensorProduct_coordinates
    (ρ σ : FiniteContinuousRepresentation G)
    (A : G → E →L[ℂ] E) (B : G → F →L[ℂ] F)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] E)
    (f : (Fin σ.dimension → ℂ) ≃ₗ[ℂ] F)
    (he : ∀ g v, e (ρ.representation g v) = A g (e v))
    (hf : ∀ g w, f (σ.representation g w) = B g (f w)) :
    ∃ c : (Fin (ρ.tensor σ).dimension → ℂ) ≃ₗ[ℂ] HilbertTensorProduct E F,
      (∀ v w, c (FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
        (v ⊗ₜ[ℂ] w)) = (Completion.toComplL (S := ℂ)) (e v ⊗ₜ[ℂ] f w)) ∧
      ∀ g z, c ((ρ.tensor σ).representation g z) =
        hilbertTensorMap (A g) (B g) (c z) := by
  classical
  -- These specified finite spaces are complete, so their tensor completion adds no vectors.
  let : FiniteDimensional ℂ E := Module.Finite.equiv e
  let : FiniteDimensional ℂ F := Module.Finite.equiv f
  let : CompleteSpace (E ⊗[ℂ] F) := FiniteDimensional.complete ℂ _
  let ι : (E ⊗[ℂ] F) →ₗᵢ[ℂ] HilbertTensorProduct E F := Completion.toComplₗᵢ
  have hι : Function.Bijective ι := by
    refine ⟨ι.injective, ?_⟩
    intro z
    have hz : z ∈ closure (Set.range ι) := Completion.denseRange_coe z
    rwa [ι.isometry.isClosedEmbedding.isClosed_range.closure_eq] at hz
  let j := LinearEquiv.ofBijective ι.toLinearMap hι
  let d := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
  let c := (d.symm.trans (TensorProduct.congr e f)).trans j
  have hc (v : Fin ρ.dimension → ℂ) (w : Fin σ.dimension → ℂ) :
      c (d (v ⊗ₜ[ℂ] w)) = (Completion.toComplL (S := ℂ)) (e v ⊗ₜ[ℂ] f w) := by
    simp only [c, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      TensorProduct.congr_tmul]
    rfl
  refine ⟨c, hc, ?_⟩
  -- Check the actual ordered pure tensors; additivity covers their entire algebraic tensor.
  intro g z
  obtain ⟨w, rfl⟩ := d.surjective z
  induction w using TensorProduct.inductionOn with
  | tmul v w =>
    rw [FiniteContinuousRepresentation.tensor_tmul]
    change c (d (ρ.representation g v ⊗ₜ[ℂ] σ.representation g w)) =
      hilbertTensorMap (A g) (B g) (c (d (v ⊗ₜ[ℂ] w)))
    rw [hc, hc, he, hf]
    change ((A g (e v) ⊗ₜ[ℂ] B g (f w)) : Completion (E ⊗[ℂ] F)) =
      (TensorProduct.mapL (A g) (B g)).completion
        ((e v ⊗ₜ[ℂ] f w) : Completion (E ⊗[ℂ] F))
    rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
  | add v w hv hw => simp only [map_add, hv, hw]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor of finite invariant subspaces retains the actual ambient tensor inclusion. -/
theorem exists_hilbertTensorSubspace_coordinates
    (S : Submodule ℂ E) (T : Submodule ℂ F)
    (ρ σ : FiniteContinuousRepresentation G)
    (A : G → E →L[ℂ] E) (B : G → F →L[ℂ] F)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] S)
    (f : (Fin σ.dimension → ℂ) ≃ₗ[ℂ] T)
    (he : ∀ g v, (e (ρ.representation g v)).val = A g (e v).val)
    (hf : ∀ g w, (f (σ.representation g w)).val = B g (f w).val) :
    ∃ c : (Fin (ρ.tensor σ).dimension → ℂ) ≃ₗ[ℂ] HilbertTensorProduct S T,
      ∀ g z, hilbertTensorMap S.subtypeL T.subtypeL (c ((ρ.tensor σ).representation g z)) =
        hilbertTensorMap (A g) (B g) (hilbertTensorMap S.subtypeL T.subtypeL (c z)) := by
  let : FiniteDimensional ℂ S := Module.Finite.equiv e
  let : FiniteDimensional ℂ T := Module.Finite.equiv f
  let e' := e.toContinuousLinearEquiv
  let f' := f.toContinuousLinearEquiv
  let AS (g : G) := e'.toContinuousLinearMap.comp
    ((ρ.representation g).comp e'.symm.toContinuousLinearMap)
  let BT (g : G) := f'.toContinuousLinearMap.comp
    ((σ.representation g).comp f'.symm.toContinuousLinearMap)
  have he' (g : G) (v : Fin ρ.dimension → ℂ) : e (ρ.representation g v) = AS g (e v) := by
    change e (ρ.representation g v) = e (ρ.representation g (e.symm (e v)))
    rw [e.symm_apply_apply]
  have hf' (g : G) (v : Fin σ.dimension → ℂ) : f (σ.representation g v) = BT g (f v) := by
    change f (σ.representation g v) = f (σ.representation g (f.symm (f v)))
    rw [f.symm_apply_apply]
  obtain ⟨c, hc, haction⟩ := exists_hilbertTensorProduct_coordinates ρ σ AS BT e f he' hf'
  refine ⟨c, ?_⟩
  -- The two specified subspace inclusions commute with the original ambient maps.
  intro g z
  have hS : S.subtypeL.comp (AS g) = (A g).comp S.subtypeL := by
    ext x
    obtain ⟨v, rfl⟩ := e.surjective x
    change (AS g (e v)).val = A g (e v).val
    rw [← he']
    exact he g v
  have hT : T.subtypeL.comp (BT g) = (B g).comp T.subtypeL := by
    ext x
    obtain ⟨v, rfl⟩ := f.surjective x
    change (BT g (f v)).val = B g (f v).val
    rw [← hf']
    exact hf g v
  have hmaps : (hilbertTensorMap S.subtypeL T.subtypeL).comp
      (hilbertTensorMap (AS g) (BT g)) =
        (hilbertTensorMap (A g) (B g)).comp (hilbertTensorMap S.subtypeL T.subtypeL) := by
    dsimp only [hilbertTensorMap]
    rw [← TensorProduct.completion_mapL_comp, hS, hT, TensorProduct.completion_mapL_comp]
  rw [haction]
  exact congrArg (fun U ↦ U (c z)) hmaps

end AtiyahSinger
