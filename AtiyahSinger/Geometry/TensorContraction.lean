/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Contraction

/-!
# Basis independence of full tensor contraction

Public module ID: M1499.

The standard dual-tensor realization of a linear map identifies the finite
contraction in any two bases. This algebraic statement supplies the repeated
slot contraction in the geometric integer Sobolev norms of SG III.2 (2.1).
It does not require a positive form or a choice of an orthonormal basis.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module LinearMap
open scoped BigOperators TensorProduct

/-- Contracting a dual form and a value form on two linear maps is independent of the basis.
The two sums represent the same full tensor pairing, without alternating normalization. -/
theorem sum_tensor_pairing_basis_eq
    {K U V ι κ : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (b : Basis ι K U) (c : Basis κ K U)
    (g : LinearMap.BilinForm K (Module.Dual K U)) (h : LinearMap.BilinForm K V)
    (A B : U →ₗ[K] V) :
    (∑ i : ι, ∑ j : ι, g (b.coord i) (b.coord j) * h (A (b i)) (B (b j))) =
      ∑ i : κ, ∑ j : κ, g (c.coord i) (c.coord j) * h (A (c i)) (B (c j)) := by
  classical
  let T (F : U →ₗ[K] V) := ∑ i : ι, b.coord i ⊗ₜ[K] F (b i)
  let S (F : U →ₗ[K] V) := ∑ i : κ, c.coord i ⊗ₜ[K] F (c i)
  -- Both expansions are the unique tensor representing the original linear map.
  have hT (F : U →ₗ[K] V) : dualTensorHom K U V (T F) = F := by
    ext x
    simp only [T, map_sum, LinearMap.sum_apply, dualTensorHom_apply]
    simpa only [map_sum, map_smul, Basis.coord_apply] using congrArg F (b.sum_repr x)
  have hS (F : U →ₗ[K] V) : dualTensorHom K U V (S F) = F := by
    ext x
    simp only [S, map_sum, LinearMap.sum_apply, dualTensorHom_apply]
    simpa only [map_sum, map_smul, Basis.coord_apply] using congrArg F (c.sum_repr x)
  have hTS (F : U →ₗ[K] V) : T F = S F := by
    apply (dualTensorHomEquivOfBasis (N := V) b).injective
    exact (hT F).trans (hS F).symm
  -- Evaluate one tensor-product bilinear form on those same two represented maps.
  let H := g.tmul h
  have hpair : H (T A) (T B) = H (S A) (S B) := by rw [hTS A, hTS B]
  simp only [H, T, S, map_sum, LinearMap.sum_apply, LinearMap.BilinForm.tmul,
    LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] at hpair
  rw [Finset.sum_comm] at hpair
  conv_rhs at hpair => rw [Finset.sum_comm]
  simpa only [mul_comm] using hpair

end AtiyahSinger
