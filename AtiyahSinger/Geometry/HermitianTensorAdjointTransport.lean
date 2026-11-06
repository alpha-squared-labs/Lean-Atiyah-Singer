/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetricAdjoint
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor adjunction in the specified native Hermitian models

Public module ID: M1275.

The original pure-tensor pairings determine the adjoint of a tensor map after
transport through the specified fiber equivalences. The native adjoint uses
the original fiber topologies and metrics; no orthonormal frame or substitute
isomorphism is chosen. This supplies the reverse corners of the graded symbol
in SG III.13 from the same forward representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n r s : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]

set_option maxSynthPendingDepth 30 in
/-- The actual native metric adjoint is the tensor of the specified factor adjoints. -/
theorem SmoothHermitianMetric.adjoint_eq_tensorMap
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := s) F)
    {A₀ A₁ B₀ B₁ : Type*}
    [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
    [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
    (h₀ : InnerProductSpace.Core ℂ A₀) (h₁ : InnerProductSpace.Core ℂ A₁)
    (k₀ : InnerProductSpace.Core ℂ B₀) (k₁ : InnerProductSpace.Core ℂ B₁)
    (x : M) (e : A₀ ⊗[ℂ] B₀ ≃ₗ[ℂ] E x) (f : A₁ ⊗[ℂ] B₁ ≃ₗ[ℂ] F x)
    (he : ∀ u v a b, h.pairing x (e (u ⊗ₜ[ℂ] a)) (e (v ⊗ₜ[ℂ] b)) =
      h₀.inner u v * k₀.inner a b)
    (hf : ∀ u v a b, k.pairing x (f (u ⊗ₜ[ℂ] a)) (f (v ⊗ₜ[ℂ] b)) =
      h₁.inner u v * k₁.inner a b)
    (p : A₀ →ₗ[ℂ] A₁) (pi : A₁ →ₗ[ℂ] A₀)
    (q : B₀ →ₗ[ℂ] B₁) (qi : B₁ →ₗ[ℂ] B₀)
    (hp : ∀ u v, h₁.inner (p u) v = h₀.inner u (pi v))
    (hq : ∀ u v, k₁.inner (q u) v = k₀.inner u (qi v))
    (T : E x →L[ℂ] F x)
    (hT : ∀ u v, T (e (u ⊗ₜ[ℂ] v)) = f (p u ⊗ₜ[ℂ] q v)) :
    ∀ v, h.adjoint k x T (f v) = e (TensorProduct.map pi qi v) := by
  classical
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin s)) F x
  let R := e.toLinearMap.comp ((TensorProduct.map pi qi).comp f.symm.toLinearMap)
  let S : F x →L[ℂ] E x := R.toContinuousLinearMap
  have hS (v : A₁ ⊗[ℂ] B₁) : S (f v) = e (TensorProduct.map pi qi v) := by
    change e (TensorProduct.map pi qi (f.symm (f v))) = _
    rw [f.symm_apply_apply]
  -- Pure tensors determine both sesquilinear pairings by additivity.
  have hpair (u : A₀ ⊗[ℂ] B₀) (v : A₁ ⊗[ℂ] B₁) :
      k.pairing x (T (e u)) (f v) = h.pairing x (e u) (S (f v)) := by
    induction u using TensorProduct.inductionOn with
    | tmul u a =>
      induction v using TensorProduct.inductionOn with
      | tmul v b =>
        rw [hT, hS, TensorProduct.map_tmul, hf, he, hp, hq]
      | add v w hv hw =>
        simp only [map_add, SmoothHermitianMetric.pairing,
          InnerProductSpace.Core.inner_add_right]
        exact congrArg₂ (· + ·) hv hw
    | add u w hu hw =>
      simp only [map_add, SmoothHermitianMetric.pairing,
        InnerProductSpace.Core.inner_add_left]
      exact congrArg₂ (· + ·) hu hw
  -- Uniqueness identifies the original native adjoint, before returning its tensor values.
  have hadjoint : h.adjoint k x T = S := h.adjoint_eq k x T S (by
    intro u v
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := f.surjective v
    exact hpair u v)
  intro v
  rw [hadjoint, hS]

end AtiyahSinger
