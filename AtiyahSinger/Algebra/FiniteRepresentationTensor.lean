/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Tensor products of finite continuous complex representations

Public module ID: M0028.

The algebraic tensor action is transported through the tensor product of the
standard coordinate bases and the fixed ordered equivalence finProdFinEquiv.
All operators and coordinates are actual constructions. Joint continuity is
a separate theorem about these operators, rather than an implicit consequence
of the name ContRepresentation. The tensor unit is the one-dimensional
trivial representation, not an arbitrary one-dimensional character.

SG III.9, printed p.212, uses tensor product and direct sum to construct the
representation ring. This construction uses no compactness, unitarity or
semisimplicity, and also includes zero-dimensional representations. Joint continuity and pure-tensor
evaluation are proved for these specified actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.FiniteContinuousRepresentation

-- Keep the original public hypotheses even when a proof only uses the supplied actions.
set_option linter.unusedSectionVars false

open scoped TensorProduct

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Standard ordered coordinates on the genuine tensor product of two finite models. -/
def tensorCoordinates (n m : ℕ) :
    ((Fin n → ℂ) ⊗[ℂ] (Fin m → ℂ)) ≃ₗ[ℂ] (Fin (n * m) → ℂ) :=
  ((Pi.basisFun ℂ (Fin n)).tensorProduct (Pi.basisFun ℂ (Fin m))).equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (n * m) ↦ ℂ) finProdFinEquiv)

/-- The actual algebraic tensor action, conjugated into the fixed finite product model. -/
def tensorRepresentation (ρ σ : FiniteContinuousRepresentation G) :
    ContRepresentation ℂ G (Fin (ρ.dimension * σ.dimension) → ℂ) :=
  .ofMonoidHom
    ((Module.End.toContinuousLinearMap (Fin (ρ.dimension * σ.dimension) → ℂ)).toMonoidHom.comp
      ((tensorCoordinates ρ.dimension σ.dimension).conjRingEquiv.toMonoidHom.comp
        (ρ.representation.toRepresentation.tprod σ.representation.toRepresentation)))

/-- The specified tensor action is jointly continuous in the group element and vector. -/
theorem continuous_tensorRepresentation (ρ σ : FiniteContinuousRepresentation G) :
    Continuous (fun p : G × (Fin (ρ.dimension * σ.dimension) → ℂ) ↦
      tensorRepresentation ρ σ p.1 p.2) := by
  /- Stage 1: evaluate each original jointly continuous action on the fixed
  standard basis vectors. Every matrix coefficient is a continuous function
  of the group element. In the displayed tensor basis, the action coefficients
  are products of the coefficients of the two original actions.
  Stage 2: each output coordinate is a finite sum of these coefficient products
  multiplied by an input coordinate. This gives joint continuity; the fixed
  finProdFinEquiv merely reorders coordinates. Empty coordinate sets cover
  either dimension zero without an additional nonzero-dimension assumption. -/
  classical
  let c : ((Fin ρ.dimension → ℂ) ⊗[ℂ] (Fin σ.dimension → ℂ)) ≃ₗ[ℂ]
      (Fin (ρ.dimension * σ.dimension) → ℂ) := tensorCoordinates ρ.dimension σ.dimension
  -- The specified coordinates turn a pure tensor into products of coordinates.
  have hpair : Continuous (fun p : (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) ↦
      c (p.1 ⊗ₜ[ℂ] p.2)) := by
    apply continuous_pi
    intro i
    simp only [c, tensorCoordinates, LinearEquiv.trans_apply, Module.Basis.equivFun_apply]
    change Continuous (fun p : (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) ↦
      (Equiv.piCongrLeft (fun _ : Fin (ρ.dimension * σ.dimension) ↦ ℂ) finProdFinEquiv)
        (((Pi.basisFun ℂ (Fin ρ.dimension)).tensorProduct
          (Pi.basisFun ℂ (Fin σ.dimension))).repr (p.1 ⊗ₜ[ℂ] p.2)) i)
    suffices h : Continuous (fun p : (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) ↦
        p.2 (finProdFinEquiv.symm i).2 * p.1 (finProdFinEquiv.symm i).1) by
      simpa [Equiv.piCongrLeft_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        Pi.basisFun_repr] using h
    fun_prop
  have htmul (g : G) (x : Fin ρ.dimension → ℂ) (y : Fin σ.dimension → ℂ) :
      tensorRepresentation ρ σ g (c (x ⊗ₜ[ℂ] y)) =
        c (ρ.representation g x ⊗ₜ[ℂ] σ.representation g y) := by
    change c (TensorProduct.map (ρ.representation g).toLinearMap
      (σ.representation g).toLinearMap (c.symm (c (x ⊗ₜ[ℂ] y)))) = _
    simp
  -- Expand in the transported tensor basis; every coefficient depends continuously on v.
  let b : Module.Basis (Fin ρ.dimension × Fin σ.dimension) ℂ
      (Fin (ρ.dimension * σ.dimension) → ℂ) :=
    ((Pi.basisFun ℂ (Fin ρ.dimension)).tensorProduct
      (Pi.basisFun ℂ (Fin σ.dimension))).map c
  have hb (i : Fin ρ.dimension × Fin σ.dimension) :
      Continuous (fun g : G ↦ tensorRepresentation ρ σ g (b i)) := by
    have hρ : Continuous (fun g : G ↦ ρ.representation g ((Pi.basisFun ℂ _) i.1)) :=
      ρ.continuous_action.comp (continuous_id.prodMk continuous_const)
    have hσ : Continuous (fun g : G ↦ σ.representation g ((Pi.basisFun ℂ _) i.2)) :=
      σ.continuous_action.comp (continuous_id.prodMk continuous_const)
    have hcomp := hpair.comp (hρ.prodMk hσ)
    apply hcomp.congr
    intro g
    simpa only [Function.comp_apply, b, Module.Basis.map_apply,
      Module.Basis.tensorProduct_apply'] using
      (htmul g ((Pi.basisFun ℂ _) i.1) ((Pi.basisFun ℂ _) i.2)).symm
  have hsum : Continuous (fun p : G × (Fin (ρ.dimension * σ.dimension) → ℂ) ↦
      ∑ i, b.repr p.2 i • tensorRepresentation ρ σ p.1 (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).smul
      ((hb i).comp continuous_fst)
  apply hsum.congr
  intro p
  simpa only [map_sum, map_smul] using congrArg (tensorRepresentation ρ σ p.1) (b.sum_repr p.2)

/-- Tensor product with its specified product dimension, actual action and joint continuity. -/
def tensor (ρ σ : FiniteContinuousRepresentation G) : FiniteContinuousRepresentation G where
  dimension := ρ.dimension * σ.dimension
  representation := tensorRepresentation ρ σ
  continuous_action := continuous_tensorRepresentation ρ σ

/-- The one-dimensional trivial representation, the tensor unit for representation classes. -/
def trivial : FiniteContinuousRepresentation G where
  dimension := 1
  representation := ContRepresentation.trivial ℂ G (Fin 1 → ℂ)
  continuous_action := continuous_snd

/-- The tensor action sends each actual pure tensor to the tensor of its two action images. -/
theorem tensor_tmul (ρ σ : FiniteContinuousRepresentation G) (g : G)
    (x : Fin ρ.dimension → ℂ) (y : Fin σ.dimension → ℂ) :
    (ρ.tensor σ).representation g
        (tensorCoordinates ρ.dimension σ.dimension (x ⊗ₜ[ℂ] y)) =
      tensorCoordinates ρ.dimension σ.dimension
        (ρ.representation g x ⊗ₜ[ℂ] σ.representation g y) := by
  /- Unfold the actual conjugated tensor operator. The inverse coordinate map
  cancels the supplied tensorCoordinates; mathlib's TensorProduct.map evaluates
  on x ⊗ y as ρ(g)x ⊗ σ(g)y. Reapply the same forward coordinates. Turning a
  finite-dimensional linear map into a continuous linear map changes no value. -/
  change tensorCoordinates ρ.dimension σ.dimension
    (TensorProduct.map (ρ.representation g).toLinearMap (σ.representation g).toLinearMap
      ((tensorCoordinates ρ.dimension σ.dimension).symm
        (tensorCoordinates ρ.dimension σ.dimension (x ⊗ₜ[ℂ] y)))) = _
  simp

end AtiyahSinger.FiniteContinuousRepresentation
