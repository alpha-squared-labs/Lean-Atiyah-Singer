/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TensorSectionOperator
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# The actual kernel of a finite tensor section operator

Public module ID: M1500.

Tensoring the original kernel inclusion and evaluating the original sections
gives an isomorphism onto the full kernel of the specified tensor section
operator. Flatness over the field proves surjectivity; no target kernel is
defined to be the desired finite span. The evaluation formula keeps the
coefficient factor and every original section value unchanged.

This is the algebraic fiberwise kernel comparison used for both vertical
operators in SG III.13.6. Smooth descent of varying base coefficients remains
a separate assertion in the prescribed associated atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable (U : Type*) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  {M : Type*} {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]

/-- The same kernel inclusion and pointwise evaluation identify the entire tensor kernel. -/
theorem exists_tensorSectionKernelEquiv (X : Submodule ℂ (∀ x, E x))
    (Y : Submodule ℂ (∀ x, F x)) (L : X →ₗ[ℂ] Y) :
    ∃ e : U ⊗[ℂ] L.ker ≃ₗ[ℂ] (tensorSectionOperator U X Y L).ker,
      ∀ t : U ⊗[ℂ] L.ker,
        (e t).val.val = tensorSectionEvaluation U X ((L.ker.subtype.lTensor U) t) := by
  let K := tensorSectionOperator U X Y L
  let eX := tensorSectionEquiv U X
  let eY := tensorSectionEquiv U Y
  let i := L.ker.subtype.lTensor U
  let f : U ⊗[ℂ] L.ker →ₗ[ℂ] dualTensorSections U X := eX.toLinearMap.comp i
  have hcomp (t : U ⊗[ℂ] X) : K (eX t) = eY ((L.lTensor U) t) := by
    simp [K, tensorSectionOperator, eX, eY]
  have hexact := Module.Flat.lTensor_exact U L.exact_subtype_ker_map
  have hfker (t : U ⊗[ℂ] L.ker) : f t ∈ K.ker := by
    change K (eX (i t)) = 0
    rw [hcomp]
    have ht : (L.lTensor U) (i t) = 0 := (hexact (i t)).mpr ⟨t, rfl⟩
    rw [ht, map_zero]
  let fK := f.codRestrict K.ker hfker
  have hf : Function.Bijective fK := by
    constructor
    · intro t s hts
      have hi : Function.Injective i :=
        Module.Flat.lTensor_preserves_injective_linearMap L.ker.subtype
          L.ker.injective_subtype
      apply hi
      apply eX.injective
      exact congrArg (fun z : K.ker ↦ z.val) hts
    · intro w
      let t := eX.symm w.val
      have ht : (L.lTensor U) t = 0 := by
        apply eY.injective
        rw [map_zero, ← hcomp]
        change K (eX (eX.symm w.val)) = 0
        rw [eX.apply_symm_apply]
        exact w.property
      obtain ⟨s, hs⟩ := (hexact t).mp ht
      refine ⟨s, ?_⟩
      apply Subtype.ext
      change eX (i s) = w.val
      rw [hs]
      exact eX.apply_symm_apply _
  exact ⟨LinearEquiv.ofBijective fK hf, fun _ ↦ rfl⟩

end AtiyahSinger
