/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Finite tensor coefficients in an actual space of sections

Public module ID: M1238.

Tensoring a prescribed section subspace by a finite-dimensional coefficient
space gives exactly the tensor-valued sections whose every dual contraction
belongs to that same subspace. The evaluation uses the original fibers and
sections. In particular one may use the actual smooth section space or the
kernel of a specified operator; no kernel is defined by the desired span.

This elementary dual-basis argument supplies finite coefficient reconstruction
for the horizontal and vertical operators in SG III.13.6. It does not
identify smoothness in any chosen tensor bundle atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable (U : Type*) [AddCommGroup U] [Module ℂ U]
  {Y : Type*} {F : Y → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]

/-- Evaluate the original section factor in every actual fiber. -/
def tensorSectionEvaluation (X : Submodule ℂ (∀ y, F y)) :
    U ⊗[ℂ] X →ₗ[ℂ] ∀ y, U ⊗[ℂ] F y :=
  LinearMap.pi fun y ↦ ((LinearMap.proj y).comp X.subtype).lTensor U

/-- Evaluation retains the original pure tensor of a coefficient and section. -/
theorem tensorSectionEvaluation_tmul (X : Submodule ℂ (∀ y, F y)) (u : U) (s : X)
    (y : Y) : tensorSectionEvaluation U X (u ⊗ₜ[ℂ] s) y = u ⊗ₜ[ℂ] s.val y := rfl

/-- Finite tensor sections are uniquely reconstructed from their actual dual contractions. -/
theorem existsUnique_tensorSection_of_dual [FiniteDimensional ℂ U]
    (X : Submodule ℂ (∀ y, F y)) (w : ∀ y, U ⊗[ℂ] F y)
    (hw : ∀ l : U →ₗ[ℂ] ℂ,
      (fun y ↦ TensorProduct.lid ℂ (F y) (TensorProduct.map l LinearMap.id (w y))) ∈ X) :
    ∃! t : U ⊗[ℂ] X, tensorSectionEvaluation U X t = w := by
  classical
  let d := Module.finrank ℂ U
  let b : Module.Basis (Fin d) ℂ U := Module.finBasis ℂ U
  let eX : U ⊗[ℂ] X ≃ₗ[ℂ] (Fin d → X) :=
    (TensorProduct.congr b.equivFun (LinearEquiv.refl ℂ X)).trans
      ((TensorProduct.comm ℂ (Fin d → ℂ) X).trans
        (TensorProduct.piScalarRight ℂ ℂ X (Fin d)))
  let eF (y : Y) : U ⊗[ℂ] F y ≃ₗ[ℂ] (Fin d → F y) :=
    (TensorProduct.congr b.equivFun (LinearEquiv.refl ℂ (F y))).trans
      ((TensorProduct.comm ℂ (Fin d → ℂ) (F y)).trans
        (TensorProduct.piScalarRight ℂ ℂ (F y) (Fin d)))
  have heX (u : U) (v : X) (i : Fin d) :
      eX (u ⊗ₜ[ℂ] v) i = b.equivFun u i • v := by
    simp [eX]
  have heF (y : Y) (u : U) (v : F y) (i : Fin d) :
      eF y (u ⊗ₜ[ℂ] v) i = b.equivFun u i • v := by
    simp [eF]
  -- The same finite coordinates commute with evaluation into each original fiber.
  have heval (t : U ⊗[ℂ] X) (y : Y) (i : Fin d) :
      eF y (tensorSectionEvaluation U X t y) i = (eX t i).val y := by
    induction t using TensorProduct.inductionOn with
    | tmul u s => rw [tensorSectionEvaluation_tmul, heF, heX]; rfl
    | add a c ha hc =>
      simp only [map_add, Pi.add_apply] at *
      exact congrArg₂ (· + ·) ha hc
  have hcontract (y : Y) (t : U ⊗[ℂ] F y) (i : Fin d) :
      eF y t i = TensorProduct.lid ℂ (F y)
        (TensorProduct.map ((LinearMap.proj i).comp b.equivFun.toLinearMap) LinearMap.id t) := by
    induction t using TensorProduct.inductionOn with
    | tmul u v => simp only [heF, TensorProduct.map_tmul, LinearMap.comp_apply,
                            LinearMap.proj_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
                            TensorProduct.lid_tmul]
    | add a c ha hc => simp only [map_add, Pi.add_apply, ha, hc]
  let c (i : Fin d) : X := ⟨fun y ↦ eF y (w y) i, by
    have h := hw ((LinearMap.proj i).comp b.equivFun.toLinearMap)
    simpa only [hcontract] using h⟩
  let t := (eX).symm c
  refine ⟨t, ?_, ?_⟩
  · funext y
    apply (eF y).injective
    funext i
    rw [heval]
    change (eX ((eX).symm c) i).val y = _
    rw [(eX).apply_symm_apply]
  · intro t' ht'
    apply (eX).injective
    rw [show eX t = c from (eX).apply_symm_apply c]
    funext i
    apply Subtype.ext
    funext y
    rw [← heval, ht']

end AtiyahSinger
