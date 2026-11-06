/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TensorSectionOperator
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Formal adjoints under finite tensor coefficients

Public module ID: M1035.

The canonical finite tensor extension of two adjoint section operators is
adjoint for the original tensor pairings. The proof uses finite tensors of
actual sections, the specified pure-tensor pairing identities, and actual
integrability of the original section pairings. It imposes no norm on the
section space and makes no closure or Sobolev-domain assertion.

For associated sphere operators this supplies the fiberwise adjunction step.
Descent of metrics and densities and their global integration remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped TensorProduct

variable (U : Type*) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  {M : Type*} [MeasurableSpace M] {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite tensor extension preserves the exact original integral adjunction. -/
theorem tensorSectionOperator_integral_adjoint
    (X : Submodule ℂ (∀ x, E x)) (Y : Submodule ℂ (∀ x, F x))
    (L : X →ₗ[ℂ] Y) (J : Y →ₗ[ℂ] X) (μ : Measure M)
    (hU : InnerProductSpace.Core ℂ U)
    (hE : ∀ x, InnerProductSpace.Core ℂ (E x))
    (hF : ∀ x, InnerProductSpace.Core ℂ (F x))
    (hUE : ∀ x, InnerProductSpace.Core ℂ (U ⊗[ℂ] E x))
    (hUF : ∀ x, InnerProductSpace.Core ℂ (U ⊗[ℂ] F x))
    (hpairE : ∀ x (u v : U) (s t : E x),
      (hUE x).inner (u ⊗ₜ[ℂ] s) (v ⊗ₜ[ℂ] t) = hU.inner u v * (hE x).inner s t)
    (hpairF : ∀ x (u v : U) (s t : F x),
      (hUF x).inner (u ⊗ₜ[ℂ] s) (v ⊗ₜ[ℂ] t) = hU.inner u v * (hF x).inner s t)
    (hIntE : ∀ s t : X, Integrable (fun x ↦ (hE x).inner (s.val x) (t.val x)) μ)
    (hIntF : ∀ s t : Y, Integrable (fun x ↦ (hF x).inner (s.val x) (t.val x)) μ)
    (hAdj : ∀ (s : X) (t : Y),
      (∫ x, (hF x).inner ((L s).val x) (t.val x) ∂μ) =
        ∫ x, (hE x).inner (s.val x) ((J t).val x) ∂μ)
    (s : dualTensorSections U X) (t : dualTensorSections U Y) :
    (∫ x, (hUF x).inner ((tensorSectionOperator U X Y L s).val x) (t.val x) ∂μ) =
      ∫ x, (hUE x).inner (s.val x) ((tensorSectionOperator U Y X J t).val x) ∂μ := by
  have hEaddLeft (x : M) (u v w : U ⊗[ℂ] E x) :
      (hUE x).inner (u + v) w = (hUE x).inner u w + (hUE x).inner v w :=
    (hUE x).add_left u v w
  have hFaddLeft (x : M) (u v w : U ⊗[ℂ] F x) :
      (hUF x).inner (u + v) w = (hUF x).inner u w + (hUF x).inner v w :=
    (hUF x).add_left u v w
  have hEaddRight (x : M) (u v w : U ⊗[ℂ] E x) :
      (hUE x).inner u (v + w) = (hUE x).inner u v + (hUE x).inner u w := by
    let := hUE x
    exact InnerProductSpace.Core.inner_add_right u v w
  have hFaddRight (x : M) (u v w : U ⊗[ℂ] F x) :
      (hUF x).inner u (v + w) = (hUF x).inner u v + (hUF x).inner u w := by
    let := hUF x
    exact InnerProductSpace.Core.inner_add_right u v w
  -- Actual pairings of all finite tensors are integrable by their original section factors.
  have hiE (s t : U ⊗[ℂ] X) : Integrable (fun x ↦ (hUE x).inner
      (tensorSectionEvaluation U X s x) (tensorSectionEvaluation U X t x)) μ := by
    induction s using TensorProduct.inductionOn with
    | tmul u s =>
      induction t using TensorProduct.inductionOn with
      | tmul v t =>
        simpa only [tensorSectionEvaluation_tmul, hpairE] using (hIntE s t).const_mul (hU.inner u v)
      | add a b ha hb =>
        simpa only [map_add, Pi.add_apply, Pi.add_def, hEaddRight] using ha.add hb
    | add a b ha hb =>
      simpa only [map_add, Pi.add_apply, Pi.add_def, hEaddLeft] using ha.add hb
  have hiF (s t : U ⊗[ℂ] Y) : Integrable (fun x ↦ (hUF x).inner
      (tensorSectionEvaluation U Y s x) (tensorSectionEvaluation U Y t x)) μ := by
    induction s using TensorProduct.inductionOn with
    | tmul u s =>
      induction t using TensorProduct.inductionOn with
      | tmul v t =>
        simpa only [tensorSectionEvaluation_tmul, hpairF] using (hIntF s t).const_mul (hU.inner u v)
      | add a b ha hb =>
        simpa only [map_add, Pi.add_apply, Pi.add_def, hFaddRight] using ha.add hb
    | add a b ha hb =>
      simpa only [map_add, Pi.add_apply, Pi.add_def, hFaddLeft] using ha.add hb
  -- On pure tensors the original adjunction is multiplied by the same coefficient pairing.
  have hadj (s : U ⊗[ℂ] X) (t : U ⊗[ℂ] Y) :
      (∫ x, (hUF x).inner (tensorSectionEvaluation U Y ((L.lTensor U) s) x)
        (tensorSectionEvaluation U Y t x) ∂μ) =
      ∫ x, (hUE x).inner (tensorSectionEvaluation U X s x)
        (tensorSectionEvaluation U X ((J.lTensor U) t) x) ∂μ := by
    induction s using TensorProduct.inductionOn with
    | tmul u s =>
      induction t using TensorProduct.inductionOn with
      | tmul v t =>
        simp only [LinearMap.lTensor_tmul, tensorSectionEvaluation_tmul, hpairE, hpairF,
          integral_const_mul, hAdj]
      | add a b ha hb =>
        simp only [map_add, Pi.add_apply, hEaddRight, hFaddRight]
        rw [integral_add (hiF ((L.lTensor U) (u ⊗ₜ[ℂ] s)) a)
          (hiF ((L.lTensor U) (u ⊗ₜ[ℂ] s)) b),
          integral_add (hiE (u ⊗ₜ[ℂ] s) ((J.lTensor U) a))
            (hiE (u ⊗ₜ[ℂ] s) ((J.lTensor U) b)), ha, hb]
    | add a b ha hb =>
      simp only [map_add, Pi.add_apply, hEaddLeft, hFaddLeft]
      rw [integral_add (hiF ((L.lTensor U) a) t) (hiF ((L.lTensor U) b) t),
        integral_add (hiE a ((J.lTensor U) t)) (hiE b ((J.lTensor U) t)), ha, hb]
  -- Canonical reconstruction identifies finite tensors with the prescribed tensor sections.
  obtain ⟨s, rfl⟩ := (tensorSectionEquiv U X).surjective s
  obtain ⟨t, rfl⟩ := (tensorSectionEquiv U Y).surjective t
  simpa only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, tensorSectionEquiv_apply] using hadj s t

end AtiyahSinger
