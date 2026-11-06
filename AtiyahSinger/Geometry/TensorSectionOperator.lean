/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FiniteTensorSections

/-!
# Finite tensor extension of an operator on actual sections

Public module ID: M1501.

A linear operator on two prescribed spaces of sections has a canonical
extension to finite tensor coefficients. Its domain consists of actual
tensor-valued sections whose every dual contraction belongs to the given
section space. Evaluation identifies this domain with the algebraic tensor
product; the extended operator commutes with every coefficient contraction.

For horizontal PDOs this retains the entire parameter fiber. Smoothness in
the original parameter atlas is an additional analytic assertion, proved
using the same operator's parameter regularity theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (U : Type*) [AddCommGroup U] [Module ℂ U]
  {M : Type*} {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]

/-- Actual tensor-valued sections detected by contraction into the prescribed section space. -/
def dualTensorSections (X : Submodule ℂ (∀ x, E x)) :
    Submodule ℂ (∀ x, U ⊗[ℂ] E x) where
  carrier := {w | ∀ l : U →ₗ[ℂ] ℂ,
    (fun x ↦ TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id (w x))) ∈ X}
  zero_mem' := by
    intro l
    convert X.zero_mem using 1
    funext x
    simp
  add_mem' := by
    intro w z hw hz l
    convert X.add_mem (hw l) (hz l) using 1
    funext x
    simp only [Pi.add_apply, map_add]
  smul_mem' := by
    intro c w hw l
    convert X.smul_mem c (hw l) using 1
    funext x
    simp only [Pi.smul_apply, map_smul]

variable [FiniteDimensional ℂ U]

/-- The canonical evaluation equivalence uses the original fibers and every dual contraction. -/
def tensorSectionEquiv (X : Submodule ℂ (∀ x, E x)) :
    U ⊗[ℂ] X ≃ₗ[ℂ] dualTensorSections U X := by
  classical
  -- Contraction before evaluation is the same original section as evaluation after contraction.
  have hcontract (t : U ⊗[ℂ] X) (l : U →ₗ[ℂ] ℂ) :
      (fun x ↦ TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id (tensorSectionEvaluation U X t x))) =
      (TensorProduct.lid ℂ X (TensorProduct.map l LinearMap.id t)).val := by
    induction t using TensorProduct.inductionOn with
    | tmul u s =>
      funext x
      simp only [tensorSectionEvaluation_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.lid_tmul]
      rfl
    | add a b ha hb =>
      funext x
      simpa only [map_add, Submodule.coe_add, Pi.add_apply] using
        congrArg₂ (· + ·) (congrFun ha x) (congrFun hb x)
  let e : U ⊗[ℂ] X →ₗ[ℂ] dualTensorSections U X :=
    (tensorSectionEvaluation U X).codRestrict (dualTensorSections U X) (by
      intro t l
      rw [hcontract]
      exact (TensorProduct.lid ℂ X (TensorProduct.map l LinearMap.id t)).property)
  apply LinearEquiv.ofBijective e
  constructor
  · intro a b hab
    have h := existsUnique_tensorSection_of_dual U X (e a).val (e a).property
    exact h.unique rfl (congrArg Subtype.val hab).symm
  · intro w
    obtain ⟨t, ht, _⟩ := existsUnique_tensorSection_of_dual U X w.val w.property
    exact ⟨t, Subtype.ext ht⟩

/-- The canonical equivalence evaluates the same original section factor at each point. -/
theorem tensorSectionEquiv_apply (X : Submodule ℂ (∀ x, E x)) (t : U ⊗[ℂ] X) :
    (tensorSectionEquiv U X t).val = tensorSectionEvaluation U X t := rfl

/-- Extend the actual section operator while leaving its finite coefficient factor unchanged. -/
def tensorSectionOperator (X : Submodule ℂ (∀ x, E x))
    (Y : Submodule ℂ (∀ x, F x)) (L : X →ₗ[ℂ] Y) :
    dualTensorSections U X →ₗ[ℂ] dualTensorSections U Y :=
  (tensorSectionEquiv U Y).toLinearMap.comp
    ((L.lTensor U).comp (tensorSectionEquiv U X).symm.toLinearMap)

/-- Every original dual contraction commutes with this same extended section operator. -/
theorem tensorSectionOperator_contract (X : Submodule ℂ (∀ x, E x))
    (Y : Submodule ℂ (∀ x, F x)) (L : X →ₗ[ℂ] Y)
    (w : dualTensorSections U X) (l : U →ₗ[ℂ] ℂ) :
    (fun x ↦ TensorProduct.lid ℂ (F x)
      (TensorProduct.map l LinearMap.id ((tensorSectionOperator U X Y L w).val x))) =
      (L ⟨fun x ↦ TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id (w.val x)), w.property l⟩).val := by
  classical
  -- Use the evaluation equivalence to reduce to finite tensors of unchanged original sections.
  obtain ⟨t, rfl⟩ := (tensorSectionEquiv U X).surjective w
  induction t using TensorProduct.inductionOn with
  | tmul u s =>
    have hout : tensorSectionOperator U X Y L (tensorSectionEquiv U X (u ⊗ₜ[ℂ] s)) =
        tensorSectionEquiv U Y (u ⊗ₜ[ℂ] L s) := by
      simp [tensorSectionOperator]
    rw [hout]
    have hin : (⟨fun x ↦ TensorProduct.lid ℂ (E x)
          (TensorProduct.map l LinearMap.id
            ((tensorSectionEquiv U X (u ⊗ₜ[ℂ] s)).val x)),
        (tensorSectionEquiv U X (u ⊗ₜ[ℂ] s)).property l⟩ : X) = l u • s := by
      apply Subtype.ext
      funext x
      change TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id (u ⊗ₜ[ℂ] s.val x)) = _
      simp
    rw [hin, map_smul]
    funext x
    change TensorProduct.lid ℂ (F x)
      (TensorProduct.map l LinearMap.id (u ⊗ₜ[ℂ] (L s).val x)) = _
    simp
  | add a b ha hb =>
    have hin : (⟨fun x ↦ TensorProduct.lid ℂ (E x)
          (TensorProduct.map l LinearMap.id
            ((tensorSectionEquiv U X (a + b)).val x)),
        (tensorSectionEquiv U X (a + b)).property l⟩ : X) =
        ⟨fun x ↦ TensorProduct.lid ℂ (E x)
            (TensorProduct.map l LinearMap.id ((tensorSectionEquiv U X a).val x)),
          (tensorSectionEquiv U X a).property l⟩ +
        ⟨fun x ↦ TensorProduct.lid ℂ (E x)
            (TensorProduct.map l LinearMap.id ((tensorSectionEquiv U X b).val x)),
          (tensorSectionEquiv U X b).property l⟩ := by
      apply Subtype.ext
      funext x
      simp only [map_add, Submodule.coe_add, Pi.add_apply]
    rw [hin, map_add]
    funext x
    simpa only [map_add, Submodule.coe_add, Pi.add_apply] using
      congrArg₂ (· + ·) (congrFun ha x) (congrFun hb x)

/-- A change of the finite coefficient space commutes with the unchanged section operator. -/
theorem tensorSectionOperator_naturality
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (X : Submodule ℂ (∀ x, E x)) (Y : Submodule ℂ (∀ x, F x)) (L : X →ₗ[ℂ] Y)
    (a : U →ₗ[ℂ] V) (w : dualTensorSections U X) (z : dualTensorSections V X)
    (hz : z.val = fun x ↦ TensorProduct.map a LinearMap.id (w.val x)) :
    (tensorSectionOperator V X Y L z).val =
      fun x ↦ TensorProduct.map a LinearMap.id
        ((tensorSectionOperator U X Y L w).val x) := by
  classical
  -- Evaluation is natural in the coefficient space before either operator is applied.
  have hevalX (t : U ⊗[ℂ] X) :
      (tensorSectionEquiv V X ((a.rTensor X) t)).val =
        fun x ↦ TensorProduct.map a LinearMap.id ((tensorSectionEquiv U X t).val x) := by
    simp only [tensorSectionEquiv_apply]
    induction t using TensorProduct.inductionOn with
    | tmul u s =>
      funext x
      simp only [LinearMap.rTensor_tmul, tensorSectionEvaluation_tmul,
        TensorProduct.map_tmul, LinearMap.id_apply]
    | add b c hb hc =>
      funext x
      simpa only [map_add, Pi.add_apply] using
        congrArg₂ (· + ·) (congrFun hb x) (congrFun hc x)
  have hevalY (t : U ⊗[ℂ] Y) :
      (tensorSectionEquiv V Y ((a.rTensor Y) t)).val =
        fun x ↦ TensorProduct.map a LinearMap.id ((tensorSectionEquiv U Y t).val x) := by
    simp only [tensorSectionEquiv_apply]
    induction t using TensorProduct.inductionOn with
    | tmul u s =>
      funext x
      simp only [LinearMap.rTensor_tmul, tensorSectionEvaluation_tmul,
        TensorProduct.map_tmul, LinearMap.id_apply]
    | add b c hb hc =>
      funext x
      simpa only [map_add, Pi.add_apply] using
        congrArg₂ (· + ·) (congrFun hb x) (congrFun hc x)
  obtain ⟨t, rfl⟩ := (tensorSectionEquiv U X).surjective w
  have hz' : z = tensorSectionEquiv V X ((a.rTensor X) t) :=
    Subtype.ext (hz.trans (hevalX t).symm)
  rw [hz']
  -- The two independent tensor factors commute by the standard tensor map identity.
  have hcomm : (L.lTensor V) ((a.rTensor X) t) =
      (a.rTensor Y) ((L.lTensor U) t) := by
    change ((L.lTensor V).comp (a.rTensor X)) t =
      ((a.rTensor Y).comp (L.lTensor U)) t
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hleft : tensorSectionOperator V X Y L
        (tensorSectionEquiv V X ((a.rTensor X) t)) =
      tensorSectionEquiv V Y ((L.lTensor V) ((a.rTensor X) t)) := by
    simp [tensorSectionOperator]
  have hright : tensorSectionOperator U X Y L (tensorSectionEquiv U X t) =
      tensorSectionEquiv U Y ((L.lTensor U) t) := by
    simp [tensorSectionOperator]
  rw [hleft, hright, hcomm]
  exact hevalY ((L.lTensor U) t)

end AtiyahSinger
