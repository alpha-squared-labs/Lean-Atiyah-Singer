/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Adjoint restriction to the full vertical kernels

Public module ID: M0774.

Three actual adjunction identities and the forward commuting square force the
reverse horizontal map to preserve the full adjoint vertical kernel. The
specified two kernel equivalences then determine its coefficient map, its
paired adjunction identity and its complete simultaneous kernel equivalence. This is
the algebraic part of the odd coefficient comparison in SG III.13. Neither a
reverse commuting square nor preservation of the vertical kernel is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X₀₀ X₁₀ X₀₁ X₁₁ C₀ C₁ : Type*}
  [AddCommGroup X₀₀] [Module ℂ X₀₀] [AddCommGroup X₁₀] [Module ℂ X₁₀]
  [AddCommGroup X₀₁] [Module ℂ X₀₁] [AddCommGroup X₁₁] [Module ℂ X₁₁]
  [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]

/-- Actual adjunctions restrict the reverse map to the specified full kernel coordinates. -/
theorem exists_adjoint_kernel_restriction
    (H₀ : X₀₀ →ₗ[ℂ] X₁₀) (H₁ : X₀₁ →ₗ[ℂ] X₁₁) (H₁a : X₁₁ →ₗ[ℂ] X₀₁)
    (V₀ : X₀₀ →ₗ[ℂ] X₀₁) (V₀a : X₀₁ →ₗ[ℂ] X₀₀)
    (V₁ : X₁₀ →ₗ[ℂ] X₁₁) (V₁a : X₁₁ →ₗ[ℂ] X₁₀)
    (p₀₀ : X₀₀ → X₀₀ → ℂ) (p₁₀ : X₁₀ → X₁₀ → ℂ)
    (p₀₁ : X₀₁ → X₀₁ → ℂ) (p₁₁ : X₁₁ → X₁₁ → ℂ)
    (hp₀₀ : ∀ x, (∀ u, p₀₀ u x = 0) → x = 0)
    (hp₁₀ : ∀ u, p₁₀ u 0 = 0)
    (hH₁ : ∀ u v, p₁₁ (H₁ u) v = p₀₁ u (H₁a v))
    (hV₀ : ∀ u v, p₀₁ (V₀ u) v = p₀₀ u (V₀a v))
    (hV₁ : ∀ u v, p₁₁ (V₁ u) v = p₁₀ u (V₁a v))
    (hcomm : ∀ u, H₁ (V₀ u) = V₁ (H₀ u))
    (Φ : C₀ ≃ₗ[ℂ] V₀a.ker) (Ψ : C₁ ≃ₗ[ℂ] V₁a.ker)
    (P : C₀ →ₗ[ℂ] C₁) (hP : ∀ u, H₁ (Φ u).val = (Ψ (P u)).val)
    (c₀ : C₀ → C₀ → ℂ) (c₁ : C₁ → C₁ → ℂ)
    (hΦ : ∀ u v, p₀₁ (Φ u).val (Φ v).val = c₀ u v)
    (hΨ : ∀ u v, p₁₁ (Ψ u).val (Ψ v).val = c₁ u v) :
    (∀ v ∈ V₁a.ker, H₁a v ∈ V₀a.ker) ∧
    ∃ R : C₁ →ₗ[ℂ] C₀,
      (∀ v, H₁a (Ψ v).val = (Φ (R v)).val) ∧
      (∀ u v, c₁ (P u) v = c₀ u (R v)) ∧
      ∃ κ : R.ker ≃ₗ[ℂ] ↥(H₁a.ker ⊓ V₁a.ker),
        ∀ v, (κ v).val = (Ψ v.val).val := by
  -- Test the reverse vertical image against every lower-left input.
  have hpres (v : X₁₁) (hv : v ∈ V₁a.ker) : H₁a v ∈ V₀a.ker := by
    change V₀a (H₁a v) = 0
    apply hp₀₀
    intro u
    calc
      p₀₀ u (V₀a (H₁a v)) = p₀₁ (V₀ u) (H₁a v) := (hV₀ u (H₁a v)).symm
      _ = p₁₁ (H₁ (V₀ u)) v := (hH₁ (V₀ u) v).symm
      _ = p₁₁ (V₁ (H₀ u)) v := by rw [hcomm]
      _ = p₁₀ (H₀ u) (V₁a v) := hV₁ (H₀ u) v
      _ = 0 := by rw [show V₁a v = 0 from hv, hp₁₀]
  -- Conjugate this genuine restriction by the two supplied full-kernel equivalences.
  let Hker : V₁a.ker →ₗ[ℂ] V₀a.ker :=
    (H₁a.comp V₁a.ker.subtype).codRestrict V₀a.ker (fun v ↦ hpres v.val v.property)
  let R : C₁ →ₗ[ℂ] C₀ := Φ.symm.toLinearMap.comp (Hker.comp Ψ.toLinearMap)
  have hR (v : C₁) : H₁a (Ψ v).val = (Φ (R v)).val := by
    exact (congrArg Subtype.val (Φ.apply_symm_apply (Hker (Ψ v)))).symm
  have hRadjoint (u : C₀) (v : C₁) : c₁ (P u) v = c₀ u (R v) := by
    calc
      c₁ (P u) v = p₁₁ (Ψ (P u)).val (Ψ v).val := (hΨ (P u) v).symm
      _ = p₁₁ (H₁ (Φ u).val) (Ψ v).val := by rw [hP]
      _ = p₀₁ (Φ u).val (H₁a (Ψ v).val) := hH₁ (Φ u).val (Ψ v).val
      _ = p₀₁ (Φ u).val (Φ (R v)).val := by rw [hR]
      _ = c₀ u (R v) := hΦ u (R v)
  -- The same evaluation, restricted once more, identifies the complete simultaneous kernel.
  let f : R.ker →ₗ[ℂ] ↥(H₁a.ker ⊓ V₁a.ker) := {
    toFun v := ⟨(Ψ v.val).val, by
      refine ⟨?_, (Ψ v.val).property⟩
      change H₁a (Ψ v.val).val = 0
      rw [hR, v.property, Φ.map_zero]
      rfl⟩
    map_add' u v := by
      apply Subtype.ext
      change (Ψ (u.val + v.val)).val = (Ψ u.val).val + (Ψ v.val).val
      rw [Ψ.map_add]
      rfl
    map_smul' a v := by
      apply Subtype.ext
      change (Ψ (a • v.val)).val = a • (Ψ v.val).val
      rw [Ψ.map_smul]
      rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply Ψ.injective
      apply Subtype.ext
      exact congrArg (fun w : ↥(H₁a.ker ⊓ V₁a.ker) ↦ w.val) huv
    · intro w
      let wV : V₁a.ker := ⟨w.val, w.property.2⟩
      let v : C₁ := Ψ.symm wV
      have hΨv : (Ψ v).val = w.val := congrArg Subtype.val (Ψ.apply_symm_apply wV)
      have hv : R v = 0 := by
        apply Φ.injective
        apply Subtype.ext
        change (Φ (R v)).val = (Φ 0).val
        rw [← hR, hΨv, Φ.map_zero]
        exact w.property.1
      exact ⟨⟨v, hv⟩, Subtype.ext hΨv⟩
  exact ⟨hpres, R, hR, hRadjoint, LinearEquiv.ofBijective f hf, fun _ ↦ rfl⟩

end AtiyahSinger
