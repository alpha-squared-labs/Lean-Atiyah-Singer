/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationProductMap
public import AtiyahSinger.Topology.ThomTensorReassociation

/-!
# The native tensor comparison along real/imaginary coordinates

Public module ID: M1737.

This implementation adapter flattens the four original coefficient pullbacks
along the actual real/imaginary product map. Every fiber vector is retained.
The coefficient bundles are kept abstract to avoid re-elaborating associated
bundle constructions inside every tensor and sum comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum
  isFiniteRank_pullback

variable {X : Type*} [TopologicalSpace X] (V : Type*) [TopologicalSpace V]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace V E)] [FiberBundle V E]
  (H : ZMod 2 → X → Type*) [∀ i x, AddCommGroup (H i x)] [∀ i x, Module ℂ (H i x)]
  [∀ i, TopologicalSpace (TotalSpace Unit (H i))] [∀ i, IsFiniteRank (H i)]

set_option maxHeartbeats 900000 in
-- The four native factors are compared through three successive pullback topologies.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The real/imaginary restriction retains all four coefficient tensors as the same vectors. -/
theorem exists_complexificationTensorPullback_iso :
    let C := fun x ↦ ℂ ⊗[ℝ] E x
    letI := complexificationTopology V E
    let TE := TotalSpace V E
    let TC := TotalSpace Unit C
    let πE : C(TE, X) := ⟨π V E, FiberBundle.continuous_proj V E⟩
    let πC : C(TC, X) := ⟨π Unit C,
      (FiberBundle.continuous_proj V E).comp
        ((FiberBundle.Prod.isInducing_diag V E V E).continuous.fst.comp
          (complexificationDoubleTotalHomeomorph V E).continuous)⟩
    let A := πE *ᵖ (H 0)
    let F := πE *ᵖ (H 1)
    let p₁ : C(TE × TE, TE) := ContinuousMap.fst
    let p₂ : C(TE × TE, TE) := ContinuousMap.snd
    let Q : C(TC, TE × TE) := complexificationProductMap V E
    ∃ r₀ : Iso
        (Q *ᵖ fun z ↦ ((p₁ *ᵖ A) z ⊗[ℂ] (p₂ *ᵖ A) z) ×
          ((p₁ *ᵖ F) z ⊗[ℂ] (p₂ *ᵖ F) z))
        (πC *ᵖ fun x ↦ (H 0 x ⊗[ℂ] H 0 x) × (H 1 x ⊗[ℂ] H 1 x)),
      ∃ r₁ : Iso
          (Q *ᵖ fun z ↦ ((p₁ *ᵖ F) z ⊗[ℂ] (p₂ *ᵖ A) z) ×
            ((p₁ *ᵖ A) z ⊗[ℂ] (p₂ *ᵖ F) z))
          (πC *ᵖ fun x ↦ (H 1 x ⊗[ℂ] H 0 x) × (H 0 x ⊗[ℂ] H 1 x)),
        (∀ z v, r₀.linearEquiv z v = v) ∧ ∀ z v, r₁.linearEquiv z v = v := by
  let C := fun x ↦ ℂ ⊗[ℝ] E x
  let := complexificationTopology V E
  let TE := TotalSpace V E
  let TC := TotalSpace Unit C
  let πE : C(TE, X) := ⟨π V E, FiberBundle.continuous_proj V E⟩
  let πC : C(TC, X) := ⟨π Unit C,
    (FiberBundle.continuous_proj V E).comp
      ((FiberBundle.Prod.isInducing_diag V E V E).continuous.fst.comp
        (complexificationDoubleTotalHomeomorph V E).continuous)⟩
  let A := πE *ᵖ (H 0)
  let F := πE *ᵖ (H 1)
  dsimp only
  let p₁ : C(TE × TE, TE) := ContinuousMap.fst
  let p₂ : C(TE × TE, TE) := ContinuousMap.snd
  let Q : C(TC, TE × TE) := complexificationProductMap V E
  let (j : ZMod 2) : IsFiniteRank (πC *ᵖ (H j)) := isFiniteRank_pullback πC
  let (i j : ZMod 2) := isFiniteRank_tensor (E := H i) (F := H j)
  let i₁ (j : ZMod 2) : Iso (Q *ᵖ (p₁ *ᵖ (πE *ᵖ (H j)))) (πC *ᵖ (H j)) :=
    (pullbackCompIso (E := πE *ᵖ (H j)) p₁ Q).trans
      (pullbackCompIso (E := H j) πE (p₁.comp Q))
  let i₂ (j : ZMod 2) : Iso (Q *ᵖ (p₂ *ᵖ (πE *ᵖ (H j)))) (πC *ᵖ (H j)) :=
    (pullbackCompIso (E := πE *ᵖ (H j)) p₂ Q).trans
      (pullbackCompIso (E := H j) πE (p₂.comp Q))
  have hi₁ (j : ZMod 2) (z : TC) (v : H j z.proj) : (i₁ j).linearEquiv z v = v := by
    change (pullbackCompIso (E := H j) πE (p₁.comp Q)).linearEquiv z
      ((pullbackCompIso (E := πE *ᵖ (H j)) p₁ Q).linearEquiv z v) = v
    rw [pullbackCompIso_apply, pullbackCompIso_apply]
  have hi₂ (j : ZMod 2) (z : TC) (v : H j z.proj) : (i₂ j).linearEquiv z v = v := by
    change (pullbackCompIso (E := H j) πE (p₂.comp Q)).linearEquiv z
      ((pullbackCompIso (E := πE *ᵖ (H j)) p₂ Q).linearEquiv z v) = v
    rw [pullbackCompIso_apply, pullbackCompIso_apply]
  have htensor (i j : ZMod 2) (z : TC) (v : H i z.proj ⊗[ℂ] H j z.proj) :
      TensorProduct.congr ((i₁ i).linearEquiv z) ((i₂ j).linearEquiv z) v = v := by
    induction v using TensorProduct.inductionOn with
    | tmul u v => rw [TensorProduct.congr_tmul, hi₁, hi₂]
    | add u v hu hv => simp only [map_add, hu, hv]
  -- Flatten exactly the original iterated pullbacks on each of the four tensor factors.
  obtain ⟨s₀, hs₀⟩ := tensorSum_pullback_comparison
    (E := p₁ *ᵖ A) (F := p₂ *ᵖ A) (G := p₁ *ᵖ F) (H := p₂ *ᵖ F) Q
  obtain ⟨s₁, hs₁⟩ := tensorSum_pullback_comparison
    (E := p₁ *ᵖ F) (F := p₂ *ᵖ A) (G := p₁ *ᵖ A) (H := p₂ *ᵖ F) Q
  obtain ⟨t₀, ht₀⟩ := tensorSum_pullback_comparison
    (E := H 0) (F := H 0) (G := H 1) (H := H 1) πC
  obtain ⟨t₁, ht₁⟩ := tensorSum_pullback_comparison
    (E := H 1) (F := H 0) (G := H 0) (H := H 1) πC
  let r₀ := (s₀.symm.trans (((i₁ 0).tensor (i₂ 0)).sum ((i₁ 1).tensor (i₂ 1)))).trans t₀
  let r₁ := (s₁.symm.trans (((i₁ 1).tensor (i₂ 0)).sum ((i₁ 0).tensor (i₂ 1)))).trans t₁
  have hr₀ (z : TC) (v) : r₀.linearEquiv z v = v := by
    have hinv : (s₀.linearEquiv z).symm v = v := by
      apply (s₀.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, hs₀]
    change t₀.linearEquiv z
      (((i₁ 0).tensor (i₂ 0)).linearEquiv z ((s₀.linearEquiv z).symm v).1,
        ((i₁ 1).tensor (i₂ 1)).linearEquiv z ((s₀.linearEquiv z).symm v).2) = v
    rw [ht₀, hinv]
    change (TensorProduct.congr ((i₁ 0).linearEquiv z) ((i₂ 0).linearEquiv z) v.1,
      TensorProduct.congr ((i₁ 1).linearEquiv z) ((i₂ 1).linearEquiv z) v.2) = v
    rw [htensor, htensor]
    rfl
  have hr₁ (z : TC) (v) : r₁.linearEquiv z v = v := by
    have hinv : (s₁.linearEquiv z).symm v = v := by
      apply (s₁.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, hs₁]
    change t₁.linearEquiv z
      (((i₁ 1).tensor (i₂ 0)).linearEquiv z ((s₁.linearEquiv z).symm v).1,
        ((i₁ 0).tensor (i₂ 1)).linearEquiv z ((s₁.linearEquiv z).symm v).2) = v
    rw [ht₁, hinv]
    change (TensorProduct.congr ((i₁ 1).linearEquiv z) ((i₂ 0).linearEquiv z) v.1,
      TensorProduct.congr ((i₁ 0).linearEquiv z) ((i₂ 1).linearEquiv z) v.2) = v
    rw [htensor, htensor]
    rfl
  exact ⟨r₀, r₁, hr₀, hr₁⟩

end AtiyahSinger.ComplexBundle
