/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.ComplexificationBundle

/-!
# Pullback transport in the original real and imaginary coordinates

Public module ID: M1736.

A complex-linear transport between two pullbacks of an actual complexified real
bundle gives a real-linear transport between their native doubled pullbacks.
Both total maps are continuous, and their formula is precisely conjugation by
the original real/imaginary equivalences.

This comparison retains the original pullback and complexification topologies.
It is used to express a continuous tubular bundle transport in smooth native
normal frames; it does not assert that the transport itself is smooth.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (V : Type*) (B : Y → Type*) [∀ y, AddCommGroup (B y)] [∀ y, Module ℝ (B y)]
  [TopologicalSpace (TotalSpace V B)]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original complex pullback transport is continuous in both native real-double directions. -/
theorem exists_realDoublePullback_transport (a b : C(X, Y)) :
    letI := complexificationTopology V B
    ∀ e : Iso ((a : X → Y) *ᵖ (fun y ↦ ℂ ⊗[ℝ] B y))
        ((b : X → Y) *ᵖ (fun y ↦ ℂ ⊗[ℝ] B y)),
      ∃ R : ∀ x, (B (a x) × B (a x)) ≃ₗ[ℝ] (B (b x) × B (b x)),
        (∀ x w, R x w = complexificationReIm (B (b x))
          (e.linearEquiv x ((complexificationReIm (B (a x))).symm w))) ∧
        Continuous (fun z : TotalSpace (V × V) ((a : X → Y) *ᵖ (B ×ᵇ B)) ↦
          (⟨z.proj, R z.proj z.snd⟩ : TotalSpace (V × V) ((b : X → Y) *ᵖ (B ×ᵇ B)))) ∧
        Continuous (fun z : TotalSpace (V × V) ((b : X → Y) *ᵖ (B ×ᵇ B)) ↦
          (⟨z.proj, (R z.proj).symm z.snd⟩ :
            TotalSpace (V × V) ((a : X → Y) *ᵖ (B ×ᵇ B)))) := by
  let := complexificationTopology V B
  intro e
  let C : Y → Type _ := fun y ↦ ℂ ⊗[ℝ] B y
  let H := complexificationDoubleTotalHomeomorph V B
  -- Pull back the same base-preserving real/imaginary homeomorphism at both endpoints.
  let P (a : C(X, Y)) : TotalSpace Unit ((a : X → Y) *ᵖ C) ≃ₜ
      TotalSpace (V × V) ((a : X → Y) *ᵖ (B ×ᵇ B)) :=
    { toFun z := ⟨z.proj, complexificationReIm (B (a z.proj)) z.snd⟩
      invFun z := ⟨z.proj, (complexificationReIm (B (a z.proj))).symm z.snd⟩
      left_inv z := by
        cases z
        simp
      right_inv z := by
        cases z
        simp
      continuous_toFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding (V × V) (B ×ᵇ B) a).continuous_iff]
        exact (_root_.Pullback.continuous_proj Unit C a).prodMk
          (H.continuous.comp (_root_.Pullback.continuous_lift Unit C a))
      continuous_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit C a).continuous_iff]
        exact (_root_.Pullback.continuous_proj (V × V) (B ×ᵇ B) a).prodMk
          (H.symm.continuous.comp (_root_.Pullback.continuous_lift (V × V) (B ×ᵇ B) a)) }
  let R (x : X) : (B (a x) × B (a x)) ≃ₗ[ℝ] (B (b x) × B (b x)) :=
    (complexificationReIm (B (a x))).symm.trans
      (((e.linearEquiv x).restrictScalars ℝ).trans (complexificationReIm (B (b x))))
  refine ⟨R, fun _ _ ↦ rfl, ?_, ?_⟩
  · exact (P b).continuous.comp (e.totalHomeomorph.continuous.comp (P a).symm.continuous)
  · exact (P a).continuous.comp (e.totalHomeomorph.symm.continuous.comp (P b).symm.continuous)

end AtiyahSinger.ComplexBundle
