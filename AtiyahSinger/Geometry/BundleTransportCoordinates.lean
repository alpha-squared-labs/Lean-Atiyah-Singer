/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Continuous transport in one original bundle frame

Public module ID: M1116.

A fiberwise linear transport between two pullbacks, continuous in both native
total-space directions, has a continuous invertible coefficient family wherever
the two base maps lie in the same original frame. Its coordinate expression
retains the specified transport exactly. If that transport is vector identity
at a point, the coefficient is identity there as well.

This local-coordinate lemma is used for nested tubular maps. It introduces no
smoothness assumption on transport: smoothness belongs to the original frame
and the geometric maps in the subsequent factorization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Y → Type*} [∀ y, AddCommGroup (B y)] [∀ y, Module ℝ (B y)]
  [TopologicalSpace (TotalSpace F B)]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual bundle transport is a continuous invertible coefficient in the same original frame. -/
theorem exists_bundleTransport_coefficients (a b : C(X, Y))
    (R : ∀ x, B (a x) ≃ₗ[ℝ] B (b x))
    (hR : Continuous (fun z : TotalSpace F ((a : X → Y) *ᵖ B) ↦
      (⟨b z.proj, R z.proj z.snd⟩ : TotalSpace F B)))
    (hRi : Continuous (fun z : TotalSpace F ((b : X → Y) *ᵖ B) ↦
      (⟨a z.proj, (R z.proj).symm z.snd⟩ : TotalSpace F B)))
    (e : Trivialization F (π F B)) [e.IsLinear ℝ] :
    ∃ A : X → F ≃L[ℝ] F,
      ContinuousOn (fun p : X × F ↦ A p.1 p.2)
        ((a ⁻¹' e.baseSet ∩ b ⁻¹' e.baseSet) ×ˢ univ) ∧
      ContinuousOn (fun p : X × F ↦ (A p.1).symm p.2)
        ((a ⁻¹' e.baseSet ∩ b ⁻¹' e.baseSet) ×ˢ univ) ∧
      (∀ x, a x ∈ e.baseSet → b x ∈ e.baseSet → ∀ w : F,
        R x (e.symm (a x) w) = e.symm (b x) (A x w)) ∧
      (∀ x, a x ∈ e.baseSet → b x ∈ e.baseSet →
        (∀ v : B (a x), (⟨b x, R x v⟩ : TotalSpace F B) = ⟨a x, v⟩) →
          A x = ContinuousLinearEquiv.refl ℝ F) := by
  classical
  let S := a ⁻¹' e.baseSet ∩ b ⁻¹' e.baseSet
  let A (x : X) : F ≃L[ℝ] F :=
    if hx : x ∈ S then
      (((e.linearEquivAt ℝ (a x) hx.1).symm.trans (R x)).trans
        (e.linearEquivAt ℝ (b x) hx.2)).toContinuousLinearEquiv
    else ContinuousLinearEquiv.refl ℝ F
  have hA (x : X) (hx : x ∈ S) (w : F) :
      A x w = (e (⟨b x, R x (e.symm (a x) w)⟩ : TotalSpace F B)).2 := by
    dsimp only [A]
    rw [dite_eq_left hx]
    rfl
  have hAi (x : X) (hx : x ∈ S) (w : F) :
      (A x).symm w = (e (⟨a x, (R x).symm (e.symm (b x) w)⟩ : TotalSpace F B)).2 := by
    dsimp only [A]
    rw [dite_eq_left hx]
    rfl
  -- Use the original pullback topology to move through the chosen frame and transport.
  have hcoord (c d : C(X, Y)) (T : ∀ x, B (c x) ≃ₗ[ℝ] B (d x))
      (hT : Continuous (fun z : TotalSpace F ((c : X → Y) *ᵖ B) ↦
        (⟨d z.proj, T z.proj z.snd⟩ : TotalSpace F B))) :
      ContinuousOn (fun p : X × F ↦
        (e (⟨d p.1, T p.1 (e.symm (c p.1) p.2)⟩ : TotalSpace F B)).2)
        ((c ⁻¹' e.baseSet ∩ d ⁻¹' e.baseSet) ×ˢ univ) := by
    let L : X × F → TotalSpace F ((c : X → Y) *ᵖ B) :=
      fun p ↦ ⟨p.1, e.symm (c p.1) p.2⟩
    have hL : ContinuousOn L ((c ⁻¹' e.baseSet ∩ d ⁻¹' e.baseSet) ×ˢ univ) := by
      rw [(inducing_pullbackTotalSpaceEmbedding F B c).continuousOn_iff]
      exact continuous_fst.continuousOn.prodMk
        (e.continuousOn_symm.comp
          ((c.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun _ hp ↦ ⟨hp.1.1, mem_univ _⟩))
    exact (e.continuousOn.comp (hT.comp_continuousOn hL)
      (fun p hp ↦ e.mem_source.mpr hp.1.2)).snd
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · exact (hcoord a b R hR).congr (fun p hp ↦ hA p.1 hp.1 p.2)
  · apply ((hcoord b a (fun x ↦ (R x).symm) hRi).mono ?_).congr
      (fun p hp ↦ hAi p.1 hp.1 p.2)
    intro p hp
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · intro x ha hb w
    rw [hA x ⟨ha, hb⟩ w, e.symm_apply_apply_mk hb]
  · -- Exact identity in the native total space becomes exact identity in this same frame.
    intro x ha hb hzero
    apply ContinuousLinearEquiv.ext
    funext w
    rw [hA x ⟨ha, hb⟩ w, hzero, e.apply_mk_symm ha]
    rfl

end AtiyahSinger
