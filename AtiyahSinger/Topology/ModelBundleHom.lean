/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Joint Hom continuity and the original pullback bundle maps

Public module ID: M1959.

Continuity is measured in mathlib's Hom total space, then converted using its
continuous evaluation theorem and the actual induced pullback topologies.
Fiberwise bijectivity gives continuous inversion only after local finite rank.
No compactness, smoothness, or connectedness of the base is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {E : X → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]
  {F : X → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace W F)] [FiberBundle W F] [VectorBundle ℂ W F]

attribute [local instance] isFiniteRank_pullback

variable (f : C(Y, X)) (a : ∀ y, E (f y) →L[ℂ] F (f y))

/-- A continuous Hom section acts jointly continuously on the pulled-back total space. -/
theorem continuous_modelPullbackHom (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x)))) :
    letI := modelTopology V E
    letI := modelTopology W F
    Continuous (fun z : TotalSpace Unit ((f : Y → X) *ᵖ E) ↦
      (⟨z.proj, a z.proj z.snd⟩ : TotalSpace Unit ((f : Y → X) *ᵖ F))) := by
  /- The pullback topology tests the base and original total-space lift. The base is unchanged.
  Retype the source lift to the original modeled bundle and apply mathlib
  Continuous.clm_bundle_apply to the joint Hom section and the vector. Retype back for the
  target lift. This uses joint total-space continuity, not just fiberwise continuity. -/
  let := modelTopology V E
  let := modelTopology W F
  -- The target pullback tests the original base projection and total-space lift.
  rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
  refine (Pullback.continuous_proj Unit E f).prodMk ?_
  apply (continuous_modelTotal_iff W F _).mpr
  -- Joint Hom evaluation uses the exact original modeled vector and operator section.
  exact (ha.comp (Pullback.continuous_proj Unit E f)).clm_bundle_apply
    ((continuous_unitTotalEquiv V E).comp (Pullback.continuous_lift Unit E f))

/-- The actual continuous bundle map induced by the Hom section. -/
def modelPullbackHom (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x)))) :
    letI := modelTopology V E
    letI := modelTopology W F
    Hom ((f : Y → X) *ᵖ E) ((f : Y → X) *ᵖ F) :=
  letI := modelTopology V E
  letI := modelTopology W F
  { linearMap y := (a y).toLinearMap
    continuous_total := continuous_modelPullbackHom V W f a ha }

/-- The adapted map acts by the original continuous linear map. -/
theorem modelPullbackHom_apply (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x)))) (y : Y) (v : E (f y)) :
    letI := modelTopology V E
    letI := modelTopology W F
    (modelPullbackHom V W f a ha).linearMap y v = a y v := by
  /- Evaluate the fiber linear map used in the constructor. Forgetting continuity of a linear
  map changes only its certificate, and keeps every vector value. -/
  rfl

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- Invertibility yields the boundary isomorphism with the prescribed forward map. -/
def modelPullbackIso (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (hi : ∀ y, Function.Bijective (a y)) :
    letI := modelTopology V E
    letI := modelTopology W F
    letI := isFiniteRank_model V E
    letI := isFiniteRank_model W F
    Iso ((f : Y → X) *ᵖ E) ((f : Y → X) *ᵖ F) :=
  letI := modelTopology V E
  letI := modelTopology W F
  letI := isFiniteRank_model V E
  letI := isFiniteRank_model W F
  (modelPullbackHom V W f a ha).toIso hi

/-- The isomorphism retains the original Hom section. -/
theorem modelPullbackIso_apply (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (hi : ∀ y, Function.Bijective (a y)) (y : Y) (v : E (f y)) :
    letI := modelTopology V E
    letI := modelTopology W F
    letI := isFiniteRank_model V E
    letI := isFiniteRank_model W F
    (modelPullbackIso V W f a ha hi).linearEquiv y v = a y v := by
  /- The toIso constructor uses the given bijective fiber linear map as its forward function.
  Its inverse-continuity theorem does not introduce a new forward map. -/
  rfl

/-- The inverse actually inverts each original fiber map. -/
theorem modelPullbackIso_symm_apply (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (hi : ∀ y, Function.Bijective (a y)) (y : Y) (v : E (f y)) :
    letI := modelTopology V E
    letI := modelTopology W F
    letI := isFiniteRank_model V E
    letI := isFiniteRank_model W F
    (modelPullbackIso V W f a ha hi).symm.linearEquiv y (a y v) = v := by
  /- Replace the displayed application of a by the isomorphism forward map and use the inverse
  law in that same fiber. This retains the original source vector. -/
  let := modelTopology V E
  let := modelTopology W F
  let := isFiniteRank_model V E
  let := isFiniteRank_model W F
  exact ((modelPullbackIso V W f a ha hi).linearEquiv y).symm_apply_apply v

set_option linter.unusedSectionVars false in
/-- Equal fiber data induce equal bundle maps, independently of continuity proofs. -/
theorem modelPullbackHom_congr (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (b : ∀ y, E (f y) →L[ℂ] F (f y))
    (hb : Continuous (fun y ↦
      (⟨f y, b y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (hab : ∀ y, a y = b y) :
    letI := modelTopology V E
    letI := modelTopology W F
    modelPullbackHom V W f a ha = modelPullbackHom V W f b hb := by
  /- The exact action formulas and the assumed equality identify every fiber linear map. Bundle
  Hom extensionality removes the remaining proof fields. -/
  let := modelTopology V E
  let := modelTopology W F
  apply Hom.ext
  intro y
  exact congrArg ContinuousLinearMap.toLinearMap (hab y)

/-- Equal fiber data induce equal boundary isomorphisms. -/
theorem modelPullbackIso_congr (ha : Continuous (fun y ↦
      (⟨f y, a y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (hi : ∀ y, Function.Bijective (a y))
    (b : ∀ y, E (f y) →L[ℂ] F (f y))
    (hb : Continuous (fun y ↦
      (⟨f y, b y⟩ : TotalSpace (V →L[ℂ] W) (fun x ↦ E x →L[ℂ] F x))))
    (hj : ∀ y, Function.Bijective (b y)) (hab : ∀ y, a y = b y) :
    letI := modelTopology V E
    letI := modelTopology W F
    letI := isFiniteRank_model V E
    letI := isFiniteRank_model W F
    modelPullbackIso V W f a ha hi = modelPullbackIso V W f b hb hj := by
  /- The forward linear equivalences have equal values on every vector. Extensionality of
  linear equivalences and bundle isomorphisms identifies the structures; inverse maps are
  forced by the forward maps. -/
  let := modelTopology V E
  let := modelTopology W F
  let := isFiniteRank_model V E
  let := isFiniteRank_model W F
  apply Iso.ext
  intro y
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun L : E (f y) →L[ℂ] F (f y) ↦ L v) (hab y)

end AtiyahSinger.ComplexBundle
