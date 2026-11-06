/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactSupportCharacterNaturality
public import AtiyahSinger.Topology.CompactSupportCohomologyProperFunctoriality

/-!
# The native real model of the original complex supported character

Public module ID: M1693.

The two supported characters use the same reduced Chern class and the same
one-point comparison. Their actual native total-space homeomorphism therefore
identifies them. This adapter keeps the original complex bundle, specified
Hermitian metric, support class, and fixed rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory OnePoint

universe u

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native real total-space character is the pullback of the original complex character. -/
theorem compactSupportChernCharacterComponent_native
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (r : ℕ)
    (hr : ∀ x, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
    let F := EuclideanSpace ℝ (Fin (2 * r))
    letI := nativeModelTopology E F
    letI := h.realNativeFiberBundle r hr
    letI := h.realNativeVectorBundle r hr
    letI := h.realNativeRiemannianBundle r hr
    let e := nativeModelTotalHomeomorph E F
    let f : C(TotalSpace F E, TotalSpace Unit E) := ⟨e, e.continuous⟩
    ∀ (a : CompactSupportKZero (TotalSpace Unit E)) (k : ℕ),
      bundleCompactSupportChernCharacterComponent (2 * r) E k
          (compactSupportKZeroPullback f e.isProperMap a) =
        compactSupportCohomologyHomeomorphPullback ℚ e (2 * k)
          (h.compactSupportChernCharacterComponent r hr k a) := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let F := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E F
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let e := nativeModelTotalHomeomorph E F
  let f : C(TotalSpace F E, TotalSpace Unit E) := ⟨e, e.continuous⟩
  dsimp only
  intro a k
  have hcharacter : bundleCompactSupportChernCharacterComponent (2 * r) E k
      (compactSupportKZeroPullback f e.isProperMap a) =
        compactSupportCohomologyProperPullback ℚ f e.isProperMap (2 * k)
          (h.compactSupportChernCharacterComponent r hr k a) := by
    -- This actual native bundle has the bijective one-point comparison.
    apply (compactSupportCohomologyToOnePoint_bundle_bijective ℚ (2 * r) E (2 * k)).injective
    rw [bundleCompactSupportChernCharacterComponent_toOnePoint,
      compactSupportCohomologyProperPullback_toOnePoint,
      h.compactSupportChernCharacterComponent_toOnePoint]
    exact (reducedChernCharacterComponent_pullback
      (∞ : OnePoint (TotalSpace F E)) (∞ : OnePoint (TotalSpace Unit E))
        (properOnePointMap f e.isProperMap) rfl a k).symm
  rw [hcharacter, compactSupportCohomologyProperPullback_homeomorph]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
