/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyProperPullback
public import AtiyahSinger.Topology.ComplexBundleCompactSupportCharacter
public import AtiyahSinger.Topology.ReducedChernCharacterNaturality

/-!
# Proper naturality of the original bundle-supported Chern character

Public module ID: M1651.

The literal one-point comparison for each original complex total space detects
the naturality square. Proper pullback extends to the same one-point map in K
theory and relative cohomology; naturality of the original reduced character
then proves the result. The two bundles need not have the same rank or metric.

Source: naturality of the Chern character, SG III.11, on the specified support models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle OnePoint

universe u

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

/-- Proper maps between the actual bundle totals preserve their specified support characters. -/
theorem compactSupportChernCharacterComponent_pullback
    {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    {F : Y → Type u} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
    (r s : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r)
    (hs : ∀ y, Module.finrank ℂ (F y) = s)
    (f : C(TotalSpace Unit E, TotalSpace Unit F)) (hf : IsProperMap f)
    (a : CompactSupportKZero (TotalSpace Unit F)) (k : ℕ) :
    hE.compactSupportChernCharacterComponent r hr k (compactSupportKZeroPullback f hf a) =
      compactSupportCohomologyProperPullback ℚ f hf (2 * k)
        (hF.compactSupportChernCharacterComponent s hs k a) := by
  -- The actual comparison is bijective here by cofinal metric disks on each original bundle.
  apply (hE.compactSupportCohomologyToOnePoint_bijective ℚ r hr (2 * k)).injective
  rw [compactSupportChernCharacterComponent_toOnePoint,
    compactSupportCohomologyProperPullback_toOnePoint,
    compactSupportChernCharacterComponent_toOnePoint]
  -- Both sides use this same extension of f, with its original infinity point.
  exact (reducedChernCharacterComponent_pullback
    (∞ : OnePoint (TotalSpace Unit E)) (∞ : OnePoint (TotalSpace Unit F))
      (properOnePointMap f hf) rfl a k).symm

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
