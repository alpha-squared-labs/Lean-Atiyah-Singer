/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ReducedChernCharacter
public import AtiyahSinger.Topology.RelativeSingularFunctoriality

/-!
# Naturality of the original point-relative Chern character

Public module ID: M2051.

The split point inclusion detects equality of its relative classes. Naturality
of the original absolute Chern character therefore identifies the point-relative
pullback of its unique reduced lift with the lift of the actual reduced K pullback.
This is used for proper maps on the original one-point compactifications.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

/-- A pointed map preserves the original point-relative Chern-character components. -/
theorem reducedChernCharacterComponent_pullback
    {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)
    (a : reducedComplexKZero y₀) (k : ℕ) :
    relativeSingularCohomologyPullback ℚ f
        (show Set.MapsTo f ({x₀} : Set X) ({y₀} : Set Y) from
          fun _ hx ↦ hx ▸ hf) (2 * k) (reducedChernCharacterComponent y₀ k a) =
      reducedChernCharacterComponent x₀ k (reducedComplexKZeroPullback x₀ y₀ f hf a) := by
  -- The same split point-relative comparison detects equality after ordinary restriction.
  apply (pointRelativeCohomologyToReduced_bijective ℚ x₀ (2 * k)).injective
  apply Subtype.ext
  change relativeSingularCohomologyToOrdinary ℚ ({x₀} : Set X) (2 * k)
      (relativeSingularCohomologyPullback ℚ f _ (2 * k)
        (reducedChernCharacterComponent y₀ k a)) =
    relativeSingularCohomologyToOrdinary ℚ ({x₀} : Set X) (2 * k)
      (reducedChernCharacterComponent x₀ k (reducedComplexKZeroPullback x₀ y₀ f hf a))
  have hsquare := relativeSingularCohomologyPullback_toOrdinary ℚ f
    (show Set.MapsTo f ({x₀} : Set X) ({y₀} : Set Y) from
      fun _ hx ↦ hx ▸ hf) (2 * k)
  have h := congrArg (fun g ↦ g (reducedChernCharacterComponent y₀ k a)) hsquare
  change relativeSingularCohomologyToOrdinary ℚ ({x₀} : Set X) (2 * k)
      (relativeSingularCohomologyPullback ℚ f _ (2 * k)
        (reducedChernCharacterComponent y₀ k a)) =
    singularCohomologyPullback ℚ f (2 * k)
      (relativeSingularCohomologyToOrdinary ℚ ({y₀} : Set Y) (2 * k)
        (reducedChernCharacterComponent y₀ k a)) at h
  -- Absolute naturality retains the actual ring-induced K pullback, including degree zero.
  rw [h, reducedChernCharacterComponent_toOrdinary, reducedChernCharacterComponent_toOrdinary]
  exact (chernCharacterKZeroComponent_pullback f a.val k).symm

end AtiyahSinger
