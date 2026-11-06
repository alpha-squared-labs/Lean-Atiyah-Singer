/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyProperPullback

/-!
# Forgetting supports commutes with actual proper pullback

Public module ID: M1660.

The equality is proved on the same original relative representative and its
literal inverse compact support. No injectivity of the forgetful map is assumed.
This square is used to compare the native and original zero-section formulas.

Source: naturality of singular cohomology of pairs and the compact-support colimit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- Forgetting support preserves pullback along the same proper continuous map. -/
theorem compactSupportCohomologyProperPullback_toOrdinary
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (n : ℕ) (a : compactSupportCohomology R Y n) :
    compactSupportCohomologyToOrdinary R X n
        (compactSupportCohomologyProperPullback R f hf n a) =
      singularCohomologyPullback R f n (compactSupportCohomologyToOrdinary R Y n a) := by
  have hforget {Z : Type u} [TopologicalSpace Z] (K : Compacts Z)
      (b : relativeSingularCohomology R (K : Set Z)ᶜ n) :
      compactSupportCohomologyToOrdinary R Z n (compactSupportCohomologyClass R Z K n b) =
        relativeSingularCohomologyToOrdinary R (K : Set Z)ᶜ n b := by
    have h : compactSupportCohomologyClass R Z K n ≫ compactSupportCohomologyToOrdinary R Z n =
        relativeSingularCohomologyToOrdinary R (K : Set Z)ᶜ n := colimit.ι_desc _ K
    exact congrArg (fun t ↦ t b) h
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R Y n a
  rw [compactSupportCohomologyProperPullback_representative, hforget, hforget]
  exact congrArg (fun t ↦ t b) (relativeSingularCohomologyPullback_toOrdinary R f
    (show Set.MapsTo f (properCompactPreimage f hf K : Set X)ᶜ (K : Set Y)ᶜ from
      fun _ hx ↦ hx) n)

end AtiyahSinger
