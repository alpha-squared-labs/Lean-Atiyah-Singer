/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularSmallChainsHomotopy

/-!
# Open excision for the original relative singular chain map

Public module ID: M2093.

For an open embedding whose image contains a closed set, its range and the
complement of that closed set form an open cover. Contracting the actual
small-chain quotient gives a chain homotopy equivalence for the original map
of relative chain cokernels. The forward map remains the specified map of pairs.

This is singular excision as in Hatcher, section 2.1. No compactness or separation
assumption is added to the closed-set version used by local homology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Topology

universe u

/-- If f is an open embedding and K is closed and contained in its range, the original
relative chain map of (X, (f ⁻¹' K)ᶜ) → (Y, Kᶜ) is a chain homotopy equivalence. -/
theorem homotopyEquivalences_relativeSingularChainsMap_openEmbedding
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (K : Set Y) (hK : IsClosed K) (hKrange : K ⊆ Set.range f) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
      (relativeSingularChainsMap R f
        (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx ↦ hx)) := by
  -- These are the actual two open subspaces used by the small-chain comparison.
  have hOpen : ∀ U ∈ ({Kᶜ, Set.range f} : Set (Set Y)), IsOpen U := by
    intro U hU
    have hc : U = Kᶜ ∨ U = Set.range f := by simpa using hU
    rcases hc with hU | hU
    · rw [hU]
      exact hK.isOpen_compl
    · rw [hU]
      exact hf.isOpen_range
  have hCover : ⋃₀ ({Kᶜ, Set.range f} : Set (Set Y)) = Set.univ := by
    rw [Set.sUnion_pair]
    ext y
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      by_cases hy : y ∈ K
      · exact Or.inr (hKrange hy)
      · exact Or.inl hy
  -- The genuine small-chain contraction gives the inverse and both inverse homotopies.
  obtain ⟨h⟩ := contractible_cokernel_smallSingularChains R {Kᶜ, Set.range f} hOpen hCover
  exact homotopyEquivalences_relativeSingularChainsMap_preimage_of_smallChainContraction
    R f hf.toIsEmbedding Kᶜ h

end AtiyahSinger
