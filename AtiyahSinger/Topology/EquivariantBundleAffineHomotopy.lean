/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoAffineHomotopy
public import AtiyahSinger.Topology.EquivariantSupportTriple

/-!
# Equivariant affine homotopies on a common compact exterior

Public module ID: M1764.

An invertible affine interpolation between two equivariant boundaries retains
the fixed source and target actions, since the group fixes the time parameter.
The original joint bundle isomorphism supplies inverse continuity on the whole
cylinder. One specified invariant compact control works for every time slice.
This is the equivariant supported comparison used after averaging a product
cutoff symbol; forgetting the action would not suffice for its representation index.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [hF : IsFiniteRank F]

attribute [local instance] isFiniteRank_restrict

include hE hF in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An invertible affine path outside one invariant compact set is an equivariant homotopy. -/
theorem CompactSupportTriple.equivariantlyHomotopic_of_affine
    (a b : CompactSupportTriple E F)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (hEA : a.IsEquivariant ρE ρF) (hEB : b.IsEquivariant ρE ρF)
    (K : Set X) (hK : IsCompact K)
    (hInv : ∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K)
    (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (h : ∀ (t : I) (x : (Kᶜ : Set X)), Function.Bijective
      ((1 - (t : ℂ)) • ((a.enlarge K hK ha).boundary.linearEquiv x).toLinearMap +
        (t : ℂ) • ((b.enlarge K hK hb).boundary.linearEquiv x).toLinearMap)) :
    a.EquivariantlyHomotopic b ρE ρF := by
  -- Use the existing affine isomorphism over the entire compact-parameter cylinder.
  obtain ⟨H, hH⟩ := (a.enlarge K hK ha).boundary.exists_affineHomotopy
    (b.enlarge K hK hb).boundary h
  have hA := hEA.enlarge K hK ha hInv
  have hB := hEB.enlarge K hK hb hInv
  refine ⟨{
    control := K
    isCompact_control := hK
    invariant_control := hInv
    left_control := ha
    right_control := hb
    homotopy := H
    intertwines := ?_ }⟩
  -- Both endpoints intertwine the same moving fibers; their scalar affine combination does too.
  intro t g x v
  rw [hH, hH, map_add, map_smul, map_smul,
    hA.boundary_intertwines, hB.boundary_intertwines]

end AtiyahSinger.ComplexBundle
