/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.EquivariantFiniteComplement
public import AtiyahSinger.Topology.EquivariantHermitianMetric
public import AtiyahSinger.Topology.EquivariantTrivialBundle
public import AtiyahSinger.Topology.FiniteBundle

/-!
# Finite representation complements of original equivariant bundles

Public module ID: M1765.

A finite-rank continuous equivariant bundle on a compact Hausdorff base is
an equivariant direct summand of a product bundle for a finite continuous
representation. The conclusion retains the original bundle and its action,
the existing product and sum topologies, and an actual equivariant bundle
isomorphism. The complementary bundle may have locally varying rank.

Karoubi I.9.31(d), with the compact-group extension in I.9.31(g), states this
equivariant finite-representation complement result after I.9.30's definition.
SG I.9.8--9.9 give the ordinary embedding/complement route; SG III.9 supplies
the compact-group setting and invariant-metric averaging.
The additional G-finite-section/Peter--Weyl input is substantive: averaging
an arbitrary injective bundle map need not preserve injectivity. The exercise
leaves its density argument implicit; the ordinary SG result alone is not
asserted to prove this equivariant complement theorem.

The theorem is entirely continuous. It constructs neither a smooth structure
on the original bundle nor smoothness of an arbitrary continuous group action.
No connectedness, constant global rank, positive rank or Lie-group hypothesis
is imposed. The proof below uses the compact unitary finite-vector theorem, the actual
regular L² orbit embedding, and the averaged finite projection splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology trivialTopology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [TopologicalSpace X] [hXC : CompactSpace X] [hXT : T2Space X]
  [MulAction G X] [ContinuousSMul G X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

include hGC hGT hXC hXT hE

/-- An original equivariant bundle has a complement in a finite representation bundle. -/
theorem EquivariantStructure.exists_finiteRepresentation_complement
    (σ : EquivariantStructure G E) :
    ∃ (F : FiniteBundle X) (τ : EquivariantStructure G F.Fiber)
      (ρ : FiniteContinuousRepresentation G),
      ∃ e : Iso (E ×ᵇ F.Fiber) (Bundle.Trivial X (Fin ρ.dimension → ℂ)),
        e.IsEquivariant (σ.sum τ) (EquivariantStructure.ofFiniteRepresentation ρ) := by
  -- Orbitize an ordinary finite embedding into the regular L² representation.
  -- Haar full support detects its original fibers; compact unit vectors and
  -- finite invariant approximation preserve injectivity over the whole base.
  obtain ⟨ρ, q, hq, heq⟩ := σ.exists_finiteRepresentation_embedding
  -- Split that same injection by an averaged projection. The complement is
  -- the actual image of 1-p, with restricted action and its existing topology.
  obtain ⟨F, τ, e, he⟩ := q.exists_equivariant_complement σ ρ hq heq
  exact ⟨F, τ, ρ, e, he⟩

end AtiyahSinger.ComplexBundle
