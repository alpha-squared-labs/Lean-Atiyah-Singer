/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportTriple

/-!
# Bundling the existing equivariant compact-support data

Public module ID: M1809.

The collection used for equivariant stable classes is a dependent pair of an
original support triple and its specified equivariant structure. The original
bundles, total topologies, compact control and boundary map are all retained.
Identity, enlargement, inverse and direct sum use those original operations.

This is the standard equivariant compact-support triple of ASI I §2 and the
equivariant version of SG I.9.23--9.26. Stabilization allows every
finite-rank equivariant bundle, not merely product representation bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable (G X : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The original finite-rank support triple together with its specified equivariant structure. -/
abbrev EquivariantSupportBundleTriple : Type _ :=
  Σ a : SupportBundleTriple X, SupportBundleTriple.EquivariantStructure G a

variable {G X}

namespace EquivariantSupportBundleTriple

/-- Package original boundary data and actions without changing any underlying object. -/
@[reducible]
def ofBoundary (E F : FiniteBundle X) (a : CompactSupportTriple E.Fiber F.Fiber)
    (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber)
    (ha : a.IsEquivariant ρE ρF) : EquivariantSupportBundleTriple G X :=
  ⟨SupportBundleTriple.ofBoundary E F a, ⟨ρE, ρF, ha⟩⟩

/-- The actual identity triple on any specified equivariant finite-rank bundle. -/
@[reducible]
def identity (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber) :
    EquivariantSupportBundleTriple G X :=
  ⟨SupportBundleTriple.identity E,
    { sourceAction := ρE
      targetAction := ρE
      isEquivariant :=
        { invariant_control := fun _ _ ↦ Iff.rfl
          boundary_intertwines := fun _ _ _ ↦ rfl } }⟩

/-- Enlarge only the compact control, retaining the original actions and boundary restriction. -/
@[reducible]
def enlarge (a : EquivariantSupportBundleTriple G X)
    (K : Set X) (hK : IsCompact K) (h : a.1.datum.control ⊆ K)
    (hInv : ∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K) :
    EquivariantSupportBundleTriple G X :=
  ⟨a.1.enlarge K hK h, a.2.enlarge K hK h hInv⟩

/-- Inverse uses the original inverse triple and exchanges its original two actions. -/
@[reducible]
def inverse (a : EquivariantSupportBundleTriple G X) :
    EquivariantSupportBundleTriple G X :=
  ⟨a.1.inverse, a.2.inverse⟩

/-- Direct sum uses the original sum triple, union control and componentwise actions. -/
@[reducible]
def sum (a b : EquivariantSupportBundleTriple G X) :
    EquivariantSupportBundleTriple G X :=
  ⟨a.1.sum b.1, a.2.sum b.2⟩

end EquivariantSupportBundleTriple

end AtiyahSinger.ComplexBundle
