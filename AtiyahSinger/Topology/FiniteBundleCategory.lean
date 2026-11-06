/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteBundle
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of finite-rank continuous complex bundles

Public module ID: M1848.

The objects are the existing `FiniteBundle X`, with their original total-space
topologies and locally finite, possibly varying ranks. Morphisms are the existing
continuous fiberwise complex-linear `Hom` maps, with their original identities
and composition. This category structure introduces no new bundle carrier.

Source: Karoubi, K-Theory, I.6.1 and I.6.17--6.18. Compactness and Hausdorffness
are needed for the Serre--Swan equivalence, not for this category structure.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The category structure on the existing finite-rank bundles and continuous bundle maps. -/
instance FiniteBundle.category : CategoryTheory.Category (FiniteBundle X) where
  Hom E F := ComplexBundle.Hom E.Fiber F.Fiber
  id E := Hom.id E.Fiber
  comp f g := g.comp f
  -- The category laws are the same pointwise function laws; continuity fields are proofs.
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end AtiyahSinger.ComplexBundle
