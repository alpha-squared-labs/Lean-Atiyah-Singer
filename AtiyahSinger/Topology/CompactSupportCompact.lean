/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality

/-!
# Compact-support K theory on a compact base

Public module ID: M1670.

The original restriction equivalence, separated from geometric Bott periodicity
to keep the product and its unit laws available to the Bott comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

/-- Compact-support K⁰ on a compact base, with its prescribed restriction map. -/
def compactSupportKZeroCompactEquiv (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] : CompactSupportKZero X ≃+ ComplexKZero X :=
  AddEquiv.ofBijective compactSupportKZeroToAbsolute
    compactSupportKZeroToAbsolute_bijective

end AtiyahSinger
