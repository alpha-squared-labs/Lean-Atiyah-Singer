/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.SuspendedKExcision

/-!
# The external product in two arbitrary nonpositive K-degrees

Public module ID: M1870.

SG Appendix C.1 uses the full graded external product. The existing suspension
model represents degree -m by compactly supported K-zero on X times real m-space.
Here the original degree-zero product is transported by the actual coordinate map
`((x,s),(y,t)) ↦ ((x,y), Fin.append s t)`. The first suspension block precedes
the second. The order is essential for the sign in graded commutativity.

Degree reindexing below only transports an equality of natural numbers. It does
not choose a Bott equivalence or permute any suspension coordinates. All bases
are locally compact Hausdorff; empty bases and zero suspension degrees are allowed.
The constructions retain the original compact-support groups and external product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Combine the two ordered real suspension blocks, retaining both base points. -/
def suspendedProductHomeomorph (m n : ℕ) (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] :
    ((X × (Fin m → ℝ)) × (Y × (Fin n → ℝ))) ≃ₜ
      ((X × Y) × (Fin (m + n) → ℝ)) :=
  (Homeomorph.prodProdProdComm X (Fin m → ℝ) Y (Fin n → ℝ)).trans
    ((Homeomorph.refl (X × Y)).prodCongr (Fin.appendHomeomorph m n))

/-- Reindex equal suspension degrees without a coordinate permutation or periodicity map. -/
def compactSupportKDegreeCongr (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] {m n : ℕ} (h : m = n) :
    CompactSupportK m X ≃+ CompactSupportK n X := by
  subst n
  exact AddEquiv.refl (CompactSupportK m X)

variable {X Y : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

/-- SG C.1: the original compact-support product with the first suspension block first. -/
def compactSupportKExternalProduct (m n : ℕ) :
    CompactSupportK m X →+ CompactSupportK n Y →+ CompactSupportK (m + n) (X × Y) :=
  compactSupportKZeroExternalProduct.compr₂
    (compactSupportKZeroHomeomorph (suspendedProductHomeomorph m n X Y))

end AtiyahSinger
