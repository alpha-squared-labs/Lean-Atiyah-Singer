/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedVectorBundle

/-!
# Associated vector coordinates at a specified principal point

Public module ID: M1560.

Every point p in an original principal fiber gives linear coordinates on
the associated fiber by the actual representative map v -> [p,v]. The
following adapter packages the existing linearity and bijectivity results
as a linear equivalence, retaining that exact forward map. Its inverse
therefore computes vector coordinates relative to the same p.

No new fiber operations or representatives are chosen, and no continuity
of a globally chosen principal section is asserted. This standard coordinate
adapter is used to construct the global spin Clifford symbol from local
representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule

variable {G P B V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The original map `v ↦ [p,v]` as linear coordinates at the specified principal point. -/
def associatedVectorFiberMkLinearEquiv (hP : IsPrincipalBundle G projection)
    (ρ : ContRepresentation ℂ G V) (p : P) {b : B} (hp : projection p = b) :
    V ≃ₗ[ℂ] AssociatedVectorFiber hP ρ b :=
  LinearEquiv.ofBijective
    (IsLinearMap.mk' (associatedVectorFiberMk hP ρ p hp)
      (associatedVectorFiberMk_isLinear hP ρ p hp))
    (associatedVectorFiberMk_bijective hP ρ p hp)

end AtiyahSinger
