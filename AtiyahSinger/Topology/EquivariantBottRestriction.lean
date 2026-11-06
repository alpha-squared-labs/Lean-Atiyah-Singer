/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import AtiyahSinger.Topology.EquivariantRepresentationNaturality

/-!
# Restriction of the actual equivariant exterior Bott construction

Public module ID: M1760.

AB01/AL01: precomposing a unitary representation by a continuous homomorphism
restricts the same exterior Bott class. Both sides retain the original vector
space, Hermitian metric, even and odd exterior bundles, singleton zero control,
and wedge-minus-contraction boundary. The restricted action is the native
`DistribMulAction.compHom`; its underlying action is precisely the existing
support restriction's `MulAction.compHom`, not a separately selected action.

The forward Bott maps form the corresponding square with the original
representation-ring restriction. This uses its already established semilinear
compatibility with the representation action on the support group. Neither
group needs to be compact or Lie: these are compatibility statements for the
explicit forward maps, not an invocation of equivariant Bott bijectivity.

Sources: Atiyah--Singer I, section 2, pp.494--496, supplies the equivariant
K-theory and Bott framework. The displayed same-model restriction diagrams
are the standard functorial expansion for the existing SG exterior
triple. They do not resolve the independent equivariant Bott inverse or the
source's dual-carrier normalization, and no index theorem is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle

set_option maxSynthPendingDepth 25

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]
  (hunitary : ∀ (g : G) (u v : V), inner ℂ (g • u) (g • v) = inner ℂ u v)

/-- Restriction preserves the actual exterior Bott class with the same zero control and boundary. -/
theorem equivariantExteriorBottClass_restrict (φ : H →ₜ* G) :
    letI : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
    letI : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
    letI : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ (equivariantExteriorBottClass hunitary) =
      equivariantExteriorBottClass (G := H) (V := V)
        (fun h u v ↦ hunitary (φ h) u v) := by
  /- Restriction keeps the original exterior triple, its finite-dimensional
  topologies, zero control and wedge-minus-contraction boundary. It only
  precomposes each parity action by phi. The native restricted linear
  action induces exactly these same exterior maps, and the unitary
  certificate is the original one evaluated at phi(h). Apply the
  restriction-on-generators formula; the resulting generator is
  definitionally the displayed restricted exterior Bott triple. -/
  let : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
  let : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
  -- Restriction keeps the same generator and only precomposes its two parity actions.
  change equivariantSupportTripleKZeroRestrict φ
      (equivariantExteriorBottTriple hunitary).kZeroClass = _
  rw [equivariantSupportTripleKZeroRestrict_apply]
  rfl

/-- The actual forward Bott map commutes with the existing representation
and support restrictions. -/
theorem equivariantBottLinearMap_restrict (φ : H →ₜ* G)
    (r : RepresentationGrothendieckGroup G) :
    letI : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
    letI : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
    letI : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ (equivariantBottLinearMap hunitary r) =
      equivariantBottLinearMap (G := H) (V := V)
        (fun h u v ↦ hunitary (φ h) u v) (representationRestrictionRingHom φ r) := by
  /- Stage 1: the original forward Bott map sends r to r times the specified
  exterior Bott class. Apply the established semilinearity of the same support
  restriction for the existing representationRestrictionRingHom. Its coefficient
  is the actual restricted representation class, not an integer dimension.
  Stage 2: the preceding same-triple theorem identifies the restricted Bott
  generator with the original exterior construction for the native restricted
  action. The result is exactly the target forward Bott map on the restricted
  coefficient. Both routes retain the same metric, support control and boundary.
  No inverse Bott map, compactness, Lie atlas, or index normalization is needed. -/
  let : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
  let : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
  -- The coefficient action uses exactly the original representation restriction.
  change equivariantSupportTripleKZeroRestrict φ
      (r • equivariantExteriorBottClass hunitary) = _
  rw [equivariantSupportTripleKZeroRestrict_smul,
    equivariantExteriorBottClass_restrict]
  rfl

end AtiyahSinger
