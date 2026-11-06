/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRingRestriction

/-!
# External products for two independent representation groups

Public module ID: M0052.

Inflate each original finite representation along its own product projection,
then use the already specified tensor product in the representation ring of
the product group. The resulting operation is additive in both virtual
representation classes. It retains the complete independent action
`(g, h) (v tensor w) = (g v) tensor (h w)` on the original tensor coordinates.

Sources: ASI I sections 4 and 9, printed pp.504--505 and 526--529, use this
external representation product in the equivariant multiplicative property.
The projection-restriction description is the standard explicit construction,
not a separately numbered theorem in those passages. No compactness, Lie
structure, unitary metric or irreducible decomposition is required here.
The generator formula follows from these specified restriction and tensor maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Inflate the two classes along their own projections and tensor their independent actions. -/
def representationExternalProduct :
    RepresentationGrothendieckGroup G →+
      RepresentationGrothendieckGroup H →+ RepresentationGrothendieckGroup (G × H) := by
  let rG := representationRestrictionRingHom (ContinuousMonoidHom.fst G H)
  let rH := representationRestrictionRingHom (ContinuousMonoidHom.snd G H)
  exact
    { toFun := fun a ↦
        { toFun := fun b ↦ rG a * rH b
          map_zero' := by rw [map_zero, mul_zero]
          map_add' := by
            intro b c
            rw [map_add, mul_add] }
      map_zero' := by
        apply AddMonoidHom.ext
        intro b
        change rG 0 * rH b = 0
        rw [map_zero, zero_mul]
      map_add' := by
        intro a b
        apply AddMonoidHom.ext
        intro c
        change rG (a + b) * rH c = rG a * rH c + rG b * rH c
        rw [map_add, add_mul] }

/-- Finite generators give the actual tensor of the two independently inflated actions. -/
theorem representationExternalProduct_finiteClass
    (ρ : FiniteContinuousRepresentation G) (σ : FiniteContinuousRepresentation H) :
    representationExternalProduct (finiteRepresentationClass ρ) (finiteRepresentationClass σ) =
      finiteRepresentationClass
        ((ρ.restrict (ContinuousMonoidHom.fst G H)).tensor
          (σ.restrict (ContinuousMonoidHom.snd G H))) := by
  /- Stage 1: the two existing restriction generator equations identify the
  inflated classes with the original finite actions precomposed by fst and
  snd. Their carriers, joint continuity and dimensions remain unchanged.
  Stage 2: apply representationMul_finiteClass to these very two restricted
  representations. The specified tensorCoordinates identifies an original
  pure tensor with the action rho(g)v tensor sigma(h)w at (g,h). Thus the
  right side retains both independent actions, not only their dimensions.
  The definition above extends precisely this product biadditively to the
  original Grothendieck groups; it imposes no new quotient relation. -/
  -- Unfold the two ring wrappers to the same original additive restriction maps.
  change representationMul (G × H)
    (representationRestriction (ContinuousMonoidHom.fst G H) (finiteRepresentationClass ρ))
    (representationRestriction (ContinuousMonoidHom.snd G H) (finiteRepresentationClass σ)) = _
  rw [representationRestriction_finiteClass, representationRestriction_finiteClass,
    representationMul_finiteClass]

end AtiyahSinger
