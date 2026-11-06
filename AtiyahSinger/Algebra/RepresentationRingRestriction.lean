/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRestriction
public import AtiyahSinger.Algebra.RepresentationRing

/-!
# Ring compatibility of the original representation restriction

Public module ID: M0056.

The already defined additive restriction preserves the genuine tensor product
and the trivial-line unit. Package this same map as a ring homomorphism on
the original representation Grothendieck groups. No second restriction map,
new quotient relation or replacement additive group is introduced.

SG III.9, printed pp.211--212, supplies the representation-ring tensor product.
Restriction compatibility is the standard direct-precomposition supplement:
both tensor factors are evaluated at the same image group element. No
compactness, unitary structure or irreducible decomposition is required.
The proof retains the specified precomposition, tensor coordinates, and unit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger


set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The original additive restriction preserves the actual tensor product and trivial unit. -/
theorem representationRestriction_multiplicative (φ : H →ₜ* G) :
    (∀ a b : RepresentationGrothendieckGroup G,
      representationRestriction φ (a * b) =
        representationRestriction φ a * representationRestriction φ b) ∧
    representationRestriction φ 1 = 1 := by
  /- Stage 1: restriction of the tensor of finite representations is
  definitionally the tensor of their restrictions. Both constructions use
  the same finite coordinates and act at h by ρ(phi(h)) tensor σ(phi(h)).
  Stage 2: use representationRestriction_finiteClass and
  representationMul_finiteClass to obtain multiplicativity on a pair of
  original generator classes. Both sides are additive in each argument.
  These classes generate the existing additive quotient, so the equality
  extends first in one argument and then in the other to virtual classes.
  This uses neither equality of dimensions as a substitute for isomorphism
  nor any extra exact-sequence relation or decomposition into irreducibles.
  Stage 3: the same one-dimensional trivial action remains trivial after
  precomposition by φ. Its finite class is exactly the ring's specified one,
  so the existing generator restriction formula gives preservation of one.
  These two laws certify the same additive map for the ring wrapper below. -/
  -- The original tensor coordinates are unchanged; only the group argument is precomposed.
  have htensor (ρ σ : FiniteContinuousRepresentation G) :
      (ρ.tensor σ).restrict φ = (ρ.restrict φ).tensor (σ.restrict φ) := rfl
  have hgen (ρ σ : FiniteContinuousRepresentation G) :
      representationRestriction φ
          (representationMul G (finiteRepresentationClass ρ) (finiteRepresentationClass σ)) =
        representationMul H
          (representationRestriction φ (finiteRepresentationClass ρ))
          (representationRestriction φ (finiteRepresentationClass σ)) := by
    rw [representationMul_finiteClass, representationRestriction_finiteClass,
      representationRestriction_finiteClass, representationRestriction_finiteClass,
      representationMul_finiteClass, htensor]
  -- Extend from each fixed finite generator in the second argument.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      (representationRestriction φ).comp (representationMul G (finiteRepresentationClass ρ)) =
        (representationMul H (representationRestriction φ (finiteRepresentationClass ρ))).comp
          (representationRestriction φ) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro σ
    exact hgen ρ σ
  constructor
  · intro a b
    -- Extend in the first argument while keeping the same restricted second argument.
    have h : (representationRestriction φ).comp ((representationMul G).flip b) =
        ((representationMul H).flip (representationRestriction φ b)).comp
          (representationRestriction φ) := by
      apply QuotientAddGroup.addMonoidHom_ext
      apply FreeAbelianGroup.lift_ext
      intro ρ
      exact DFunLike.congr_fun (hρ ρ) b
    exact DFunLike.congr_fun h a
  · change representationRestriction φ
      (finiteRepresentationClass (FiniteContinuousRepresentation.trivial (G := G))) =
        finiteRepresentationClass (FiniteContinuousRepresentation.trivial (G := H))
    rw [representationRestriction_finiteClass]
    rfl

/-- The restriction ring homomorphism has exactly the already defined additive map. -/
def representationRestrictionRingHom (φ : H →ₜ* G) :
    RepresentationGrothendieckGroup G →+* RepresentationGrothendieckGroup H where
  __ := representationRestriction φ
  map_one' := (representationRestriction_multiplicative φ).2
  map_mul' := (representationRestriction_multiplicative φ).1

end AtiyahSinger
