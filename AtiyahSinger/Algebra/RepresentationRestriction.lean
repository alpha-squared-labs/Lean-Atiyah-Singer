/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationGrothendieckGroup

/-!
# Restriction of actual representation classes along continuous group homomorphisms

Public module ID: M0054.

Precompose each actual group action with a continuous homomorphism, retaining
its vector-space carrier and joint continuity. This operation descends from
the free abelian group through the existing isomorphism and direct-sum
relations. Its generator and arbitrary-space formulas retain these original
actions, rather than selecting a representation with the same dimension.

Identity, composition and dimension compatibility describe this contravariant
restriction on the existing representation Grothendieck groups. No group
compactness, unitarity or decomposition into irreducibles is needed.
Sources: SG III.9, printed pp.211--212, supplies the finite continuous complex
representation construction. Restriction is the standard precomposition
supplement, matching mathlib's actual `ContRepresentation.restrict`; these SG
pages do not separately number a restriction lemma. The explicit quotient
descent is a project expansion, proved for these same precomposed actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger


set_option linter.unusedSectionVars false

variable {G H K : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Restrict the same finite-model action by actual continuous group precomposition. -/
def FiniteContinuousRepresentation.restrict
    (ρ : FiniteContinuousRepresentation G) (φ : H →ₜ* G) :
    FiniteContinuousRepresentation H where
  dimension := ρ.dimension
  representation := ρ.representation.restrict φ.toMonoidHom
  continuous_action := ρ.continuous_action.comp
    ((φ.continuous.comp continuous_fst).prodMk continuous_snd)

/-- Restriction sends the original representation relations to zero in the target group. -/
theorem representationRelations_le_ker_restrict (φ : H →ₜ* G) :
    representationRelations G ≤
      (FreeAbelianGroup.lift (fun ρ : FiniteContinuousRepresentation G ↦
        finiteRepresentationClass (ρ.restrict φ))).ker := by
  /- Stage 1: an actual continuous linear intertwiner for G also intertwines
  the restricted H actions: substitute φ(h) into its original intertwining
  equation. Its same inverse and original topologies are retained. Thus each
  isomorphism-relation generator maps to zero in the target Grothendieck group.
  Stage 2: restriction commutes with the actual ordered direct sum. Both
  routes use the same Fin-addition coordinate equivalence and evaluate the
  original two action blocks at φ(h). Their jointly continuous actions are
  equal, up to proof irrelevance for the continuity witnesses. Each original
  direct-sum relation therefore maps to its corresponding target relation.
  Stage 3: the kernel of the specified free-group lift is an additive subgroup.
  Since it contains both generating families, it contains their closure.
  This certificate allows the actual lift to descend, without imposing new
  relations such as arbitrary nonsplit exact-sequence relations. -/
  -- Restrict the same equivariant linear map by substituting the image group element.
  have hiso (ρ σ : FiniteContinuousRepresentation G) (h : ρ.IsEquivalent σ) :
      finiteRepresentationClass (ρ.restrict φ) = finiteRepresentationClass (σ.restrict φ) := by
    obtain ⟨e⟩ := h
    apply finiteRepresentationClass_eq_of_isEquivalent
    exact ⟨ContRepresentation.Equiv.mk e.toContinuousLinearEquiv
      (fun h ↦ e.isIntertwining (φ h))⟩
  -- Both ordered block constructions have definitionally the same action and coordinates.
  have hsum (ρ σ : FiniteContinuousRepresentation G) :
      (ρ.directSum σ).restrict φ = (ρ.restrict φ).directSum (σ.restrict φ) := rfl
  apply (AddSubgroup.closure_le _).mpr
  rintro x (⟨ρ, σ, hρσ, rfl⟩ | ⟨ρ, σ, rfl⟩)
  · change (FreeAbelianGroup.lift _) (_ - _) = 0
    simp [hiso ρ σ hρσ]
  · change (FreeAbelianGroup.lift _) (_ - _ - _) = 0
    simp [hsum, finiteRepresentationClass_directSum]

/-- Restriction on the existing additive representation Grothendieck groups. -/
def representationRestriction (φ : H →ₜ* G) :
    RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup H :=
  QuotientAddGroup.lift (representationRelations G)
    (FreeAbelianGroup.lift (fun ρ : FiniteContinuousRepresentation G ↦
      finiteRepresentationClass (ρ.restrict φ)))
    (fun _ hx ↦ representationRelations_le_ker_restrict φ hx)

/-- Restriction of an original finite generator is its actual precomposed action. -/
theorem representationRestriction_finiteClass (φ : H →ₜ* G)
    (ρ : FiniteContinuousRepresentation G) :
    representationRestriction φ (finiteRepresentationClass ρ) =
      finiteRepresentationClass (ρ.restrict φ) := by
  /- Evaluate the defining quotient lift on the same original free generator
  ρ. The free abelian group lift returns exactly its prescribed restricted
  representation class, including its unchanged dimension and coordinate carrier. -/
  exact FreeAbelianGroup.lift_apply_of
    (fun σ : FiniteContinuousRepresentation G ↦ finiteRepresentationClass (σ.restrict φ)) ρ

/-- Arbitrary finite-dimensional actions restrict on their unchanged original carrier. -/
theorem representationRestriction_class (φ : H →ₜ* G)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    representationRestriction φ (representationClass ρ hρ) =
      representationClass (ρ.restrict φ.toMonoidHom)
        (hρ.comp ((φ.continuous.comp continuous_fst).prodMk continuous_snd)) := by
  /- The coordinates chosen by representationClass depend only on E.
  Unfold both class presentations, use the finite-generator restriction
  formula, and identify their actions by definition: both evaluate the
  original operator at phi(h) in the same coordinates. The displayed
  composite transports the original joint continuity witness. -/
  -- The chosen coordinates depend only on E, so both action presentations use the same map.
  unfold representationClass
  rw [representationRestriction_finiteClass]
  rfl

/-- Restriction along the identity group homomorphism is the identity homomorphism. -/
theorem representationRestriction_id :
    representationRestriction (ContinuousMonoidHom.id G) =
      AddMonoidHom.id (RepresentationGrothendieckGroup G) := by
  /- On every original finite generator, precomposition by identity retains
  the same action, dimension and jointly continuous map. The generator formula
  gives identity there. Since these classes generate the original quotient
  additively, the two displayed additive homomorphisms are equal. -/
  -- Check the identity on original finite generators before extending through the quotient.
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro ρ
  change representationRestriction (ContinuousMonoidHom.id G) (finiteRepresentationClass ρ) =
    finiteRepresentationClass ρ
  rw [representationRestriction_finiteClass]
  rfl

/-- Restriction along a composite agrees with the same successive precompositions. -/
theorem representationRestriction_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) :
    representationRestriction (φ.comp ψ) =
      (representationRestriction ψ).comp (representationRestriction φ) := by
  /- Stage 1: on a finite representation ρ, both routes evaluate its original
  action at φ(ψ(k)), on the unchanged finite carrier. The identity of these
  representations also respects their explicitly composed continuity proofs.
  Stage 2: use the generator formula twice, then equality of additive maps on
  the generating classes. The reversed order is the contravariance of group
  restriction; no injectivity or surjectivity of either homomorphism is needed. -/
  -- Both restrictions evaluate the same original operator at φ (ψ k).
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro ρ
  change representationRestriction (φ.comp ψ) (finiteRepresentationClass ρ) =
    representationRestriction ψ (representationRestriction φ (finiteRepresentationClass ρ))
  rw [representationRestriction_finiteClass, representationRestriction_finiteClass,
    representationRestriction_finiteClass]
  rfl

/-- Restricting the action leaves the actual underlying vector-space dimension unchanged. -/
theorem representationDimension_restriction (φ : H →ₜ* G) :
    (representationDimension H).comp (representationRestriction φ) =
      representationDimension G := by
  /- On a finite generator, restriction keeps exactly its original dimension.
  Apply representationRestriction_finiteClass and both dimension formulas.
  Equality extends from these generators to the additive Grothendieck group,
  including virtual differences. This statement forgets the group action
  only through the explicit dimension maps. -/
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro ρ
  change representationDimension H (representationRestriction φ (finiteRepresentationClass ρ)) =
    representationDimension G (finiteRepresentationClass ρ)
  rw [representationRestriction_finiteClass, representationDimension_finiteClass,
    representationDimension_finiteClass]
  rfl

end AtiyahSinger
