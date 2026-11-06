/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRingRestriction
public import Mathlib.RepresentationTheory.Character

import AtiyahSinger.Algebra.CompactRepresentationEquivalence

/-!
# Characters of the original finite continuous representation ring

Public module ID: M0051.

AL03/AR04: the character of a virtual representation is the trace of its
actual action, extended through the existing split Grothendieck presentation.
The generator formula below uses mathlib's `Representation.character` on the
original `ContRepresentation.toRepresentation`. The target ring has pointwise
operations on functions G -> C; continuity and conjugacy invariance are
properties of this specified character, not replacement definitions.

Compact Hausdorff groups have injective character maps on these original
virtual classes. Compactness is essential: the original quotient imposes
isomorphism and direct-sum relations, not arbitrary exact-sequence relations.
For a noncompact group, a nonsplit extension can have the same trace as a
split sum. Joint continuity of each finite action is also essential for the
Haar averaging argument; it is retained in FiniteContinuousRepresentation.
Mathlib's finite-group character orthogonality alone does not cover O(r).

Source: Atiyah--Singer I, Proposition (4.4), p.505, uses detection by compact
group characters; Lemma (4.7), pp.507--508, uses the representation rings in
low dimensions. The general compact-group character theorem is a standard
supplementary input invoked there. Its Haar projection and invariant-splitting
argument applies to the same finite representations.
SG III.9 pp.211--212 supplies the original R(G).
This module does not assert any point-pushforward index normalization.
Compact-group character injectivity uses the same actual finite actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual traces extend uniquely to a ring homomorphism on the original representation ring. -/
theorem existsUnique_representationCharacter :
    ∃! χ : RepresentationGrothendieckGroup G →+* (G → ℂ),
      ∀ ρ : FiniteContinuousRepresentation G,
        χ (finiteRepresentationClass ρ) = ρ.representation.toRepresentation.character := by
  /- Stage 1: the trace is unchanged by an actual equivariant linear
  isomorphism and is additive on the specified ordered direct sum. Thus its
  function of the group element kills precisely the two families generating
  representationRelations. Descend the free additive trace map through that
  same quotient, without adding exact-sequence or semisimplicity relations.
  Stage 2: the actual tensor representation has pointwise character equal
  to the product of the two characters. On the original one-dimensional
  trivial representation it is the constant function one. Extend these
  identities from generators by additivity to certify a ring homomorphism
  for the already specified tensor multiplication and unit.
  Stage 3: finite representation classes generate the additive quotient.
  Any two homomorphisms with the displayed trace values therefore coincide
  on every original virtual class. No compactness is used in this descent. -/
  classical
  -- Actual equivariant isomorphisms preserve trace on the original carriers.
  have hiso (ρ σ : FiniteContinuousRepresentation G) (h : ρ.IsEquivalent σ) :
      ρ.representation.toRepresentation.character =
        σ.representation.toRepresentation.character := by
    obtain ⟨e⟩ := h
    apply Representation.char_iso
    refine Representation.Equiv.mk e.toContinuousLinearEquiv.toLinearEquiv ?_
    intro g
    exact congrArg ContinuousLinearMap.toLinearMap (e.isIntertwining g)
  -- The ordered sum is conjugate to the original block action in its specified coordinates.
  have hadd (ρ σ : FiniteContinuousRepresentation G) :
      (ρ.directSum σ).representation.toRepresentation.character =
        ρ.representation.toRepresentation.character +
          σ.representation.toRepresentation.character := by
    let d : (Fin (ρ.dimension + σ.dimension) → ℂ) ≃L[ℂ]
        (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : Fin ρ.dimension ⊕ Fin σ.dimension ↦ ℂ) finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin ρ.dimension) (Fin σ.dimension)
          (fun _ ↦ ℂ))
    funext g
    change LinearMap.trace ℂ _ (d.toLinearEquiv.symm.conj
      ((ρ.representation g).toLinearMap.prodMap (σ.representation g).toLinearMap)) = _
    rw [LinearMap.trace_conj', LinearMap.trace_prodMap']
    rfl
  have htensor (ρ σ : FiniteContinuousRepresentation G) :
      (ρ.tensor σ).representation.toRepresentation.character =
        ρ.representation.toRepresentation.character *
          σ.representation.toRepresentation.character := by
    funext g
    change LinearMap.trace ℂ _
      ((FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension).conj
        (TensorProduct.map (ρ.representation g).toLinearMap (σ.representation g).toLinearMap)) = _
    rw [LinearMap.trace_conj', LinearMap.trace_tensorProduct']
    rfl
  have hone :
      (FiniteContinuousRepresentation.trivial (G := G)).representation.toRepresentation.character =
        (1 : G → ℂ) := by
    funext g
    change LinearMap.trace ℂ (Fin 1 → ℂ) (LinearMap.id) = 1
    simp
  -- Descend trace through exactly the original additive isomorphism and sum relations.
  obtain ⟨χ, hχ, hχunique⟩ := representationGrothendieckGroup_universal_property
    (fun ρ : FiniteContinuousRepresentation G ↦ ρ.representation.toRepresentation.character)
    hiso hadd
  have hext (f k : RepresentationGrothendieckGroup G →+ (G → ℂ))
      (h : ∀ ρ, f (finiteRepresentationClass ρ) = k (finiteRepresentationClass ρ)) : f = k := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- Extend tensor multiplicativity first in the second variable, then in the first.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      χ.comp (representationMul G (finiteRepresentationClass ρ)) =
        { toFun := fun y ↦ χ (finiteRepresentationClass ρ) * χ y
          map_zero' := by simp
          map_add' := by intro y z; simp [mul_add] } := by
    apply hext
    intro σ
    simp only [AddMonoidHom.comp_apply, representationMul_finiteClass, hχ, htensor,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hmul (x y : RepresentationGrothendieckGroup G) : χ (x * y) = χ x * χ y := by
    have h : χ.comp ((representationMul G).flip y) =
        { toFun := fun z ↦ χ z * χ y
          map_zero' := by simp
          map_add' := by intro z w; simp [add_mul] } := by
      apply hext
      intro ρ
      exact DFunLike.congr_fun (hρ ρ) y
    exact DFunLike.congr_fun h x
  have hunit : χ 1 = 1 := by
    change χ (finiteRepresentationClass (FiniteContinuousRepresentation.trivial (G := G))) = 1
    rw [hχ, hone]
  let φ : RepresentationGrothendieckGroup G →+* (G → ℂ) :=
    { χ with map_one' := hunit, map_mul' := hmul }
  refine ⟨φ, hχ, ?_⟩
  -- Additive uniqueness already compares every virtual class, hence the ring maps.
  intro ψ hψ
  apply RingHom.ext
  intro a
  exact DFunLike.congr_fun (hχunique ψ.toAddMonoidHom hψ) a

/-- The trace character on the original quotient, uniquely fixed on every actual generator. -/
def representationCharacter : RepresentationGrothendieckGroup G →+* (G → ℂ) :=
  Classical.choose (existsUnique_representationCharacter G).exists

/-- A generator's character is the trace of its original group action on the same finite model. -/
theorem representationCharacter_finiteClass (ρ : FiniteContinuousRepresentation G) :
    representationCharacter G (finiteRepresentationClass ρ) =
      ρ.representation.toRepresentation.character := by
  /- Evaluate the specification of the unique trace homomorphism on this
  very generator. Its action and finite coordinates have not been changed;
  mathlib's character is the trace of the original underlying linear map. -/
  exact (Classical.choose_spec (existsUnique_representationCharacter G).exists) ρ

/-- Every virtual character is continuous in the original topology of the group. -/
theorem representationCharacter_continuous (a : RepresentationGrothendieckGroup G) :
    Continuous (representationCharacter G a) := by
  /- Stage 1: evaluate the original jointly continuous action on each fixed
  coordinate basis vector. Its finitely many matrix entries are continuous
  in g, so their diagonal sum is the continuous trace character.
  Stage 2: write the original quotient element as a finite integer linear
  combination of generator classes. The trace characterization turns its
  character into that same finite combination of continuous functions.
  This does not infer joint continuity from ContRepresentation alone. -/
  classical
  -- Each diagonal coefficient is continuous by the actual joint action continuity.
  have hfinite (ρ : FiniteContinuousRepresentation G) :
      Continuous ρ.representation.toRepresentation.character := by
    have hformula : ρ.representation.toRepresentation.character =
        fun g ↦ ∑ i : Fin ρ.dimension, ρ.representation g (Pi.single i 1) i := by
      funext g
      rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ _)]
      simp [Matrix.trace]
      rfl
    rw [hformula]
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).comp
      (ρ.continuous_action.comp (continuous_id.prodMk continuous_const))
  -- Every original quotient element is a finite additive combination of generator classes.
  refine Quotient.inductionOn a ?_
  intro z
  change Continuous (representationCharacter G ((QuotientAddGroup.mk' _) z))
  induction z using FreeAbelianGroup.induction_on with
  | zero => simpa only [map_zero, Pi.zero_def] using (continuous_const (y := (0 : ℂ)))
  | of ρ =>
    change Continuous (representationCharacter G (finiteRepresentationClass ρ))
    rw [representationCharacter_finiteClass]
    exact hfinite ρ
  | neg ρ hρ => simpa only [map_neg] using hρ.neg
  | add u v hu hv => simpa only [map_add] using hu.add hv

/-- The same virtual character is constant on conjugacy classes. -/
theorem representationCharacter_conj (a : RepresentationGrothendieckGroup G) (g h : G) :
    representationCharacter G a (h * g * h⁻¹) = representationCharacter G a g := by
  /- For a finite generator the action of h conjugates the action of g,
  and trace is invariant under this linear equivalence. This is mathlib's
  character-conjugacy identity on the original representation. Additivity
  extends it to the same virtual quotient class, with no compactness premise. -/
  -- Compare the two additive evaluations on each original representation generator.
  have heq : (Pi.evalAddMonoidHom (fun _ : G ↦ ℂ) (h * g * h⁻¹)).comp
        (representationCharacter G).toAddMonoidHom =
      (Pi.evalAddMonoidHom (fun _ : G ↦ ℂ) g).comp
        (representationCharacter G).toAddMonoidHom := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    change representationCharacter G (finiteRepresentationClass ρ) (h * g * h⁻¹) =
      representationCharacter G (finiteRepresentationClass ρ) g
    rw [representationCharacter_finiteClass]
    exact ρ.representation.toRepresentation.char_conj g h
  exact DFunLike.congr_fun heq a

/-- Character at the identity equals the original integer dimension augmentation. -/
theorem representationCharacter_apply_one (a : RepresentationGrothendieckGroup G) :
    representationCharacter G a 1 = (representationDimension G a : ℂ) := by
  /- On an actual generator, the identity acts by the identity linear map,
  whose trace is its given finite dimension. The original dimension map has
  that same generator value. Additivity and compatibility of the integer
  cast with sums and negatives identify both maps on all virtual classes. -/
  -- Evaluation at identity and dimension are additive maps on the same quotient.
  have heq : (Pi.evalAddMonoidHom (fun _ : G ↦ ℂ) 1).comp
        (representationCharacter G).toAddMonoidHom =
      (Int.castAddHom ℂ).comp (representationDimension G) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    change representationCharacter G (finiteRepresentationClass ρ) 1 =
      (representationDimension G (finiteRepresentationClass ρ) : ℂ)
    rw [representationCharacter_finiteClass, representationDimension_finiteClass]
    simp
  exact DFunLike.congr_fun heq a

variable {G} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Original representation restriction precomposes its actual character by the same group map. -/
theorem representationCharacter_restrict (φ : H →ₜ* G)
    (a : RepresentationGrothendieckGroup G) (h : H) :
    representationCharacter H (representationRestrictionRingHom φ a) h =
      representationCharacter G a (φ h) := by
  /- On a finite generator, restriction precomposes the original group
  action by phi and retains its finite model. At h, the two traces are
  therefore traces of the identical linear operator rho(phi(h)). Extend
  through the original additive quotient and use the existing restriction
  ring homomorphism, whose additive map is that same precomposition. -/
  -- Restriction leaves the finite carrier and operator at φ(h) unchanged.
  have heq : (Pi.evalAddMonoidHom (fun _ : H ↦ ℂ) h).comp
        ((representationCharacter H).toAddMonoidHom.comp
          (representationRestrictionRingHom φ).toAddMonoidHom) =
      (Pi.evalAddMonoidHom (fun _ : G ↦ ℂ) (φ h)).comp
        (representationCharacter G).toAddMonoidHom := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    change representationCharacter H (representationRestriction φ (finiteRepresentationClass ρ)) h =
      representationCharacter G (finiteRepresentationClass ρ) (φ h)
    rw [representationRestriction_finiteClass, representationCharacter_finiteClass,
      representationCharacter_finiteClass]
    rfl
  exact DFunLike.congr_fun heq a

variable (G)

/-- Compact Hausdorff group characters distinguish the original virtual representation classes. -/
theorem representationCharacter_injective [CompactSpace G] [T2Space G] :
    Function.Injective (representationCharacter G) := by
  classical
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : MeasureTheory.Measure G := MeasureTheory.Measure.haar
  let μ : MeasureTheory.Measure G := (ν Set.univ)⁻¹ • ν
  -- Every element of the original split quotient is a difference of two finite classes.
  have hnormal (z : RepresentationGrothendieckGroup G) :
      ∃ ρ σ : FiniteContinuousRepresentation G,
        z = finiteRepresentationClass ρ - finiteRepresentationClass σ := by
    refine Quotient.inductionOn z ?_
    intro v
    change ∃ ρ σ : FiniteContinuousRepresentation G,
      (QuotientAddGroup.mk' _) v = finiteRepresentationClass ρ - finiteRepresentationClass σ
    let τ := FiniteContinuousRepresentation.trivial (G := G)
    induction v using FreeAbelianGroup.induction_on with
    | zero => exact ⟨τ, τ, by simp⟩
    | of ρ =>
      refine ⟨ρ.directSum τ, τ, ?_⟩
      rw [finiteRepresentationClass_directSum]
      simp only [add_sub_cancel_right]
      rfl
    | neg v hv =>
      obtain ⟨ρ, σ, h⟩ := hv
      refine ⟨σ, ρ, ?_⟩
      rw [map_neg, h, neg_sub]
    | add v w hv hw =>
      obtain ⟨ρ, σ, h⟩ := hv
      obtain ⟨ρ', σ', h'⟩ := hw
      refine ⟨ρ.directSum ρ', σ.directSum σ', ?_⟩
      rw [map_add, h, h', finiteRepresentationClass_directSum, finiteRepresentationClass_directSum]
      abel
  intro x y hxy
  obtain ⟨ρ, σ, hnormal⟩ := hnormal (x - y)
  have hzero : representationCharacter G (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hnormal, map_sub, representationCharacter_finiteClass,
    representationCharacter_finiteClass] at hzero
  -- Haar Hom projection and invariant splitting give an actual equivalence of those two actions.
  obtain ⟨e⟩ := nonempty_equiv_of_character_eq μ ρ.representation σ.representation
    ρ.continuous_action σ.continuous_action (sub_eq_zero.mp hzero)
  apply sub_eq_zero.mp
  rw [hnormal, finiteRepresentationClass_eq_of_isEquivalent ρ σ ⟨e⟩, sub_self]

end AtiyahSinger
