/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.RelativeCohomologyGradedCommutativity
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup

/-!
# Cup product on the original compact-support cohomology

Public module ID: M1658.

D11. Compactly supported classes multiply by applying the original
ordinary-supported action after forgetting only the first factor's support.
For Hausdorff X, the representative formula identifies this exact operation
with the original two-relative cup on the intersection of its two compact
supports. This comparison uses the specified open-union small-chain map,
not an assumption that every simplex in a union lies in one member.

The operation, associativity, graded commutativity, forgetting support and
homeomorphism naturality need no separation or compactness assumption.
The intersection representative formula uses T2Space precisely to ensure
closed compact supports, open complements and a compact intersection.
Signed commutativity follows on a common union support from the relative
Alexander--Whitney homotopy; forgetting support need not be injective.

Sources: Hatcher, Algebraic Topology, section 3.2, p.209 and Theorem 3.11,
and section 3.3, pp.242--245. The support comparisons are the standard
assembly of the original relative product and directed-colimit model.
The original coefficient inclusion Z -> Q commutes with this product.
A general noncompact Hc ring is not assigned a unit; its action by the
ordinary unit is already stated in CompactSupportCohomologyAction.
The algebraic and functorial laws and the intersection-support representative
formula are proved below. Signed commutativity uses the same relative reversal
homotopy after enlarging both compact supports to their union.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The compact-support cup is the actual action after forgetting only its first support. -/
def compactSupportCohomologyCup (p q : ℕ) :
    compactSupportCohomology R X p →ₗ[R] compactSupportCohomology R X q →ₗ[R]
      compactSupportCohomology R X (p + q) :=
  (compactSupportCohomologyAction R X p q).comp
    (compactSupportCohomologyToOrdinary R X p).hom

/-- Two original supported representatives multiply at their exact intersection support. -/
theorem compactSupportCohomologyCup_representative [T2Space X]
    (K L : Compacts X) (p q : ℕ)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) p)
    (b : relativeSingularCohomology R ((L : Set X)ᶜ) q) :
    compactSupportCohomologyCup R X p q (compactSupportCohomologyClass R X K p a)
        (compactSupportCohomologyClass R X L q b) =
      compactSupportCohomologyClass R X (K ⊓ L) (p + q)
        ((eqToIso (by rw [Compacts.coe_inf, Set.compl_inter]) :
            relativeSingularCohomology R ((K : Set X)ᶜ ∪ (L : Set X)ᶜ) (p + q) ≅
              relativeSingularCohomology R (((K ⊓ L : Compacts X) : Set X)ᶜ)
                (p + q)).hom
          (relativeSingularCohomologyUnionCup R ((K : Set X)ᶜ) ((L : Set X)ᶜ)
            K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a b)) := by
  /- Stage 1: evaluate the defining action on the original L-relative
  representative and the original forget-support map on the K-relative
  representative. The left side becomes the original L injection of
  the ordinary-relative product, with only a's support forgotten.
  Stage 2: apply relativeSingularCohomologyUnionCup_restrict_right to
  the two open complements. Its exact union comparison identifies
  this relative action with restriction of the prescribed two-relative
  cup. De Morgan's equality is precisely the displayed pair transport.
  Stage 3: K intersection L is compact and contained in L. The original
  colimit cocone identifies its injection followed by this restriction
  with the original L injection. No unrelated representative is chosen,
  and no injectivity of a forget-support map is assumed. -/
  -- The original colimit leg forgets support by its prescribed relative projection.
  have hforget : compactSupportCohomologyToOrdinary R X p
      (compactSupportCohomologyClass R X K p a) =
        relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) p a := by
    have hleg : compactSupportCohomologyClass R X K p ≫
        compactSupportCohomologyToOrdinary R X p =
          relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) p :=
      Limits.colimit.ι_desc _ K
    exact congrArg (fun f ↦ f a) hleg
  dsimp only [compactSupportCohomologyCup, LinearMap.comp_apply]
  rw [hforget, compactSupportCohomologyAction_representative]
  rw [← relativeSingularCohomologyUnionCup_restrict_right R
    ((K : Set X)ᶜ) ((L : Set X)ᶜ)
    K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a b]
  -- Pair transport by De Morgan's equality commutes with the same relative restriction.
  have htransport (A A' B : Set X) (h : A = A') (hBA : B ⊆ A) (hBA' : B ⊆ A') :
      (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + q)) h)).hom ≫
          relativeSingularCohomologyRestriction R B A' hBA' (p + q) =
        relativeSingularCohomologyRestriction R B A hBA (p + q) := by
    subst A'
    simp
  let hset : (K : Set X)ᶜ ∪ (L : Set X)ᶜ = ((K ⊓ L : Compacts X) : Set X)ᶜ := by
    rw [Compacts.coe_inf, Set.compl_inter]
  let c := relativeSingularCohomologyUnionCup R ((K : Set X)ᶜ) ((L : Set X)ᶜ)
    K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a b
  let e := eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + q)) hset)
  have hrestriction : e.hom ≫
        (compactSupportCohomologyFunctor R X (p + q)).map
          (homOfLE (inf_le_right : K ⊓ L ≤ L)) =
      relativeSingularCohomologyRestriction R ((L : Set X)ᶜ)
        ((K : Set X)ᶜ ∪ (L : Set X)ᶜ) (fun _ h ↦ Or.inr h) (p + q) :=
    htransport _ _ _ hset _ _
  -- The directed-colimit cocone identifies the intersection leg with its image at L.
  have hcocone := Limits.colimit.w (compactSupportCohomologyFunctor R X (p + q))
    (homOfLE (inf_le_right : K ⊓ L ≤ L))
  change compactSupportCohomologyClass R X L (p + q)
      (relativeSingularCohomologyRestriction R ((L : Set X)ᶜ)
        ((K : Set X)ᶜ ∪ (L : Set X)ᶜ) (fun _ h ↦ Or.inr h) (p + q) c) =
    compactSupportCohomologyClass R X (K ⊓ L) (p + q) (e.hom c)
  rw [← hrestriction]
  exact congrArg (fun f ↦ f (e.hom c)) hcocone

/-- The original compact-support product is associative, with only degree reassociation. -/
theorem compactSupportCohomologyCup_assoc (p q r : ℕ)
    (a : compactSupportCohomology R X p) (b : compactSupportCohomology R X q)
    (c : compactSupportCohomology R X r) :
    (eqToIso (by rw [Nat.add_assoc]) :
        compactSupportCohomology R X ((p + q) + r) ≅
          compactSupportCohomology R X (p + (q + r))).hom
      (compactSupportCohomologyCup R X (p + q) r
        (compactSupportCohomologyCup R X p q a b) c) =
    compactSupportCohomologyCup R X p (q + r) a
      (compactSupportCohomologyCup R X q r b c) := by
  /- Stage 1: unfold the actual cup definition. Forgetting the inner
  action gives the original ordinary cup of the same forgotten a and b,
  by compactSupportCohomologyToOrdinary_action.
  Stage 2: use compactSupportCohomologyAction_assoc with those original
  ordinary classes and c. Refolding the same action composites gives
  the right side. Only the displayed degree reassociation is needed;
  no Hausdorff hypothesis or new three-relative product is required. -/
  -- Rewrite the forgotten inner product as the ordinary cup of the same two classes.
  dsimp only [compactSupportCohomologyCup, LinearMap.comp_apply]
  rw [compactSupportCohomologyToOrdinary_action]
  -- The existing action associates on the unchanged third supported class.
  exact compactSupportCohomologyAction_assoc R X p q r
    (compactSupportCohomologyToOrdinary R X p a)
    (compactSupportCohomologyToOrdinary R X q b) c

/-- The compact-support cup is graded commutative with its full degree-dependent sign. -/
theorem compactSupportCohomologyCup_comm (p q : ℕ)
    (a : compactSupportCohomology R X p) (b : compactSupportCohomology R X q) :
    (eqToIso (by rw [Nat.add_comm p q]) :
        compactSupportCohomology R X (p + q) ≅
          compactSupportCohomology R X (q + p)).hom
      (compactSupportCohomologyCup R X p q a b) =
    (-1 : R) ^ (p * q) • compactSupportCohomologyCup R X q p b a := by
  /- Stage 1: choose original representatives at K and L and enlarge
  both to the same compact union K union L. The action representative
  formula identifies both products with the corresponding relative
  cochain products for that single complement pair.
  Stage 2: signed reversal of original simplex vertices and its prism
  chain homotopy preserve this same subspace. They therefore induce
  the relative cohomology identity, exactly as in Hatcher Theorem 3.11.
  Reversal interchanges the original front and back faces, producing
  (-1)^(p*q); the coefficient ring is commutative.
  Stage 3: pass through the original relative cocycle quotients and the
  same union-support injection. This proves equality in Hc itself,
  not merely after forgetting support. Neither open complements nor
  cofinal intersections are used, so no separation assumption is needed. -/
  -- At a single compact support, both factors are relative to exactly the same subspace.
  have hsame (K : Compacts X)
      (α : relativeSingularCohomology R ((K : Set X)ᶜ) p)
      (β : relativeSingularCohomology R ((K : Set X)ᶜ) q) :
      (eqToIso (by rw [Nat.add_comm p q]) :
          compactSupportCohomology R X (p + q) ≅
            compactSupportCohomology R X (q + p)).hom
        (compactSupportCohomologyCup R X p q
          (compactSupportCohomologyClass R X K p α)
          (compactSupportCohomologyClass R X K q β)) =
      (-1 : R) ^ (p * q) • compactSupportCohomologyCup R X q p
        (compactSupportCohomologyClass R X K q β)
        (compactSupportCohomologyClass R X K p α) := by
    have hforget (n : ℕ) (c : relativeSingularCohomology R ((K : Set X)ᶜ) n) :
        compactSupportCohomologyToOrdinary R X n
          (compactSupportCohomologyClass R X K n c) =
          relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) n c := by
      have hleg : compactSupportCohomologyClass R X K n ≫
          compactSupportCohomologyToOrdinary R X n =
            relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) n :=
        Limits.colimit.ι_desc _ K
      exact congrArg (fun f ↦ f c) hleg
    have htransport (n m : ℕ) (h : n = m)
        (c : relativeSingularCohomology R ((K : Set X)ᶜ) n) :
        (eqToIso (congrArg (compactSupportCohomology R X) h)).hom
          (compactSupportCohomologyClass R X K n c) =
        compactSupportCohomologyClass R X K m
          ((eqToIso (congrArg (relativeSingularCohomology R ((K : Set X)ᶜ)) h)).hom c) := by
      subst m
      rfl
    dsimp only [compactSupportCohomologyCup, LinearMap.comp_apply]
    rw [hforget, hforget, compactSupportCohomologyAction_representative,
      compactSupportCohomologyAction_representative,
      htransport (p + q) (q + p) (Nat.add_comm p q),
      relativeSingularCohomologyAction_comm, map_smul]
  -- The directed colimit moves the two original representatives to their compact union.
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X p a
  obtain ⟨L, β, rfl⟩ := compactSupportCohomology_exists_representative R X q b
  let M := K ⊔ L
  let f : K ⟶ M := homOfLE le_sup_left
  let g : L ⟶ M := homOfLE le_sup_right
  let α' := (compactSupportCohomologyFunctor R X p).map f α
  let β' := (compactSupportCohomologyFunctor R X q).map g β
  have hα : compactSupportCohomologyClass R X M p α' =
      compactSupportCohomologyClass R X K p α :=
    congrArg (fun F ↦ F α) (Limits.colimit.w (compactSupportCohomologyFunctor R X p) f)
  have hβ : compactSupportCohomologyClass R X M q β' =
      compactSupportCohomologyClass R X L q β :=
    congrArg (fun F ↦ F β) (Limits.colimit.w (compactSupportCohomologyFunctor R X q) g)
  rw [← hα, ← hβ]
  exact hsame M α' β'

/-- Forgetting both supports identifies this cup with the existing ordinary cup product. -/
theorem compactSupportCohomologyToOrdinary_cup (p q : ℕ)
    (a : compactSupportCohomology R X p) (b : compactSupportCohomology R X q) :
    compactSupportCohomologyToOrdinary R X (p + q)
        (compactSupportCohomologyCup R X p q a b) =
      singularCohomologyCup R X p q (compactSupportCohomologyToOrdinary R X p a)
        (compactSupportCohomologyToOrdinary R X q b) := by
  /- Unfold the actual cup definition and apply the action's forget
  compatibility to the same ordinary image of a and supported b.
  Both forget maps are the original relative-to-ordinary cocones;
  this is equality of the specified maps and products. -/
  -- Apply the action comparison to precisely the original forgotten first input.
  exact compactSupportCohomologyToOrdinary_action R X p q
    (compactSupportCohomologyToOrdinary R X p a) b

variable {X}

/-- The existing pullback by the original homeomorphism preserves the supported cup product. -/
theorem compactSupportCohomologyHomeomorphPullback_cup
    {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y) (p q : ℕ)
    (a : compactSupportCohomology R Y p) (b : compactSupportCohomology R Y q) :
    compactSupportCohomologyHomeomorphPullback R e (p + q)
        (compactSupportCohomologyCup R Y p q a b) =
      compactSupportCohomologyCup R X p q
        (compactSupportCohomologyHomeomorphPullback R e p a)
        (compactSupportCohomologyHomeomorphPullback R e q b) := by
  /- Stage 1: on each original compact-support representative,
  forgetting support commutes with the actual relative pullback by e.
  Its inverse-image support is the one used by the existing Hc map.
  Stage 2: unfold cup and apply the action's homeomorphism naturality.
  The first-stage square identifies its ordinary first factor with
  the original forget-support image on X. Refold the same cup. -/
  -- Compare forgetting support and pullback on the same original compact representative.
  have hforget : singularCohomologyPullback R ⟨e, e.continuous⟩ p
      (compactSupportCohomologyToOrdinary R Y p a) =
        compactSupportCohomologyToOrdinary R X p
          (compactSupportCohomologyHomeomorphPullback R e p a) := by
    obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R Y p a
    let L := homeomorphCompactPreimage e K
    let f : C(X, Y) := ⟨e, e.continuous⟩
    have hf : Set.MapsTo f ((L : Set X)ᶜ) ((K : Set Y)ᶜ) := fun _ hx ↦ hx
    have hY : compactSupportCohomologyClass R Y K p ≫
        compactSupportCohomologyToOrdinary R Y p =
          relativeSingularCohomologyToOrdinary R ((K : Set Y)ᶜ) p :=
      CategoryTheory.Limits.colimit.ι_desc _ K
    have hX : compactSupportCohomologyClass R X L p ≫
        compactSupportCohomologyToOrdinary R X p =
          relativeSingularCohomologyToOrdinary R ((L : Set X)ᶜ) p :=
      CategoryTheory.Limits.colimit.ι_desc _ L
    -- The quotient projection square uses exactly this homeomorphism of complement pairs.
    let H := singularCochainDualFunctor R ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p
    have hchain : relativeSingularChainsProjection R ((L : Set X)ᶜ) ≫
        relativeSingularChainsMap R f hf =
          (singularChainsFunctor R).map (TopCat.ofHom f) ≫
            relativeSingularChainsProjection R ((K : Set Y)ᶜ) := by
      simp [relativeSingularChainsProjection, relativeSingularChainsMap]
    have hpair : relativeSingularCohomologyToOrdinary R ((K : Set Y)ᶜ) p ≫
        singularCohomologyPullback R f p =
          relativeSingularCohomologyPullback R f hf p ≫
            relativeSingularCohomologyToOrdinary R ((L : Set X)ᶜ) p := by
      change H.map (relativeSingularChainsProjection R ((K : Set Y)ᶜ)).op ≫
          H.map ((singularChainsFunctor R).map (TopCat.ofHom f)).op =
        H.map (relativeSingularChainsMap R f hf).op ≫
          H.map (relativeSingularChainsProjection R ((L : Set X)ᶜ)).op
      rw [← H.map_comp, ← H.map_comp, ← CategoryTheory.op_comp,
        ← CategoryTheory.op_comp, hchain]
    rw [compactSupportCohomologyHomeomorphPullback_representative]
    change singularCohomologyPullback R f p
        (compactSupportCohomologyToOrdinary R Y p
          (compactSupportCohomologyClass R Y K p α)) =
      compactSupportCohomologyToOrdinary R X p
        (compactSupportCohomologyClass R X L p
          (relativeSingularCohomologyPullback R f hf p α))
    rw [show compactSupportCohomologyToOrdinary R Y p
        (compactSupportCohomologyClass R Y K p α) =
          relativeSingularCohomologyToOrdinary R ((K : Set Y)ᶜ) p α from
      congrArg (fun g ↦ g α) hY]
    rw [show compactSupportCohomologyToOrdinary R X p
        (compactSupportCohomologyClass R X L p
          (relativeSingularCohomologyPullback R f hf p α)) =
        relativeSingularCohomologyToOrdinary R ((L : Set X)ᶜ) p
          (relativeSingularCohomologyPullback R f hf p α) from
      congrArg (fun g ↦ g (relativeSingularCohomologyPullback R f hf p α)) hX]
    exact congrArg (fun g ↦ g α) hpair
  -- Naturality of the original action now applies to the unchanged two supported inputs.
  dsimp only [compactSupportCohomologyCup, LinearMap.comp_apply]
  rw [compactSupportCohomologyHomeomorphPullback_action, hforget]

/-- The actual integer-to-rational coefficient maps preserve the compact-support cup product. -/
theorem compactSupportCohomologyRationalization_cup (X : Type u) [TopologicalSpace X]
    (p q : ℕ) (a : compactSupportCohomology ℤ X p) (b : compactSupportCohomology ℤ X q) :
    compactSupportCohomologyRationalization X (p + q)
        (compactSupportCohomologyCup ℤ X p q a b) =
      compactSupportCohomologyCup ℚ X p q (compactSupportCohomologyRationalization X p a)
        (compactSupportCohomologyRationalization X q b) := by
  /- Unfold the actual action composite. Its coefficient compatibility
  treats the original forgotten first factor and supported second
  factor. compactSupportCohomologyRationalization_toOrdinary identifies
  that first factor with the ordinary image of the original rationalized
  a. Refolding gives exactly the rational cup on the same two images.
  This does not assert that every rational supported class is an
  integral coefficient image or that coefficient inclusion is injective. -/
  -- Coefficient inclusion preserves the action on these same two integral inputs.
  dsimp only [compactSupportCohomologyCup, LinearMap.comp_apply]
  rw [compactSupportCohomologyRationalization_action,
    compactSupportCohomologyRationalization_toOrdinary]
  rfl

end AtiyahSinger
