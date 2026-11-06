/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OnePointCohomology
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Homeomorphism pullback on the original compact-support colimit

Public module ID: M1661.

This standard functorial construction pulls a compact support back along the
specified homeomorphism, applies the original relative singular pullback, and
descends through the original colimit. Its equivalence has precisely this
forward map. The comparison with the one-point pair commutes with the actual
extension of the same homeomorphism. No general one-point comparison
isomorphism is asserted here.

Source: Hatcher, Algebraic Topology, section 3.3, pp.242--245, together with
relative singular functoriality and excision. The naturality comparison is a
project supplement. This construction transports the real native bundle model
back to the unchanged complex bundle total space in C04.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits TopologicalSpace OnePoint Opposite

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)

/-- The original compact support pulled back by a homeomorphism. -/
def homeomorphCompactPreimage (K : Compacts Y) : Compacts X where
  carrier := e ⁻¹' (K : Set Y)
  isCompact' := e.isCompact_preimage.mpr K.isCompact

/-- Pull back a relative representative and inject at exactly its inverse-image support. -/
def homeomorphCompactSupportCohomologyLeg (K : Compacts Y) (n : ℕ) :
    relativeSingularCohomology R ((K : Set Y)ᶜ) n ⟶
      compactSupportCohomology R X n :=
  relativeSingularCohomologyPullback R ⟨e, e.continuous⟩
      (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ)
        ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n ≫
    compactSupportCohomologyClass R X (homeomorphCompactPreimage e K) n

/-- The representative pullbacks form the cocone on the same compact-support diagram. -/
theorem homeomorphCompactSupportCohomologyLeg_naturality
    (K L : Compacts Y) (h : K ≤ L) (n : ℕ) :
    (compactSupportCohomologyFunctor R Y n).map (homOfLE h) ≫
        homeomorphCompactSupportCohomologyLeg R e L n =
      homeomorphCompactSupportCohomologyLeg R e K n := by
  /- Stage 1: inverse images preserve K subset L. Relative pullback commutes
  with restriction between their original complements by functoriality of
  the same relative chain maps.
  Stage 2: compose that square with the original colimit injections. Their
  cocone identity for e inverse K subset e inverse L gives this equality. -/
  let h' : homeomorphCompactPreimage e K ≤ homeomorphCompactPreimage e L :=
    fun _ hx ↦ h hx
  let pK := relativeSingularChainsMap R (⟨e, e.continuous⟩ : C(X, Y))
    (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ) ((K : Set Y)ᶜ)
      from fun _ hx ↦ hx)
  let pL := relativeSingularChainsMap R (⟨e, e.continuous⟩ : C(X, Y))
    (show Set.MapsTo e ((homeomorphCompactPreimage e L : Set X)ᶜ) ((L : Set Y)ᶜ)
      from fun _ hx ↦ hx)
  let rX := (relativeSingularChainsFunctor R X).map
    (homOfLE (Set.compl_subset_compl.mpr h'))
  let rY := (relativeSingularChainsFunctor R Y).map
    (homOfLE (Set.compl_subset_compl.mpr h))
  -- The square commutes on the original relative chain quotients.
  have hsquare : pL ≫ rY = rX ≫ pK := by
    apply (cancel_epi (relativeSingularChainsProjection R
      ((homeomorphCompactPreimage e L : Set X)ᶜ))).mp
    simp [pL, pK, rX, rY, relativeSingularChainsFunctor, relativeSingularChainsMap,
      relativeSingularChainsProjection, cokernel.map, Category.assoc]
  let H := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  have hcohom : (compactSupportCohomologyFunctor R Y n).map (homOfLE h) ≫
      relativeSingularCohomologyPullback R (⟨e, e.continuous⟩ : C(X, Y))
        (show Set.MapsTo e ((homeomorphCompactPreimage e L : Set X)ᶜ)
          ((L : Set Y)ᶜ) from fun _ hx ↦ hx) n =
      relativeSingularCohomologyPullback R (⟨e, e.continuous⟩ : C(X, Y))
        (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ)
          ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n ≫
        (compactSupportCohomologyFunctor R X n).map (homOfLE h') := by
    change H.map rY.op ≫ H.map pL.op = H.map pK.op ≫ H.map rX.op
    rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp, hsquare]
  -- The original cocone identifies restriction followed by its larger-support injection.
  change _ ≫ (_ ≫ compactSupportCohomologyClass R X (homeomorphCompactPreimage e L) n) = _
  erw [← Category.assoc, hcohom, Category.assoc]
  change _ ≫ ((compactSupportCohomologyFunctor R X n).map (homOfLE h') ≫
    colimit.ι (compactSupportCohomologyFunctor R X n) _) = _
  rw [colimit.w]
  rfl

/-- Pullback on compact supports induced by the actual homeomorphism. -/
def compactSupportCohomologyHomeomorphPullback (n : ℕ) :
    compactSupportCohomology R Y n ⟶ compactSupportCohomology R X n :=
  colimit.desc (compactSupportCohomologyFunctor R Y n)
    { pt := compactSupportCohomology R X n
      ι :=
        { app := fun K ↦ homeomorphCompactSupportCohomologyLeg R e K n
          naturality := by
            intro K L f
            change (compactSupportCohomologyFunctor R Y n).map f ≫
                homeomorphCompactSupportCohomologyLeg R e L n =
              homeomorphCompactSupportCohomologyLeg R e K n ≫ 𝟙 _
            rw [Category.comp_id]
            have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
            simpa only [hf] using
              homeomorphCompactSupportCohomologyLeg_naturality R e K L (leOfHom f) n } }

/-- The colimit pullback retains the actual relative pullback on each representative. -/
theorem compactSupportCohomologyHomeomorphPullback_representative
    (K : Compacts Y) (n : ℕ) (a : relativeSingularCohomology R ((K : Set Y)ᶜ) n) :
    compactSupportCohomologyHomeomorphPullback R e n
        (compactSupportCohomologyClass R Y K n a) =
      homeomorphCompactSupportCohomologyLeg R e K n a := by
  /- Evaluate the defining descent on its original K-th cocone injection.
  The resulting leg uses the same inverse-image support and pair pullback. -/
  have h : compactSupportCohomologyClass R Y K n ≫
      compactSupportCohomologyHomeomorphPullback R e n =
      homeomorphCompactSupportCohomologyLeg R e K n := colimit.ι_desc _ K
  exact congrArg (fun f ↦ f a) h

/-- The specified pullback is bijective, with inverse induced by the inverse homeomorphism. -/
theorem compactSupportCohomologyHomeomorphPullback_bijective (n : ℕ) :
    Function.Bijective (compactSupportCohomologyHomeomorphPullback R e n) := by
  /- Stage 1: inverse image under e is an equivalence of the actual compact
  supports, with inverse induced by e.symm. The original pair pullbacks form
  a natural isomorphism because e also identifies each pair of complement subspaces.
  Stage 2: take its colimit and reindex along this same support equivalence.
  The cocone equations identify their composite with the displayed pullback,
  so this specified map is invertible. Both inverse constructions use e.symm. -/
  -- The actual inverse-image operation is an order equivalence of compact supports.
  let supportEquiv : Compacts Y ≃o Compacts X :=
    { toFun := homeomorphCompactPreimage e
      invFun := homeomorphCompactPreimage e.symm
      left_inv := by
        intro K
        ext y
        change e (e.symm y) ∈ (K : Set Y) ↔ y ∈ (K : Set Y)
        rw [e.apply_symm_apply]
      right_inv := by
        intro K
        ext x
        change e.symm (e x) ∈ (K : Set X) ↔ x ∈ (K : Set X)
        rw [e.symm_apply_apply]
      map_rel_iff' := by
        intro K L
        constructor
        · intro h y hy
          obtain ⟨x, rfl⟩ := e.surjective y
          exact h hy
        · intro h x hx
          exact h hx }
  let P := supportEquiv.equivalence.functor
  let FX := compactSupportCohomologyFunctor R X n
  let FY := compactSupportCohomologyFunctor R Y n
  let H := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  -- These components are the specified pair pullbacks, before their colimit injections.
  let α : FY ⟶ P ⋙ FX :=
    { app := fun K ↦ relativeSingularCohomologyPullback R
        (⟨e, e.continuous⟩ : C(X, Y))
        (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ)
          ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n
      naturality := by
        intro K L f
        let h : K ≤ L := leOfHom f
        let h' : homeomorphCompactPreimage e K ≤ homeomorphCompactPreimage e L :=
          fun _ hx ↦ h hx
        let pK := relativeSingularChainsMap R (⟨e, e.continuous⟩ : C(X, Y))
          (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ)
            ((K : Set Y)ᶜ) from fun _ hx ↦ hx)
        let pL := relativeSingularChainsMap R (⟨e, e.continuous⟩ : C(X, Y))
          (show Set.MapsTo e ((homeomorphCompactPreimage e L : Set X)ᶜ)
            ((L : Set Y)ᶜ) from fun _ hx ↦ hx)
        let rX := (relativeSingularChainsFunctor R X).map
          (homOfLE (Set.compl_subset_compl.mpr h'))
        let rY := (relativeSingularChainsFunctor R Y).map
          (homOfLE (Set.compl_subset_compl.mpr h))
        have hsquare : pL ≫ rY = rX ≫ pK := by
          apply (cancel_epi (relativeSingularChainsProjection R
            ((homeomorphCompactPreimage e L : Set X)ᶜ))).mp
          simp [pL, pK, rX, rY, relativeSingularChainsFunctor, relativeSingularChainsMap,
            relativeSingularChainsProjection, cokernel.map, Category.assoc]
        change H.map rY.op ≫ H.map pL.op = H.map pK.op ≫ H.map rX.op
        rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp, hsquare] }
  -- The same homeomorphism restricts to the two actual complement subspaces.
  have hα (K : Compacts Y) : IsIso (α.app K) := by
    let es : ↥((homeomorphCompactPreimage e K : Set X)ᶜ) ≃ₜ ↥((K : Set Y)ᶜ) :=
      e.subtype (fun _ ↦ Iff.rfl)
    have : IsIso (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y))) := by
      change IsIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e).hom
      infer_instance
    have : IsIso (TopCat.ofHom (⟨es, es.continuous⟩ :
        C(↥((homeomorphCompactPreimage e K : Set X)ᶜ), ↥((K : Set Y)ᶜ)))) := by
      change IsIso (TopCat.isoOfHomeo
        (X := TopCat.of ↥((homeomorphCompactPreimage e K : Set X)ᶜ))
        (Y := TopCat.of ↥((K : Set Y)ᶜ)) es).hom
      infer_instance
    have : IsIso ((singularChainsFunctor R).map
        (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))) := inferInstance
    have : IsIso ((singularChainsFunctor R).map (TopCat.ofHom (⟨es, es.continuous⟩ :
        C(↥((homeomorphCompactPreimage e K : Set X)ᶜ), ↥((K : Set Y)ᶜ))))) := inferInstance
    have : IsIso (relativeSingularChainsMap R (⟨e, e.continuous⟩ : C(X, Y))
        (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ)
          ((K : Set Y)ᶜ) from fun _ hx ↦ hx)) := by
      change IsIso (cokernel.map _ _ ((singularChainsFunctor R).map
        (TopCat.ofHom (⟨es, es.continuous⟩ :
          C(↥((homeomorphCompactPreimage e K : Set X)ᶜ), ↥((K : Set Y)ᶜ)))))
        ((singularChainsFunctor R).map (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))) (by
          simp only [singularSubspaceChains, ← CategoryTheory.Functor.map_comp]
          rfl))
      infer_instance
    change IsIso (H.map (relativeSingularChainsMap R
      (⟨e, e.continuous⟩ : C(X, Y))
      (show Set.MapsTo e ((homeomorphCompactPreimage e K : Set X)ᶜ)
        ((K : Set Y)ᶜ) from fun _ hx ↦ hx)).op)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : P.IsEquivalence := inferInstanceAs supportEquiv.equivalence.functor.IsEquivalence
  -- Colimit functoriality and reindexing by this support equivalence are isomorphisms.
  have hmap : compactSupportCohomologyHomeomorphPullback R e n =
      colim.map α ≫ colimit.pre FX P := by
    apply colimit.hom_ext
    intro K
    change colimit.ι FY K ≫ compactSupportCohomologyHomeomorphPullback R e n = _
    erw [colimit.ι_desc, ← Category.assoc, ι_colimMap, Category.assoc,
      colimit.ι_pre]
    rfl
  have : IsIso (compactSupportCohomologyHomeomorphPullback R e n) := by
    rw [hmap]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The homeomorphism equivalence with the specified pullback as its forward map. -/
def compactSupportCohomologyHomeomorphEquiv (n : ℕ) :
    compactSupportCohomology R Y n ≃ₗ[R] compactSupportCohomology R X n :=
  LinearEquiv.ofBijective (compactSupportCohomologyHomeomorphPullback R e n).hom
    (compactSupportCohomologyHomeomorphPullback_bijective R e n)

/-- The original one-point comparison commutes with the same extended homeomorphism. -/
theorem compactSupportCohomologyHomeomorphPullback_toOnePoint
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    (n : ℕ) (a : compactSupportCohomology R Y n) :
    compactSupportCohomologyToOnePoint R X n
        (compactSupportCohomologyHomeomorphPullback R e n a) =
      relativeSingularCohomologyPullback R ⟨e.onePointCongr, e.onePointCongr.continuous⟩
        (show Set.MapsTo e.onePointCongr ({∞} : Set (OnePoint X))
          ({∞} : Set (OnePoint Y)) from fun x hx ↦ by
            have hx' : x = ∞ := hx
            subst x
            rfl) n
        (compactSupportCohomologyToOnePoint R Y n a) := by
  /- Stage 1: represent a on a compact K. The original finite-point
  inclusions commute with e and its actual OnePoint.map extension.
  Naturality of relative pullback gives the square for the two excision maps.
  Stage 2: invert these specified excision maps, then restrict both pairs
  to their original singleton infinity. This is the claimed equality on
  the representative; the colimit representative property finishes.
  No injectivity or surjectivity of the one-point comparison is assumed. -/
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R Y n a
  let L := homeomorphCompactPreimage e K
  let fX : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let fY : C(Y, OnePoint Y) := ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
  let e₀ : C(X, Y) := ⟨e, e.continuous⟩
  let e₁ : C(OnePoint X, OnePoint Y) := ⟨e.onePointCongr, e.onePointCongr.continuous⟩
  let AX : Set (OnePoint X) := (fX '' (L : Set X))ᶜ
  let AY : Set (OnePoint Y) := (fY '' (K : Set Y))ᶜ
  let hp : Set.MapsTo e₀ ((L : Set X)ᶜ) ((K : Set Y)ᶜ) := fun _ h ↦ h
  have hq : Set.MapsTo e₁ AX AY := by
    rintro z hz ⟨y, hy, heq⟩
    have hpre : e.symm y ∈ (L : Set X) := by
      change e (e.symm y) ∈ (K : Set Y)
      simpa only [e.apply_symm_apply] using hy
    apply hz
    refine ⟨e.symm y, hpre, ?_⟩
    apply e.onePointCongr.injective
    change ((e (e.symm y) : Y) : OnePoint Y) = e₁ z
    rw [e.apply_symm_apply]
    exact heq
  have hInfinity : Set.MapsTo e₁ ({∞} : Set (OnePoint X)) ({∞} : Set (OnePoint Y)) := by
    rintro z rfl
    rfl
  have hAX : ({∞} : Set (OnePoint X)) ⊆ AX := by
    rintro z rfl
    exact OnePoint.infty_notMem_image_coe
  have hAY : ({∞} : Set (OnePoint Y)) ⊆ AY := by
    rintro z rfl
    exact OnePoint.infty_notMem_image_coe
  let p := relativeSingularCohomologyPullback R e₀ hp n
  let q := relativeSingularCohomologyPullback R e₁ hq n
  let qInfinity := relativeSingularCohomologyPullback R e₁ hInfinity n
  let pX := onePointCohomologySupportPullback R X L n
  let pY := onePointCohomologySupportPullback R Y K n
  let rX := relativeSingularCohomologyRestriction R {∞} AX hAX n
  let rY := relativeSingularCohomologyRestriction R {∞} AY hAY n
  have hX : IsIso pX := isIso_onePointCohomologySupportPullback R X L n
  have hY : IsIso pY := isIso_onePointCohomologySupportPullback R Y K n
  -- Finite-point inclusions commute with the same extended homeomorphism before inversion.
  have hsquare : pY ≫ p = q ≫ pX := by
    dsimp only [pY, pX, onePointCohomologySupportPullback, p, q]
    erw [← relativeSingularCohomologyPullback_comp,
      ← relativeSingularCohomologyPullback_comp]
    rfl
  have hinfinity : rY ≫ qInfinity = q ≫ rX :=
    relativeSingularCohomologyPullback_restriction R e₁ hAX hAY hInfinity hq n
  have hmap : p ≫ onePointCohomologySupportMap R X L n =
      onePointCohomologySupportMap R Y K n ≫ qInfinity := by
    change p ≫ ((asIso pX).inv ≫ rX) = ((asIso pY).inv ≫ rY) ≫ qInfinity
    apply (cancel_epi pY).mp
    erw [← Category.assoc pY p, hsquare, Category.assoc q pX,
      (asIso pX).hom_inv_id_assoc, Category.assoc (asIso pY).inv,
      (asIso pY).hom_inv_id_assoc]
    exact hinfinity.symm
  -- Evaluate that square on the original support representative in the colimit.
  rw [compactSupportCohomologyHomeomorphPullback_representative,
    compactSupportCohomologyToOnePoint_representative]
  change compactSupportCohomologyToOnePoint R X n
      (compactSupportCohomologyClass R X L n (p b)) =
    qInfinity (onePointCohomologySupportMap R Y K n b)
  rw [compactSupportCohomologyToOnePoint_representative]
  exact congrArg (fun t ↦ t b) hmap

end AtiyahSinger
