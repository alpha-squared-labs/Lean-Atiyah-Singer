/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyUnionCup
public import AtiyahSinger.Topology.RelativeSingularCohomologyChangeCoefficients

/-!
# Coefficient change for the original open-union cup product

Public module ID: M2075.

The actual integer coefficient map preserves the joint quotient by the two
subspace chain images and commutes with its specified open-union comparison.
The ordered Alexander--Whitney product therefore commutes with coefficient
change into an arbitrary commutative ring. No simplexwise vanishing on the
union or injectivity of the relative-to-ordinary map is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite

universe u

variable (R : Type) [CommRing R]

local notation "RRes" => ModuleCat.restrictScalars (Int.castRingHom R)
local notation "RResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom R)) (ComplexShape.up ℕ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary coefficient map restricts uniquely to the same joint quotient dual. -/
private theorem existsUnique_relativeUnionSingularCochainsChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    ∃! f : relativeUnionSingularCochains ℤ A B ⟶ (RResC).obj (relativeUnionSingularCochains R A B),
      f ≫ (RResC).map
          ((singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A B).op) =
        (singularCochainDualFunctor ℤ).map (relativeUnionSingularChainsProjection ℤ A B).op ≫
          singularCochainsChangeCoefficients R X := by
  /- Restrict the actual ordinary coefficient map to cochains vanishing on
  both subspaces separately. The injective joint quotient dual then checks
  the differential square and fixes the map uniquely. -/
  classical
  let JZ := (singularCochainDualFunctor ℤ).map (relativeUnionSingularChainsProjection ℤ A B).op
  let JQ := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A B).op
  let FX := singularCochainsChangeCoefficients R X
  -- The two original summands vanish separately after their joint quotient projection.
  have hkillLeft (S : Type) [CommRing S] :
      singularSubspaceChains S A ≫ relativeUnionSingularChainsProjection S A B = 0 := by
    have h := congrArg
      (fun g ↦ (biprod.inl : singularChains S A ⟶ singularChains S A ⊞ singularChains S B) ≫ g)
      (cokernel.condition (singularSubspaceSumChains S A B))
    have hs : (biprod.inl : singularChains S A ⟶ singularChains S A ⊞ singularChains S B) ≫
        singularSubspaceSumChains S A B = singularSubspaceChains S A := biprod.inl_desc _ _
    rw [← Category.assoc, hs, comp_zero] at h
    exact h
  have hkillRight (S : Type) [CommRing S] :
      singularSubspaceChains S B ≫ relativeUnionSingularChainsProjection S A B = 0 := by
    have h := congrArg
      (fun g ↦ (biprod.inr : singularChains S B ⟶ singularChains S A ⊞ singularChains S B) ≫ g)
      (cokernel.condition (singularSubspaceSumChains S A B))
    have hs : (biprod.inr : singularChains S B ⟶ singularChains S A ⊞ singularChains S B) ≫
        singularSubspaceSumChains S A B = singularSubspaceChains S B := biprod.inr_desc _ _
    rw [← Category.assoc, hs, comp_zero] at h
    exact h
  have hvanish (n : ℕ) (φ : (relativeUnionSingularCochains ℤ A B).X n) :
      ((singularCochainDualFunctor R).map (singularSubspaceSumChains R A B).op).f n
        (FX.f n (JZ.f n φ)) = 0 := by
    have hside (U : Set X)
        (hU : singularSubspaceChains ℤ U ≫ relativeUnionSingularChainsProjection ℤ A B = 0) :
        ((singularCochainDualFunctor R).map (singularSubspaceChains R U).op).f n
          (FX.f n (JZ.f n φ)) = 0 := by
      have hsource :
          ((singularCochainDualFunctor ℤ).map (singularSubspaceChains ℤ U).op).f n
            (JZ.f n φ) = 0 := by
        change (singularSubspaceChains ℤ U).f n ≫
          ((relativeUnionSingularChainsProjection ℤ A B).f n ≫ φ) = 0
        rw [← Category.assoc, ← HomologicalComplex.comp_f, hU]
        simp
      have hnat := congrArg (fun F ↦ F.f n (JZ.f n φ))
        (singularCochainsChangeCoefficients_naturality R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
      change (singularCochainsChangeCoefficients R U).f n
          (((singularCochainDualFunctor ℤ).map (singularSubspaceChains ℤ U).op).f n
            (JZ.f n φ)) = _ at hnat
      exact hnat.symm.trans ((congrArg ((singularCochainsChangeCoefficients R U).f n)
        hsource).trans (map_zero _))
    have hA : (singularSubspaceChains R A).f n ≫ FX.f n (JZ.f n φ) = 0 :=
      hside A (hkillLeft ℤ)
    have hB : (singularSubspaceChains R B).f n ≫ FX.f n (JZ.f n φ) = 0 :=
      hside B (hkillRight ℤ)
    change (biprod.desc (singularSubspaceChains R A)
      (singularSubspaceChains R B)).f n ≫ FX.f n (JZ.f n φ) = 0
    rw [biprod.desc_eq, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Preadditive.add_comp,
      Category.assoc, Category.assoc, hA, hB, comp_zero, comp_zero, add_zero]
  let component (n : ℕ) : (relativeUnionSingularCochains ℤ A B).X n →ₛₗ[Int.castRingHom R]
      (relativeUnionSingularCochains R A B).X n :=
    { toFun := fun φ ↦ (relativeUnionSingularCochainEquiv R A B n).symm
        ⟨FX.f n (JZ.f n φ), hvanish n φ⟩
      map_add' := by
        intro φ ψ
        apply (relativeUnionSingularCochainEquiv R A B n).injective
        simp only [map_add, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        rfl
      map_smul' := by
        intro r φ
        apply (relativeUnionSingularCochainEquiv R A B n).injective
        simp only [map_smul, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        change FX.f n (JZ.f n (r • φ)) =
          (r : R) • (show (singularCochains R X).X n from FX.f n (JZ.f n φ))
        rw [map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul] }
  have hcomponent (n : ℕ) (φ : (relativeUnionSingularCochains ℤ A B).X n) :
      JQ.f n (component n φ) = FX.f n (JZ.f n φ) :=
    congrArg Subtype.val ((relativeUnionSingularCochainEquiv R A B n).apply_symm_apply _)
  -- The injective quotient-dual inclusion checks all differential squares.
  let F : relativeUnionSingularCochains ℤ A B ⟶ (RResC).obj (relativeUnionSingularCochains R A B) :=
    { f := fun n ↦ ModuleCat.semilinearMapAddEquiv (Int.castRingHom R)
        ((relativeUnionSingularCochains ℤ A B).X n)
        ((relativeUnionSingularCochains R A B).X n) (component n)
      comm' := by
        intro n m _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply (relativeUnionSingularCochainEquiv R A B m).injective
        apply Subtype.ext
        change JQ.f m ((relativeUnionSingularCochains R A B).d n m (component n φ)) =
          JQ.f m (component m ((relativeUnionSingularCochains ℤ A B).d n m φ))
        have hJQ := congrArg (fun f ↦ f (component n φ)) (JQ.comm n m)
        have hJZ := congrArg (fun f ↦ f φ) (JZ.comm n m)
        have hFX := congrArg (fun f ↦ f (JZ.f n φ)) (FX.comm n m)
        exact hJQ.symm.trans
          ((congrArg ((singularCochains R X).d n m) (hcomponent n φ)).trans
            (hFX.trans ((congrArg (FX.f m) hJZ).trans
              (hcomponent m ((relativeUnionSingularCochains ℤ A B).d n m φ)).symm))) }
  refine ⟨F, ?_, ?_⟩
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact hcomponent n
  · -- The original relative cochain is determined by its ordinary inclusion.
    intro G hG
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply (relativeUnionSingularCochainEquiv R A B n).injective
    apply Subtype.ext
    exact (congrArg (fun f ↦ f.f n φ) hG).trans (hcomponent n φ).symm

/-- The actual relative coefficient change fixed by the original ordinary cochain square. -/
private def relativeUnionSingularCochainsChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    relativeUnionSingularCochains ℤ A B ⟶ (RResC).obj (relativeUnionSingularCochains R A B) :=
  Classical.choose (existsUnique_relativeUnionSingularCochainsChangeCoefficients R A B).exists

/-- Relative coefficient change followed by the canonical homology comparison. -/
private def relativeUnionSingularCohomologyChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    relativeUnionSingularCohomology ℤ A B n ⟶
      (RRes).obj (relativeUnionSingularCohomology R A B n) :=
  HomologicalComplex.homologyMap (relativeUnionSingularCochainsChangeCoefficients R A B) n ≫
    (((relativeUnionSingularCochains R A B).sc n).mapHomologyIso RRes).hom


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Integer coefficient change preserves the actual ordered cup product with open union support. -/
theorem relativeSingularCohomologyChangeCoefficients_unionCup
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : relativeSingularCohomology ℤ A p) (b : relativeSingularCohomology ℤ B q) :
    relativeSingularCohomologyChangeCoefficients R (A ∪ B) (p + q)
        (relativeSingularCohomologyUnionCup ℤ A B hA hB p q a b) =
      relativeSingularCohomologyUnionCup R A B hA hB p q
        (relativeSingularCohomologyChangeCoefficients R A p a)
        (relativeSingularCohomologyChangeCoefficients R B q b) := by
  /- First compare the actual joint-to-union quotient maps after coefficient
  change. Their injective quotient-dual inclusions identify the entire cochain
  square. On cocycles the joint products then agree by the original ordinary
  AW formula. Finally cancel the specified open-union cohomology comparison. -/
  let F := singularCochainsChangeCoefficients R X
  let Q := relativeUnionSingularCochainsChangeCoefficients R A B
  let U := relativeSingularCochainsChangeCoefficients R (A ∪ B)
  let JZ := (singularCochainDualFunctor ℤ).map
    (relativeUnionSingularChainsProjection ℤ A B).op
  let JR := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsProjection R A B).op
  let KZ := (singularCochainDualFunctor ℤ).map
    (relativeUnionSingularChainsToRelative ℤ A B).op
  let KR := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsToRelative R A B).op
  have hQ := (existsUnique_relativeUnionSingularCochainsChangeCoefficients R A B).exists.choose_spec
  have hU := (existsUnique_relativeSingularCochainsChangeCoefficients R (A ∪ B)).exists.choose_spec
  have hprojection (S : Type) [CommRing S] :
      (singularCochainDualFunctor S).map (relativeUnionSingularChainsToRelative S A B).op ≫
          (singularCochainDualFunctor S).map (relativeUnionSingularChainsProjection S A B).op =
        (singularCochainDualFunctor S).map (relativeSingularChainsProjection S (A ∪ B)).op := by
    rw [← Functor.map_comp, ← op_comp]
    have hchain : relativeUnionSingularChainsProjection S A B ≫
        relativeUnionSingularChainsToRelative S A B =
          relativeSingularChainsProjection S (A ∪ B) := by
      simp [relativeUnionSingularChainsProjection, relativeUnionSingularChainsToRelative]
    rw [hchain]
  -- The same ordinary inclusion detects the coefficient square before taking cohomology.
  have hsquare : KZ ≫ Q = U ≫ (RResC).map KR := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply (relativeUnionSingularCochainEquiv R A B n).injective
    apply Subtype.ext
    change JR.f n (Q.f n (KZ.f n φ)) = JR.f n (KR.f n (U.f n φ))
    have h₁ := congrArg (fun G ↦ G.f n (KZ.f n φ)) hQ
    have h₂ := congrArg (fun G ↦ G.f n φ) (hprojection ℤ)
    have h₃ := congrArg (fun G ↦ G.f n φ) hU
    have h₄ := congrArg (fun G ↦ G.f n (U.f n φ)) (hprojection R)
    exact h₁.trans ((congrArg (F.f n) h₂).trans (h₃.symm.trans h₄.symm))
  have hcomparison (n : ℕ) (z : relativeSingularCohomology ℤ (A ∪ B) n) :
      relativeUnionCohomologyComparison R A B n
          (relativeSingularCohomologyChangeCoefficients R (A ∪ B) n z) =
        relativeUnionSingularCohomologyChangeCoefficients R A B n
          (relativeUnionCohomologyComparison ℤ A B n z) := by
    have hmap := congrArg (fun G ↦ HomologicalComplex.homologyMap G n) hsquare
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
    have hv := congrArg (fun G ↦ G z) hmap
    change HomologicalComplex.homologyMap Q n (HomologicalComplex.homologyMap KZ n z) =
      HomologicalComplex.homologyMap ((RResC).map KR) n
        (HomologicalComplex.homologyMap U n z) at hv
    have hnat := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℕ) n).map KR) RRes
    have hn := congrArg (fun G ↦ G (HomologicalComplex.homologyMap U n z)) hnat
    change (((relativeUnionSingularCochains R A B).sc n).mapHomologyIso RRes).hom
        (HomologicalComplex.homologyMap ((RResC).map KR) n
          (HomologicalComplex.homologyMap U n z)) =
      relativeUnionCohomologyComparison R A B n
        (relativeSingularCohomologyChangeCoefficients R (A ∪ B) n z) at hn
    exact ((congrArg
      (((relativeUnionSingularCochains R A B).sc n).mapHomologyIso RRes).hom hv).trans hn).symm
  -- Choose original relative cocycles, without changing any open support condition.
  have hrep (S : Type) [CommRing S] (C : CochainComplex (ModuleCat.{u} S) ℕ)
      (n : ℕ) (z : C.homology n) :
      ∃ α : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ α) = z := by
    obtain ⟨α, hα⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom z)
    refine ⟨α, ?_⟩
    rw [hα]
    exact congrArg (fun G ↦ G z) (C.sc n).moduleCatHomologyIso.hom_inv_id
  obtain ⟨α, hα⟩ := hrep ℤ (relativeSingularCochains ℤ A) p a
  obtain ⟨β, hβ⟩ := hrep ℤ (relativeSingularCochains ℤ B) q b
  change relativeSingularCocycleClass ℤ A p α = a at hα
  change relativeSingularCocycleClass ℤ B q β = b at hβ
  let αR := relativeSingularCocycleChangeCoefficients R A p α
  let βR := relativeSingularCocycleChangeCoefficients R B q β
  have hjoint (S : Type) [CommRing S]
      (x : (relativeSingularCochains S A).X p) (y : (relativeSingularCochains S B).X q) :
      ((singularCochainDualFunctor S).map
          (relativeUnionSingularChainsProjection S A B).op).f (p + q)
          (relativeUnionSingularCochainCup S A B p q x y) =
        singularCochainCup S X p q
          (((singularCochainDualFunctor S).map (relativeSingularChainsProjection S A).op).f p x)
          (((singularCochainDualFunctor S).map (relativeSingularChainsProjection S B).op).f q y) :=
    congrArg Subtype.val ((relativeUnionSingularCochainEquiv S A B (p + q)).apply_symm_apply _)
  -- Cancel precisely the open-union comparison used in the definition of both products.
  apply (relativeUnionCohomologyComparison_bijective R A B hA hB (p + q)).injective
  rw [hcomparison, ← hα, ← hβ, relativeSingularCohomologyUnionCup_cocycleClass,
    relativeSingularCohomologyChangeCoefficients_cocycleClass,
    relativeSingularCohomologyChangeCoefficients_cocycleClass,
    relativeSingularCohomologyUnionCup_cocycleClass]
  apply homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R)
    (relativeUnionSingularCochains ℤ A B) (relativeUnionSingularCochains R A B) Q (p + q)
  apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
  apply Subtype.ext
  change JR.f (p + q) (Q.f (p + q) (relativeUnionSingularCochainCup ℤ A B p q α.val β.val)) =
    JR.f (p + q) (relativeUnionSingularCochainCup R A B p q αR.val βR.val)
  have hQvalue := congrArg
    (fun G ↦ G.f (p + q) (relativeUnionSingularCochainCup ℤ A B p q α.val β.val)) hQ
  have hAvalue := congrArg (fun G ↦ G.f p α.val)
    (existsUnique_relativeSingularCochainsChangeCoefficients R A).exists.choose_spec
  have hBvalue := congrArg (fun G ↦ G.f q β.val)
    (existsUnique_relativeSingularCochainsChangeCoefficients R B).exists.choose_spec
  change ((singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R A).op).f p αR.val =
    F.f p (((singularCochainDualFunctor ℤ).map
      (relativeSingularChainsProjection ℤ A).op).f p α.val) at hAvalue
  change ((singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R B).op).f q βR.val =
    F.f q (((singularCochainDualFunctor ℤ).map
      (relativeSingularChainsProjection ℤ B).op).f q β.val) at hBvalue
  have hcup := singularCochainsChangeCoefficients_cup R X p q
    (((singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op).f p α.val)
    (((singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ B).op).f q β.val)
  exact hQvalue.trans ((congrArg (F.f (p + q)) (hjoint ℤ α.val β.val)).trans
    (hcup.trans ((congrArg₂ (fun (x : (singularCochains R X).X p)
      (y : (singularCochains R X).X q) ↦ singularCochainCup R X p q x y)
        hAvalue.symm hBvalue.symm).trans
      (hjoint R αR.val βR.val).symm)))

end AtiyahSinger
