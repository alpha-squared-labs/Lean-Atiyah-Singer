/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyRationalization
public import AtiyahSinger.Topology.RelativeCohomologyCup

/-!
# Integral-to-rational coefficients on the original relative cochains

Public module ID: M2068.

The existing relative cochain complex is the dual of
the original relative singular chain quotient. Its canonical inclusion in
ordinary cochains identifies it with the cochains vanishing on the subspace.
The fixed ordinary coefficient inclusion preserves that vanishing condition,
and hence specifies a unique coefficient map on the original relative complex.
Homology and the standard restriction-of-scalars comparison give the actual
relative cohomology map used below.

Sources: Hatcher, Algebraic Topology, sections 3.1--3.2, coefficient
homomorphisms, relative cochains and the Alexander--Whitney product;
Milnor--Stasheff, Characteristic Classes, Theorem 10.4, for the later
application to Thom classes. This module only constructs coefficient change
and its naturality and product laws. It asserts neither a tensor-product
description of rational cohomology nor that every rational class is the
image of an integral class.

The continuous maps, subspaces, quotient projections and cup order are
unchanged. Subspaces need not be closed; bases need not be compact,
paracompact, connected or nonempty. Normalized rational orientations and
Thom classes are subsequent applications, not premises of these maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

local notation "ℚRes" => ModuleCat.restrictScalars (Int.castRingHom ℚ)
local notation "ℚResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom ℚ)) (ComplexShape.up ℕ)

/-- The original ordinary coefficient map uniquely restricts to the actual relative cochains. -/
theorem existsUnique_relativeSingularCochainsRationalization
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    ∃! f : relativeSingularCochains ℤ A ⟶ (ℚResC).obj (relativeSingularCochains ℚ A),
      f ≫ (ℚResC).map
          ((singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op) =
        (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op ≫
          singularCochainsRationalization X := by
  /- Stage 1: relativeSingularCochainEquiv identifies each original relative
  cochain with its actual ordinary cochain vanishing on A. The specified
  singularCochainsRationalization changes each original simplex value by
  integer inclusion. In particular, a zero evaluation on a simplex of A
  stays zero. Its rational cochain therefore belongs to the same relative
  kernel, and the inverse relative cochain equivalence gives the required
  degreewise map, linear over the original integer coefficients.
  Stage 2: both original inclusions into ordinary cochains commute with
  the differentials. The ordinary rationalization does as well. Their
  injective degreewise inclusions therefore show that the restricted maps
  commute with differentials, giving the displayed cochain-map square.
  Stage 3: an original relative cochain is determined by its composite
  with the relative chain quotient projection. Thus the square fixes every
  degreewise value and proves uniqueness of the whole map. No generator
  of a cohomology group or independent rational scale is chosen. -/
  classical
  let JZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JQ := (singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op
  let FX := singularCochainsRationalization X
  -- Pullback to A evaluates on the original simplex included into X.
  have hpull (R : Type) [CommRing R] (n : ℕ) (χ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋n⦌)) :
      singularCochainEquiv R A n
        (((singularCochainDualFunctor R).map (singularSubspaceChains R A).op).f n χ) σ =
          singularCochainEquiv R X n χ
            ((TopCat.toSSet.map (TopCat.ofHom
              (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))).app (op ⦋n⦌) σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X n ⟶ singularCoefficient R from χ)
      (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom
          (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))))
            (singularCoefficient R)).f n) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  -- Integer inclusion preserves the actual vanishing kernel on A.
  have hvanish (n : ℕ) (φ : (relativeSingularCochains ℤ A).X n) :
      ((singularCochainDualFunctor ℚ).map (singularSubspaceChains ℚ A).op).f n
        (FX.f n (JZ.f n φ)) = 0 := by
    apply (singularCochainEquiv ℚ A n).injective
    funext σ
    let τ := (TopCat.toSSet.map (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))).app (op ⦋n⦌) σ
    have hz := (relativeSingularCochainEquiv ℤ A n φ).property
    have hvalue := congrArg (fun χ ↦ singularCochainEquiv ℤ A n χ σ) hz
    have hzero : singularCochainEquiv ℤ X n (JZ.f n φ) τ = 0 :=
      (hpull ℤ n (JZ.f n φ) σ).symm.trans
        (hvalue.trans (congrFun (singularCochainEquiv ℤ A n).map_zero σ))
    have hcoeff := Classical.choose_spec (existsUnique_singularCochainsRationalization X).exists
      n (JZ.f n φ) τ
    have hcast := congrArg
      (fun z : ULift.{u} ℤ ↦ (ULift.up (z.down : ℚ) : ULift.{u} ℚ)) hzero
    exact (hpull ℚ n (FX.f n (JZ.f n φ)) σ).trans
      (hcoeff.trans (hcast.trans (congrFun (singularCochainEquiv ℚ A n).map_zero σ).symm))
  let component (n : ℕ) : (relativeSingularCochains ℤ A).X n →ₗ[ℤ]
      (relativeSingularCochains ℚ A).X n :=
    { toFun := fun φ ↦ (relativeSingularCochainEquiv ℚ A n).symm
        ⟨FX.f n (JZ.f n φ), hvanish n φ⟩
      map_add' := by
        intro φ ψ
        apply (relativeSingularCochainEquiv ℚ A n).injective
        simp only [map_add, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        rfl
      map_smul' := by
        intro r φ
        apply (relativeSingularCochainEquiv ℚ A n).injective
        simp only [map_zsmul, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        change FX.f n (JZ.f n (r • φ)) = r • FX.f n (JZ.f n φ)
        rw [map_zsmul, map_zsmul] }
  have hcomponent (n : ℕ) (φ : (relativeSingularCochains ℤ A).X n) :
      JQ.f n (component n φ) = FX.f n (JZ.f n φ) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv ℚ A n).apply_symm_apply _)
  -- The injective quotient-dual inclusion checks all differential squares.
  let F : relativeSingularCochains ℤ A ⟶ (ℚResC).obj (relativeSingularCochains ℚ A) :=
    { f := fun n ↦ ModuleCat.ofHom (component n)
      comm' := by
        intro n m _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply (relativeSingularCochainEquiv ℚ A m).injective
        apply Subtype.ext
        change JQ.f m ((relativeSingularCochains ℚ A).d n m (component n φ)) =
          JQ.f m (component m ((relativeSingularCochains ℤ A).d n m φ))
        have hJQ := congrArg (fun f ↦ f (component n φ)) (JQ.comm n m)
        have hJZ := congrArg (fun f ↦ f φ) (JZ.comm n m)
        have hFX := congrArg (fun f ↦ f (JZ.f n φ)) (FX.comm n m)
        exact hJQ.symm.trans
          ((congrArg ((singularCochains ℚ X).d n m) (hcomponent n φ)).trans
            (hFX.trans ((congrArg (FX.f m) hJZ).trans
              (hcomponent m ((relativeSingularCochains ℤ A).d n m φ)).symm))) }
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
    apply (relativeSingularCochainEquiv ℚ A n).injective
    apply Subtype.ext
    exact (congrArg (fun f ↦ f.f n φ) hG).trans (hcomponent n φ).symm

/-- The actual relative coefficient inclusion fixed by the original ordinary cochain square. -/
def relativeSingularCochainsRationalization
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    relativeSingularCochains ℤ A ⟶ (ℚResC).obj (relativeSingularCochains ℚ A) :=
  Classical.choose (existsUnique_relativeSingularCochainsRationalization A).exists

/-- Relative coefficient inclusion followed by the canonical homology comparison. -/
def relativeSingularCohomologyRationalization
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    relativeSingularCohomology ℤ A n ⟶ (ℚRes).obj (relativeSingularCohomology ℚ A n) :=
  HomologicalComplex.homologyMap (relativeSingularCochainsRationalization A) n ≫
    (((relativeSingularCochains ℚ A).sc n).mapHomologyIso ℚRes).hom

/-- Relative coefficient inclusion commutes with pullback along the same continuous pair map. -/
theorem relativeSingularCohomologyRationalization_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ)
    (b : relativeSingularCohomology ℤ B n) :
    relativeSingularCohomologyRationalization A n
        (relativeSingularCohomologyPullback ℤ f hf n b) =
      relativeSingularCohomologyPullback ℚ f hf n
        (relativeSingularCohomologyRationalization B n b) := by
  /- Stage 1: the ordinary coefficient map commutes with precomposition
  by the same continuous f, since both composites evaluate a cochain on
  f composed with the original simplex and then include that integer in Q.
  Stage 2: hf sends simplices in A to simplices in B. Consequently the
  original relative pullbacks preserve the vanishing kernels. Compare
  the composites after the injective original cochain inclusions; their
  prescribed coefficient squares give the same relative cochain map.
  Stage 3: apply homology and the natural restriction-of-scalars homology
  comparison. This gives the formula on the original class b, with the
  same f, A, B and hf rather than separately selected pair maps. -/
  have hordinarySquare {V W : Type u} [TopologicalSpace V] [TopologicalSpace W]
      (g : C(V, W)) :
      (singularCochainsFunctor ℤ).map (TopCat.ofHom g).op ≫
          singularCochainsRationalization V =
        singularCochainsRationalization W ≫ (ℚResC).map
          ((singularCochainsFunctor ℚ).map (TopCat.ofHom g).op) := by
    -- Check coefficient inclusion on the very simplex composed with the given map.
    let PZ := (singularCochainsFunctor ℤ).map (TopCat.ofHom g).op
    let PQ := (singularCochainsFunctor ℚ).map (TopCat.ofHom g).op
    have heval (Z : Type u) [TopologicalSpace Z] :=
      Classical.choose_spec (existsUnique_singularCochainsRationalization Z).exists
    have hpull (R : Type) [CommRing R] (k : ℕ) (χ : (singularCochains R W).X k)
        (σ : (TopCat.toSSet.obj (TopCat.of V)).obj (op ⦋k⦌)) :
        singularCochainEquiv R V k
          (((singularCochainsFunctor R).map (TopCat.ofHom g).op).f k χ) σ =
            singularCochainEquiv R W k χ
              ((TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋k⦌) σ) := by
      change (show ((TopCat.toSSet.obj (TopCat.of W)).chainComplex
        (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
        (((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex σ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
            (singularCoefficient R)).f k) (ULift.up 1)) = _
      rw [SSet.ι_chainComplexMap_f]
      rfl
    have hsquare : PZ ≫ singularCochainsRationalization V =
        singularCochainsRationalization W ≫ (ℚResC).map PQ := by
      apply HomologicalComplex.Hom.ext
      funext k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro χ
      apply (singularCochainEquiv ℚ V k).injective
      funext σ
      change singularCochainEquiv ℚ V k
        ((singularCochainsRationalization V).f k (PZ.f k χ)) σ =
          singularCochainEquiv ℚ V k
            (PQ.f k ((singularCochainsRationalization W).f k χ)) σ
      let castValue (v : ULift.{u} ℤ) : ULift.{u} ℚ := ULift.up (v.down : ℚ)
      exact (heval V k (PZ.f k χ) σ).trans
        ((congrArg castValue (hpull ℤ k χ σ)).trans
          ((heval W k χ ((TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋k⦌) σ)).symm.trans
            (hpull ℚ k ((singularCochainsRationalization W).f k χ) σ).symm))
    exact hsquare
  -- The two pair pullbacks commute with their original quotient-dual inclusions.
  let PZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsMap ℤ f hf).op
  let PQ := (singularCochainDualFunctor ℚ).map (relativeSingularChainsMap ℚ f hf).op
  let JZA := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JZB := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ B).op
  let JQA := (singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op
  let JQB := (singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ B).op
  let OZ := (singularCochainsFunctor ℤ).map (TopCat.ofHom f).op
  let OQ := (singularCochainsFunctor ℚ).map (TopCat.ofHom f).op
  let FA := relativeSingularCochainsRationalization A
  let FB := relativeSingularCochainsRationalization B
  have hprojection (R : Type) [CommRing R] :
      (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op ≫
          (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op =
        (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op ≫
          (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
    have hchain : relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
        (singularChainsFunctor R).map (TopCat.ofHom f) ≫
          relativeSingularChainsProjection R B := by
      simp [relativeSingularChainsProjection, relativeSingularChainsMap]
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ =
      (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf).op =
        (singularCochainDualFunctor R).map
          ((singularChainsFunctor R).map (TopCat.ofHom f) ≫
            relativeSingularChainsProjection R B).op
    rw [hchain]
  have hFA := Classical.choose_spec (existsUnique_relativeSingularCochainsRationalization A).exists
  have hFB := Classical.choose_spec (existsUnique_relativeSingularCochainsRationalization B).exists
  have hsquare : PZ ≫ FA = FB ≫ (ℚResC).map PQ := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    apply (relativeSingularCochainEquiv ℚ A k).injective
    apply Subtype.ext
    change JQA.f k (FA.f k (PZ.f k χ)) = JQA.f k (PQ.f k (FB.f k χ))
    have h₁ := congrArg (fun F ↦ F.f k (PZ.f k χ)) hFA
    have h₂ := congrArg (fun F ↦ F.f k χ) (hprojection ℤ)
    have h₃ := congrArg (fun F ↦ F.f k (JZB.f k χ)) (hordinarySquare f)
    have h₄ := congrArg (fun F ↦ F.f k χ) hFB
    have h₅ := congrArg (fun F ↦ F.f k (FB.f k χ)) (hprojection ℚ)
    exact h₁.trans ((congrArg ((singularCochainsRationalization X).f k) h₂).trans
      (h₃.trans ((congrArg (OQ.f k) h₄.symm).trans h₅.symm)))
  -- Pass through homology and its natural comparison for restriction of scalars.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F b) hmap
  change HomologicalComplex.homologyMap FA n (HomologicalComplex.homologyMap PZ n b) =
    HomologicalComplex.homologyMap ((ℚResC).map PQ) n
      (HomologicalComplex.homologyMap FB n b) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℚ)
      (ComplexShape.up ℕ) n).map PQ) ℚRes
  have hnatValue := congrArg (fun F ↦ F (HomologicalComplex.homologyMap FB n b)) hnat
  change (((relativeSingularCochains ℚ A).sc n).mapHomologyIso ℚRes).hom
    (HomologicalComplex.homologyMap ((ℚResC).map PQ) n
      (HomologicalComplex.homologyMap FB n b)) =
        relativeSingularCohomologyPullback ℚ f hf n
          (relativeSingularCohomologyRationalization B n b) at hnatValue
  exact (congrArg (((relativeSingularCochains ℚ A).sc n).mapHomologyIso ℚRes).hom
    hvalue).trans hnatValue

/-- Forgetting the original relative condition commutes with normalized coefficient change. -/
theorem relativeSingularCohomologyRationalization_toOrdinary
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (a : relativeSingularCohomology ℤ A n) :
    singularCohomologyRationalization X n (relativeSingularCohomologyToOrdinary ℤ A n a) =
      relativeSingularCohomologyToOrdinary ℚ A n
        (relativeSingularCohomologyRationalization A n a) := by
  /- The unique cochain map was chosen to commute with precisely the
  duals of the original relative quotient projections. Those dual maps
  induce relativeSingularCohomologyToOrdinary. Apply homology to the
  defining square, then use naturality of the canonical restriction-of-
  scalars comparison to identify its two targets with the original
  rational cohomology modules. Evaluate on a to obtain this equality. -/
  -- Use exactly the square specifying the original relative coefficient map.
  let F := relativeSingularCochainsRationalization A
  let JZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JQ := (singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op
  have hsquare : JZ ≫ singularCochainsRationalization X = F ≫ (ℚResC).map JQ :=
    (Classical.choose_spec (existsUnique_relativeSingularCochainsRationalization A).exists).symm
  have hmap := congrArg (fun G ↦ HomologicalComplex.homologyMap G n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun G ↦ G a) hmap
  change HomologicalComplex.homologyMap (singularCochainsRationalization X) n
    (HomologicalComplex.homologyMap JZ n a) =
      HomologicalComplex.homologyMap ((ℚResC).map JQ) n
        (HomologicalComplex.homologyMap F n a) at hvalue
  -- The native comparison returns to the same rational ordinary homology object.
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℚ)
      (ComplexShape.up ℕ) n).map JQ) ℚRes
  have hnatValue := congrArg (fun G ↦ G (HomologicalComplex.homologyMap F n a)) hnat
  change (((singularCochains ℚ X).sc n).mapHomologyIso ℚRes).hom
    (HomologicalComplex.homologyMap ((ℚResC).map JQ) n
      (HomologicalComplex.homologyMap F n a)) =
        relativeSingularCohomologyToOrdinary ℚ A n
          (relativeSingularCohomologyRationalization A n a) at hnatValue
  exact (congrArg (((singularCochains ℚ X).sc n).mapHomologyIso ℚRes).hom hvalue).trans
    hnatValue

/-- Coefficient inclusion preserves the original ordinary-relative cup action and its order. -/
theorem relativeSingularCohomologyRationalization_action
    {X : Type u} [TopologicalSpace X] (A : Set X) (p q : ℕ)
    (a : singularCohomology ℤ X p) (b : relativeSingularCohomology ℤ A q) :
    relativeSingularCohomologyRationalization A (p + q)
        (relativeSingularCohomologyAction ℤ A p q a b) =
      relativeSingularCohomologyAction ℚ A p q
        (singularCohomologyRationalization X p a)
        (relativeSingularCohomologyRationalization A q b) := by
  /- Stage 1: choose original cocycles for a and b. The relative cocycle
  is an ordinary cocycle vanishing on A through the same quotient-dual
  inclusion. The original Alexander--Whitney formula evaluates a on the
  front face and b on the back face. Integer inclusion preserves this
  product, the face maps and the vanishing condition on A.
  Stage 2: the unique relative coefficient square identifies that actual
  rationalized product with the product of the two coefficient images.
  Passing through the original cocycle/coboundary quotients and canonical
  homology comparisons gives the stated formula. The ordinary factor
  remains first and the relative factor second; no graded interchange,
  degree subtraction, excision or tensor-cohomology isomorphism is used. -/
  -- Retain the original quotient classes and the mapped homology comparison.
  have hclass (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      (C : CochainComplex (ModuleCat.{u} R) ℕ)
      (D : CochainComplex (ModuleCat.{u} S) ℕ)
      (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
        (ComplexShape.up ℕ)).obj D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      ((D.sc n).mapHomologyIso (ModuleCat.restrictScalars ι)).hom
        (HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a))) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData
        ((D.sc n).moduleCatLeftHomologyData.map (ModuleCat.restrictScalars ι))
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap, (D.sc n).moduleCatLeftHomologyData.mapHomologyIso_eq (ModuleCat.restrictScalars ι)]
    let J := ((D.sc n).moduleCatLeftHomologyData.map (ModuleCat.restrictScalars ι)).homologyIso
    change (D.sc n).moduleCatHomologyIso.inv
      (J.hom (J.inv (G.φH ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))))) = _
    have hcancel : (C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc n).moduleCatToCycles.range.mkQ a :=
      congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
        (C.sc n).moduleCatHomologyIso.inv_hom_id
    rw [hcancel]
    have hJ : J.hom (J.inv (G.φH ((C.sc n).moduleCatToCycles.range.mkQ a))) =
        G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) :=
      congrArg (fun f ↦ f (G.φH ((C.sc n).moduleCatToCycles.range.mkQ a))) J.inv_hom_id
    rw [hJ, hquot]
  have hrep (R : Type) [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  have hcycles (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      (C : CochainComplex (ModuleCat.{u} R) ℕ)
      (D : CochainComplex (ModuleCat.{u} S) ℕ)
      (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
        (ComplexShape.up ℕ)).obj D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
    rfl
  -- Coefficient inclusion preserves the product on the same front and back faces.
  let F := singularCochainsRationalization X
  have heval := Classical.choose_spec (existsUnique_singularCochainsRationalization X).exists
  have hcup (a : (singularCochains ℤ X).X p) (b : (singularCochains ℤ X).X q) :
      F.f (p + q) (singularCochainCup ℤ X p q a b) =
        singularCochainCup ℚ X p q (F.f p a) (F.f q b) := by
    have hevalCup (R : Type) [CommRing R] (a : (singularCochains R X).X p)
        (b : (singularCochains R X).X q)
        (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋p + q⦌)) :
        singularCochainEquiv R X (p + q) (singularCochainCup R X p q a b) σ =
          singularCochainEquiv R X p a
            ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op σ) *
          singularCochainEquiv R X q b
            ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ) :=
      congrFun ((singularCochainEquiv R X (p + q)).apply_symm_apply _) σ
    apply (singularCochainEquiv ℚ X (p + q)).injective
    funext σ
    let castValue (v : ULift.{u} ℤ) : ULift.{u} ℚ := ULift.up (v.down : ℚ)
    let front := (TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op σ
    let back := (TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ
    have hmul : castValue (singularCochainEquiv ℤ X p a front *
        singularCochainEquiv ℤ X q b back) =
          castValue (singularCochainEquiv ℤ X p a front) *
            castValue (singularCochainEquiv ℤ X q b back) := by
      apply ULift.ext
      simp [castValue]
    exact (heval (p + q) (singularCochainCup ℤ X p q a b) σ).trans
      ((congrArg castValue (hevalCup ℤ a b σ)).trans
        (hmul.trans ((congrArg₂ (· * ·) (heval p a front).symm
          (heval q b back).symm).trans (hevalCup ℚ (F.f p a) (F.f q b) σ).symm)))
  -- Compare the ordered relative action after its injective ordinary inclusion.
  let FR := relativeSingularCochainsRationalization A
  let JZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JQ := (singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op
  have hsquare := Classical.choose_spec
    (existsUnique_relativeSingularCochainsRationalization A).exists
  have haction (R : Type) [CommRing R] (a : (singularCochains R X).X p)
      (b : (relativeSingularCochains R A).X q) :
      ((singularCochainDualFunctor R).map
          (relativeSingularChainsProjection R A).op).f (p + q)
        (relativeSingularCochainAction R A p q a b) =
          singularCochainCup R X p q a
            (((singularCochainDualFunctor R).map
              (relativeSingularChainsProjection R A).op).f q b) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A (p + q)).apply_symm_apply _)
  have hrelative (a : (singularCochains ℤ X).X p)
      (b : (relativeSingularCochains ℤ A).X q) :
      FR.f (p + q) (relativeSingularCochainAction ℤ A p q a b) =
        relativeSingularCochainAction ℚ A p q (F.f p a) (FR.f q b) := by
    apply (relativeSingularCochainEquiv ℚ A (p + q)).injective
    apply Subtype.ext
    have h₁ := congrArg
      (fun G ↦ G.f (p + q) (relativeSingularCochainAction ℤ A p q a b)) hsquare
    have h₂ := haction ℤ a b
    have h₃ := hcup a (JZ.f q b)
    have h₄ := congrArg (fun G ↦ G.f q b) hsquare
    have h₅ := haction ℚ (F.f p a) (FR.f q b)
    exact h₁.trans ((congrArg (F.f (p + q)) h₂).trans
      (h₃.trans ((congrArg (singularCochainCup ℚ X p q (F.f p a)) h₄.symm).trans h₅.symm)))
  -- Choose original ordinary and relative cocycles and descend the same cochain identity.
  obtain ⟨α, hα⟩ := hrep ℤ (singularCochains ℤ X) p a
  obtain ⟨β, hβ⟩ := hrep ℤ (relativeSingularCochains ℤ A) q b
  obtain ⟨αQ, hαQ⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ)
    (singularCochains ℤ X) (singularCochains ℚ X) F p α
  obtain ⟨βQ, hβQ⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ)
    (relativeSingularCochains ℤ A) (relativeSingularCochains ℚ A) FR q β
  have hαclass : singularCohomologyRationalization X p (singularCocycleClass ℤ X p α) =
      singularCocycleClass ℚ X p αQ :=
    hclass ℤ ℚ (Int.castRingHom ℚ) _ _ F p α αQ hαQ.symm
  have hβclass : relativeSingularCohomologyRationalization A q
      (relativeSingularCocycleClass ℤ A q β) = relativeSingularCocycleClass ℚ A q βQ :=
    hclass ℤ ℚ (Int.castRingHom ℚ) _ _ FR q β βQ hβQ.symm
  have hproduct : relativeSingularCohomologyRationalization A (p + q)
      (relativeSingularCocycleClass ℤ A (p + q)
        (relativeSingularCocycleAction ℤ A p q α β)) =
      relativeSingularCocycleClass ℚ A (p + q)
        (relativeSingularCocycleAction ℚ A p q αQ βQ) := by
    apply hclass ℤ ℚ (Int.castRingHom ℚ) _ _ FR (p + q)
    change FR.f (p + q) (relativeSingularCochainAction ℤ A p q α.val β.val) =
      relativeSingularCochainAction ℚ A p q αQ.val βQ.val
    rw [hαQ, hβQ]
    exact hrelative α.val β.val
  change singularCocycleClass ℤ X p α = a at hα
  change relativeSingularCocycleClass ℤ A q β = b at hβ
  rw [← hα, ← hβ, relativeSingularCohomologyAction_cocycleClass, hαclass, hβclass,
    relativeSingularCohomologyAction_cocycleClass]
  exact hproduct

end AtiyahSinger
