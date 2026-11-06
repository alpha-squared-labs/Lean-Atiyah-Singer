/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyCup
public import AtiyahSinger.Topology.RelativeUnionCochains

/-!
# The original cup product for two open relative subspaces

Public module ID: M2072.

Hatcher, Algebraic Topology, Section 3.2, p.209. The actual
front/back product descends on both original relative cocycle quotients
to the cohomology of C_*(X)/(C_*(A)+C_*(B)). The inverse of the specified
small-chain comparison then gives H^p(X,A) x H^q(X,B) -> H^(p+q)(X,A union B)
when both subspaces are open.

Every data map is fixed by the original chain quotients, original cochain
formula and canonical homology comparisons. No arbitrary relative lift is
selected and no assertion of simplexwise union vanishing is made. The product
is natural for the same maps of pairs. Restricting its relative condition to
B agrees with the existing ordinary-relative action, after forgetting only
the first factor's relative condition. This is the support comparison needed
by the compact-support Thom map over a noncompact base.

No manifold, separation, nontrivial-ring or positive-degree assumption is
used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The standard two-relative cup product through the actual joint quotient and open comparison. -/
def relativeSingularCohomologyUnionCup
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ) :
    relativeSingularCohomology R A p →ₗ[R] relativeSingularCohomology R B q →ₗ[R]
      relativeSingularCohomology R (A ∪ B) (p + q) := by
  -- Form the class of the same AW product in the actual joint cocycle quotient.
  let product := (relativeUnionSingularCocycleCup R A B p q).compr₂
    (relativeUnionSingularCoboundaries R A B (p + q)).mkQ
  have hLeft : relativeSingularCoboundaries R A p ≤ product.ker := by
    intro a ha
    apply LinearMap.ext
    intro b
    change (relativeUnionSingularCoboundaries R A B (p + q)).mkQ
        (relativeUnionSingularCocycleCup R A B p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeUnionSingularCocycleCup_mem_coboundaries R A B p q a b (Or.inl ha))
  have hRight : relativeSingularCoboundaries R B q ≤ product.flip.ker := by
    intro b hb
    apply LinearMap.ext
    intro a
    change (relativeUnionSingularCoboundaries R A B (p + q)).mkQ
        (relativeUnionSingularCocycleCup R A B p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeUnionSingularCocycleCup_mem_coboundaries R A B p q a b (Or.inr hb))
  -- Descend through both coboundary submodules and their canonical homology comparisons.
  let descended := product.liftQ₂
    (relativeSingularCoboundaries R A p) (relativeSingularCoboundaries R B q) hLeft hRight
  let comparison := descended.compr₂
    ((relativeUnionSingularCochains R A B).sc (p + q)).moduleCatHomologyIso.inv.hom
  let onOriginal := (comparison.compl₂
    ((relativeSingularCochains R B).sc q).moduleCatHomologyIso.hom.hom).comp
      ((relativeSingularCochains R A).sc p).moduleCatHomologyIso.hom.hom
  -- Invert only the specified open-union small-chain comparison.
  exact onOriginal.compr₂ (relativeUnionCohomologyEquiv R A B hA hB (p + q)).symm.toLinearMap

/-- On the original cocycles, the union product has precisely the prescribed joint AW class. -/
theorem relativeSingularCohomologyUnionCup_cocycleClass
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : relativeSingularCocycles R A p) (b : relativeSingularCocycles R B q) :
    relativeUnionCohomologyComparison R A B (p + q)
        (relativeSingularCohomologyUnionCup R A B hA hB p q
          (relativeSingularCocycleClass R A p a) (relativeSingularCocycleClass R B q b)) =
      ((relativeUnionSingularCochains R A B).sc (p + q)).moduleCatHomologyIso.inv
        ((relativeUnionSingularCoboundaries R A B (p + q)).mkQ
          (relativeUnionSingularCocycleCup R A B p q a b)) := by
  /- First cancel the open-union equivalence with the very comparison
  inverted by the definition. Next cancel the two canonical relative
  homology comparisons. Evaluation of the double quotient lift on these
  original cocycles is the class of their actual joint AW product. The
  final homology comparison is exactly the displayed original joint one. -/
  -- The specified comparison cancels exactly the inverse used in the product definition.
  let E := relativeUnionCohomologyEquiv R A B hA hB (p + q)
  let product := (relativeUnionSingularCocycleCup R A B p q).compr₂
    (relativeUnionSingularCoboundaries R A B (p + q)).mkQ
  have hLeft : relativeSingularCoboundaries R A p ≤ product.ker := by
    intro a ha
    apply LinearMap.ext
    intro b
    change (relativeUnionSingularCoboundaries R A B (p + q)).mkQ
        (relativeUnionSingularCocycleCup R A B p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeUnionSingularCocycleCup_mem_coboundaries R A B p q a b (Or.inl ha))
  have hRight : relativeSingularCoboundaries R B q ≤ product.flip.ker := by
    intro b hb
    apply LinearMap.ext
    intro a
    change (relativeUnionSingularCoboundaries R A B (p + q)).mkQ
        (relativeUnionSingularCocycleCup R A B p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeUnionSingularCocycleCup_mem_coboundaries R A B p q a b (Or.inr hb))
  let descended := product.liftQ₂
    (relativeSingularCoboundaries R A p) (relativeSingularCoboundaries R B q) hLeft hRight
  let I := ((relativeSingularCochains R A).sc p).moduleCatHomologyIso
  let J := ((relativeSingularCochains R B).sc q).moduleCatHomologyIso
  let K := ((relativeUnionSingularCochains R A B).sc (p + q)).moduleCatHomologyIso
  change E (E.symm (K.inv
    (descended (I.hom (I.inv ((relativeSingularCoboundaries R A p).mkQ a)))
      (J.hom (J.inv ((relativeSingularCoboundaries R B q).mkQ b)))))) = _
  refine (E.apply_symm_apply _).trans ?_
  -- The original cocycle quotient comparisons then reduce to their same representatives.
  have hI : I.hom (I.inv ((relativeSingularCoboundaries R A p).mkQ a)) =
      (relativeSingularCoboundaries R A p).mkQ a :=
    congrArg (fun f ↦ f ((relativeSingularCoboundaries R A p).mkQ a)) I.inv_hom_id
  have hJ : J.hom (J.inv ((relativeSingularCoboundaries R B q).mkQ b)) =
      (relativeSingularCoboundaries R B q).mkQ b :=
    congrArg (fun f ↦ f ((relativeSingularCoboundaries R B q).mkQ b)) J.inv_hom_id
  rw [hI, hJ]
  rfl

/-- The two-relative product is natural for the specified continuous map and both pair maps. -/
theorem relativeSingularCohomologyPullback_unionCup
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    {A B : Set X} {A' B' : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (p q : ℕ)
    (a : relativeSingularCohomology R A' p) (b : relativeSingularCohomology R B' q) :
    relativeSingularCohomologyPullback R f
        (show Set.MapsTo f (A ∪ B) (A' ∪ B') from
          fun _ hx ↦ hx.elim (fun ha ↦ Or.inl (hfA ha)) (fun hb ↦ Or.inr (hfB hb)))
        (p + q) (relativeSingularCohomologyUnionCup R A' B' hA' hB' p q a b) =
      relativeSingularCohomologyUnionCup R A B hA hB p q
        (relativeSingularCohomologyPullback R f hfA p a)
        (relativeSingularCohomologyPullback R f hfB q b) := by
  /- Stage 1: the same f carries each original subspace chain image into
  its prescribed target image, hence induces a map on the actual quotients
  by their sums. Composing with the original projection characterizes this
  map, and gives its commuting square with the two union quotient maps.
  Stage 2: composition of a simplex with f commutes with its original
  front and back faces. Thus the joint AW cochain products are natural;
  pass through their original cocycle and coboundary quotients.
  Stage 3: the preceding square makes the two canonical cohomology
  comparisons commute with pullback. Their bijectivity, proved by open
  excision, gives the corresponding identity for their specified inverses.
  Compose this with Stage 2. No inverse-image equality for A or B, properness
  of f, or arbitrary naturality of a selected lift is assumed. -/
  -- The canonical quotient comparison supplies actual cocycle representatives.
  have hrep (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- Naturality uses the same chosen homology comparisons and actual map on kernels.
  have hclass (C D : CochainComplex (ModuleCat.{u} R) ℕ) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
    -- The comparison map on cycles has the prescribed underlying cochain value.
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    -- Its quotient square determines the induced map on the original homology objects.
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap]
    change (D.sc n).moduleCatHomologyIso.inv
      (G.φH ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))) = _
    have hcancel : (C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc n).moduleCatToCycles.range.mkQ a :=
      congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
        (C.sc n).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  -- A cochain morphism preserves the original outgoing kernel.
  have hcycles (C D : CochainComplex (ModuleCat.{u} R) ℕ) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  -- The original simplex maps commute with both faces in the Alexander--Whitney formula.
  let P := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  have hcup (i j : ℕ) (a : (singularCochains R Y).X i)
      (b : (singularCochains R Y).X j) :
      P.f (i + j) (singularCochainCup R Y i j a b) =
        singularCochainCup R X i j (P.f i a) (P.f j b) := by
    let g := TopCat.toSSet.map (TopCat.ofHom f)
    have heval (k : ℕ) (χ : (singularCochains R Y).X k)
        (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k⦌)) :
        singularCochainEquiv R X k (P.f k χ) σ =
          singularCochainEquiv R Y k χ (g.app (op ⦋k⦌) σ) := by
      change (show ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
        (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
        (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
          (SSet.chainComplexMap g (singularCoefficient R)).f k) (ULift.up 1)) = _
      rw [SSet.ι_chainComplexMap_f]
      rfl
    apply (singularCochainEquiv R X (i + j)).injective
    funext σ
    rw [heval]
    change singularCochainEquiv R Y (i + j)
      ((singularCochainEquiv R Y (i + j)).symm _) _ =
        singularCochainEquiv R X (i + j) ((singularCochainEquiv R X (i + j)).symm _) _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    dsimp only
    rw [heval, heval]
    have hfront := congrArg (fun t ↦ t σ) (g.naturality (singularCupFrontFace i j).op)
    have hback := congrArg (fun t ↦ t σ) (g.naturality (singularCupBackFace i j).op)
    exact congrArg₂ (fun u v ↦ singularCochainEquiv R Y i a u *
      singularCochainEquiv R Y j b v) hfront.symm hback.symm
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  have hkillLeft {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      singularSubspaceChains R U ≫ relativeUnionSingularChainsProjection R U V = 0 := by
    have hz := congrArg
      (fun g ↦ (biprod.inl : singularChains R U ⟶ singularChains R U ⊞ singularChains R V) ≫ g)
      (cokernel.condition (singularSubspaceSumChains R U V))
    dsimp only [singularSubspaceSumChains] at hz
    simp only [biprod.inl_desc_assoc] at hz
    exact hz
  have hkillRight {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      singularSubspaceChains R V ≫ relativeUnionSingularChainsProjection R U V = 0 := by
    have hz := congrArg
      (fun g ↦ (biprod.inr : singularChains R V ⟶ singularChains R U ⊞ singularChains R V) ≫ g)
      (cokernel.condition (singularSubspaceSumChains R U V))
    dsimp only [singularSubspaceSumChains] at hz
    simp only [biprod.inr_desc_assoc] at hz
    exact hz
  have hsub (U : Set X) (V : Set Y) (hfUV : Set.MapsTo f U V) :
      singularSubspaceChains R U ≫ F =
        (singularChainsFunctor R).map (TopCat.ofHom
          (⟨fun x : U ↦ ⟨f x, hfUV x.property⟩,
            (f.continuous.comp continuous_subtype_val).subtype_mk _⟩ : C(U, V))) ≫
          singularSubspaceChains R V := by
    simp only [singularSubspaceChains, F, ← Functor.map_comp]
    rfl
  -- The specified map of pairs carries both original summands to their target summands.
  have hvan : singularSubspaceSumChains R A B ≫ F ≫
      relativeUnionSingularChainsProjection R A' B' = 0 := by
    apply biprod.hom_ext'
    · simp only [singularSubspaceSumChains, biprod.inl_desc_assoc, comp_zero]
      rw [← Category.assoc, hsub A A' hfA, Category.assoc, hkillLeft, comp_zero]
    · simp only [singularSubspaceSumChains, biprod.inr_desc_assoc, comp_zero]
      rw [← Category.assoc, hsub B B' hfB, Category.assoc, hkillRight, comp_zero]
  let Qchain := cokernel.desc (singularSubspaceSumChains R A B)
    (F ≫ relativeUnionSingularChainsProjection R A' B') hvan
  have hQchain : relativeUnionSingularChainsProjection R A B ≫ Qchain =
      F ≫ relativeUnionSingularChainsProjection R A' B' := cokernel.π_desc _ _ _
  have hto {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      relativeUnionSingularChainsProjection R U V ≫ relativeUnionSingularChainsToRelative R U V =
        relativeSingularChainsProjection R (U ∪ V) := by
    simp [relativeUnionSingularChainsProjection, relativeUnionSingularChainsToRelative]
  let hfUnion : Set.MapsTo f (A ∪ B) (A' ∪ B') :=
    fun _ hx ↦ hx.elim (fun ha ↦ Or.inl (hfA ha)) (fun hb ↦ Or.inr (hfB hb))
  have hUnion : Qchain ≫ relativeUnionSingularChainsToRelative R A' B' =
      relativeUnionSingularChainsToRelative R A B ≫ relativeSingularChainsMap R f hfUnion := by
    apply (cancel_epi (relativeUnionSingularChainsProjection R A B)).mp
    rw [← Category.assoc, hQchain, Category.assoc, hto]
    rw [← Category.assoc, hto]
    simp [relativeSingularChainsMap, relativeSingularChainsProjection, F]
  let Q := (singularCochainDualFunctor R).map Qchain.op
  let FA := (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hfA).op
  let FB := (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hfB).op
  let JX := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A B).op
  let JY := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A' B').op
  let JAX := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JAY := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A').op
  let JBX := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  let JBY := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B').op
  have hQprojection : Q ≫ JX = JY ≫ P := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ =
      (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeUnionSingularChainsProjection R A B ≫ Qchain).op =
        (singularCochainDualFunctor R).map
          (F ≫ relativeUnionSingularChainsProjection R A' B').op
    rw [hQchain]
  have hpairProjection (U : Set X) (V : Set Y) (hfUV : Set.MapsTo f U V) :
      (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hfUV).op ≫
          (singularCochainDualFunctor R).map (relativeSingularChainsProjection R U).op =
        (singularCochainDualFunctor R).map (relativeSingularChainsProjection R V).op ≫ P := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ =
      (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R U ≫ relativeSingularChainsMap R f hfUV).op =
        (singularCochainDualFunctor R).map (F ≫ relativeSingularChainsProjection R V).op
    have hpair : relativeSingularChainsProjection R U ≫ relativeSingularChainsMap R f hfUV =
        F ≫ relativeSingularChainsProjection R V := by
      simp [relativeSingularChainsProjection, relativeSingularChainsMap, F]
    rw [hpair]
  -- The same quotient square makes the original cohomology comparisons commute.
  have hcomparison : relativeSingularCohomologyPullback R f hfUnion (p + q) ≫
        relativeUnionCohomologyComparison R A B (p + q) =
      relativeUnionCohomologyComparison R A' B' (p + q) ≫
        HomologicalComplex.homologyMap Q (p + q) := by
    let H := singularCochainDualFunctor R ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (p + q)
    change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hUnion]
  have hcomparisonValue (z : relativeSingularCohomology R (A' ∪ B') (p + q)) :
      relativeUnionCohomologyComparison R A B (p + q)
          (relativeSingularCohomologyPullback R f hfUnion (p + q) z) =
        HomologicalComplex.homologyMap Q (p + q)
          (relativeUnionCohomologyComparison R A' B' (p + q) z) :=
    congrArg (fun g ↦ g z) hcomparison
  have hjoint {Z : Type u} [TopologicalSpace Z] (U V : Set Z)
      (α : (relativeSingularCochains R U).X p) (β : (relativeSingularCochains R V).X q) :
      ((singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R U V).op).f
          (p + q) (relativeUnionSingularCochainCup R U V p q α β) =
        singularCochainCup R Z p q
          (((singularCochainDualFunctor R).map (relativeSingularChainsProjection R U).op).f p α)
          (((singularCochainDualFunctor R).map (relativeSingularChainsProjection R V).op).f q β) :=
    congrArg Subtype.val ((relativeUnionSingularCochainEquiv R U V (p + q)).apply_symm_apply _)
  apply (relativeUnionCohomologyComparison_bijective R A B hA hB (p + q)).injective
  rw [hcomparisonValue]
  obtain ⟨α, hα⟩ := hrep (relativeSingularCochains R A') p a
  obtain ⟨β, hβ⟩ := hrep (relativeSingularCochains R B') q b
  change relativeSingularCocycleClass R A' p α = a at hα
  change relativeSingularCocycleClass R B' q β = b at hβ
  obtain ⟨α', hα'⟩ := hcycles (relativeSingularCochains R A') (relativeSingularCochains R A) FA p α
  obtain ⟨β', hβ'⟩ := hcycles (relativeSingularCochains R B') (relativeSingularCochains R B) FB q β
  have ha := hclass (relativeSingularCochains R A')
    (relativeSingularCochains R A) FA p α α' hα'.symm
  have hb := hclass (relativeSingularCochains R B')
    (relativeSingularCochains R B) FB q β β' hβ'.symm
  change relativeSingularCohomologyPullback R f hfA p (relativeSingularCocycleClass R A' p α) =
    relativeSingularCocycleClass R A p α' at ha
  change relativeSingularCohomologyPullback R f hfB q (relativeSingularCocycleClass R B' q β) =
    relativeSingularCocycleClass R B q β' at hb
  rw [← hα, ← hβ, relativeSingularCohomologyUnionCup_cocycleClass, ha, hb,
    relativeSingularCohomologyUnionCup_cocycleClass]
  apply hclass (relativeUnionSingularCochains R A' B')
    (relativeUnionSingularCochains R A B) Q (p + q)
  apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
  apply Subtype.ext
  change JX.f (p + q) (Q.f (p + q) (relativeUnionSingularCochainCup R A' B' p q α.val β.val)) =
    JX.f (p + q) (relativeUnionSingularCochainCup R A B p q α'.val β'.val)
  have hQvalue (n : ℕ) (z : (relativeUnionSingularCochains R A' B').X n) :
      JX.f n (Q.f n z) = P.f n (JY.f n z) := congrArg (fun g ↦ g.f n z) hQprojection
  have hAvalue : JAX.f p α'.val = P.f p (JAY.f p α.val) :=
    (congrArg (fun z ↦ JAX.f p z) hα').trans
      (congrArg (fun g ↦ g.f p α.val) (hpairProjection A A' hfA))
  have hBvalue : JBX.f q β'.val = P.f q (JBY.f q β.val) :=
    (congrArg (fun z ↦ JBX.f q z) hβ').trans
      (congrArg (fun g ↦ g.f q β.val) (hpairProjection B B' hfB))
  calc
    _ = P.f (p + q) (JY.f (p + q)
        (relativeUnionSingularCochainCup R A' B' p q α.val β.val)) := hQvalue (p + q) _
    _ = P.f (p + q) (singularCochainCup R Y p q (JAY.f p α.val) (JBY.f q β.val)) :=
      congrArg (fun z ↦ P.f (p + q) z) (hjoint A' B' α.val β.val)
    _ = singularCochainCup R X p q (P.f p (JAY.f p α.val)) (P.f q (JBY.f q β.val)) :=
      hcup p q _ _
    _ = singularCochainCup R X p q (JAX.f p α'.val) (JBX.f q β'.val) :=
      congrArg₂ (fun x y ↦ singularCochainCup R X p q x y) hAvalue.symm hBvalue.symm
    _ = _ := (hjoint A B α'.val β'.val).symm

/-- Restricting the union condition to B recovers the original ordinary-relative action. -/
theorem relativeSingularCohomologyUnionCup_restrict_right
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : relativeSingularCohomology R A p) (b : relativeSingularCohomology R B q) :
    relativeSingularCohomologyRestriction R B (A ∪ B) (fun _ hb ↦ Or.inr hb) (p + q)
        (relativeSingularCohomologyUnionCup R A B hA hB p q a b) =
      relativeSingularCohomologyAction R B p q
        (relativeSingularCohomologyToOrdinary R A p a) b := by
  /- Stage 1: the canonical quotient C_*(X,B) -> C_*(X)/(C_*(A)+C_*(B))
  is induced by the original chain projections. Composing it with the
  joint-to-union map gives precisely C_*(X,B) -> C_*(X,A union B).
  Dualization therefore identifies restriction of the union comparison
  inverse with restriction of the joint class to the original B-relative
  cohomology. This uses the same commuting square and the comparison's
  bijectivity, not injectivity of the map forgetting all relative support.
  Stage 2: on original cocycles the joint product pulled back to C_*(X,B)
  is exactly relativeSingularCochainAction: its left factor is the original
  A-relative cochain pulled back to ordinary cochains, and its right factor
  remains the original B-relative cochain. Pass through the same quotient
  classes and canonical homology comparisons to obtain the displayed action. -/
  -- The canonical quotient comparison supplies actual cocycle representatives.
  have hrep (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- Naturality uses the same chosen homology comparisons and actual map on kernels.
  have hclass (C D : CochainComplex (ModuleCat.{u} R) ℕ) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
    -- The comparison map on cycles has the prescribed underlying cochain value.
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    -- Its quotient square determines the induced map on the original homology objects.
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap]
    change (D.sc n).moduleCatHomologyIso.inv
      (G.φH ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))) = _
    have hcancel : (C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc n).moduleCatToCycles.range.mkQ a :=
      congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
        (C.sc n).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  -- A cochain morphism preserves the original outgoing kernel.
  have hcycles (C D : CochainComplex (ModuleCat.{u} R) ℕ) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  -- The B-relative projection factors through the same joint quotient.
  have hBzero : singularSubspaceChains R B ≫ relativeUnionSingularChainsProjection R A B = 0 := by
    have hz := congrArg
      (fun g ↦ (biprod.inr : singularChains R B ⟶ singularChains R A ⊞ singularChains R B) ≫ g)
      (cokernel.condition (singularSubspaceSumChains R A B))
    dsimp only [singularSubspaceSumChains] at hz
    simp only [biprod.inr_desc_assoc] at hz
    exact hz
  let qB : relativeSingularChains R B ⟶ relativeUnionSingularChains R A B :=
    cokernel.desc (singularSubspaceChains R B) (relativeUnionSingularChainsProjection R A B) hBzero
  have hqB : relativeSingularChainsProjection R B ≫ qB =
      relativeUnionSingularChainsProjection R A B := cokernel.π_desc _ _ _
  have hchain : qB ≫ relativeUnionSingularChainsToRelative R A B =
      relativeSingularChainsMap R (ContinuousMap.id X)
        (show Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ h ↦ Or.inr h) := by
    apply (cancel_epi (relativeSingularChainsProjection R B)).mp
    rw [← Category.assoc, hqB]
    simp [relativeUnionSingularChainsProjection, relativeUnionSingularChainsToRelative,
      relativeSingularChainsProjection, relativeSingularChainsMap]
  let C := relativeUnionSingularCochains R A B
  let D := relativeSingularCochains R B
  let F := (singularCochainDualFunctor R).map qB.op
  let G := (singularCochainDualFunctor R).map (relativeUnionSingularChainsToRelative R A B).op
  let JA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  let J := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A B).op
  have hprojection : F ≫ JB = J := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp, hqB]
  -- The canonical comparison followed by this pullback is the original B restriction.
  have hcochain : G ≫ F = (singularCochainDualFunctor R).map
      (relativeSingularChainsMap R (ContinuousMap.id X)
        (show Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ h ↦ Or.inr h)).op := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp, hchain]
  have hcohom : relativeUnionCohomologyComparison R A B (p + q) ≫
      HomologicalComplex.homologyMap F (p + q) =
        relativeSingularCohomologyRestriction R B (A ∪ B) (fun _ h ↦ Or.inr h) (p + q) := by
    change HomologicalComplex.homologyMap G (p + q) ≫
      HomologicalComplex.homologyMap F (p + q) = _
    rw [← HomologicalComplex.homologyMap_comp, hcochain]
    rfl
  have hrestriction (z : relativeSingularCohomology R (A ∪ B) (p + q)) :
      relativeSingularCohomologyRestriction R B (A ∪ B) (fun _ h ↦ Or.inr h) (p + q) z =
        HomologicalComplex.homologyMap F (p + q)
          (relativeUnionCohomologyComparison R A B (p + q) z) :=
    (congrArg (fun f ↦ f z) hcohom).symm
  -- Both products pull back to the same original front/back cochain formula.
  have hjoint (α : (relativeSingularCochains R A).X p)
      (β : (relativeSingularCochains R B).X q) :
      J.f (p + q) (relativeUnionSingularCochainCup R A B p q α β) =
        singularCochainCup R X p q (JA.f p α) (JB.f q β) :=
    congrArg Subtype.val ((relativeUnionSingularCochainEquiv R A B (p + q)).apply_symm_apply _)
  have haction (α : (singularCochains R X).X p)
      (β : (relativeSingularCochains R B).X q) :
      JB.f (p + q) (relativeSingularCochainAction R B p q α β) =
        singularCochainCup R X p q α (JB.f q β) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R B (p + q)).apply_symm_apply _)
  obtain ⟨α, hα⟩ := hrep (relativeSingularCochains R A) p a
  obtain ⟨β, hβ⟩ := hrep D q b
  change relativeSingularCocycleClass R A p α = a at hα
  change relativeSingularCocycleClass R B q β = b at hβ
  obtain ⟨α', hα'⟩ := hcycles (relativeSingularCochains R A) (singularCochains R X) JA p α
  have ha := hclass (relativeSingularCochains R A) (singularCochains R X) JA p α α' hα'.symm
  change relativeSingularCohomologyToOrdinary R A p (relativeSingularCocycleClass R A p α) =
    singularCocycleClass R X p α' at ha
  rw [hrestriction, ← hα, ← hβ, relativeSingularCohomologyUnionCup_cocycleClass,
    ha, relativeSingularCohomologyAction_cocycleClass]
  apply hclass C D F (p + q)
  apply (relativeSingularCochainEquiv R B (p + q)).injective
  apply Subtype.ext
  change JB.f (p + q) (F.f (p + q) (relativeUnionSingularCochainCup R A B p q α.val β.val)) =
    JB.f (p + q) (relativeSingularCochainAction R B p q α'.val β.val)
  have hcomp (n : ℕ) (v : C.X n) : JB.f n (F.f n v) = J.f n v :=
    congrArg (fun f ↦ f.f n v) hprojection
  calc
    _ = J.f (p + q) (relativeUnionSingularCochainCup R A B p q α.val β.val) :=
      hcomp (p + q) _
    _ = singularCochainCup R X p q (JA.f p α.val) (JB.f q β.val) := hjoint α.val β.val
    _ = singularCochainCup R X p q α'.val (JB.f q β.val) :=
      congrArg (fun χ ↦ singularCochainCup R X p q χ (JB.f q β.val)) hα'.symm
    _ = _ := (haction α'.val β.val).symm

end AtiyahSinger
