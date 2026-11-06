/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyCup
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The normalized integral-to-rational map on singular cohomology

Public module ID: M1626.

D11 / C02. Integer coefficients are included in the rationals on every
original singular simplex. The actual cochain map is uniquely fixed by
that evaluation formula. Restriction of scalars only makes the target an
integer module; the canonical homology comparison returns to the original
rational cohomology group. No rational cohomology generator is selected.

The induced map is natural for the specified continuous maps and preserves
the original Alexander--Whitney cup product and constant-one class. These
are the coefficient-change properties used by rational characteristic
classes. No finite generation, compactness or connectedness is required,
and no injectivity or rational-cohomology comparison is claimed.

Source: Hatcher, Algebraic Topology, sections 3.1 and 3.2, the cochain
coefficient homomorphism and the Alexander--Whitney formula. The unique
cochain-map certificate is an implementation of that standard coefficient
homomorphism. The proofs preserve the original complexes and comparison maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

local notation "ℚRes" => ModuleCat.restrictScalars (Int.castRingHom ℚ)
local notation "ℚResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom ℚ)) (ComplexShape.up ℕ)

/-- Coefficient inclusion uniquely specifies the cochain map on every original simplex. -/
theorem existsUnique_singularCochainsRationalization
    (X : Type u) [TopologicalSpace X] :
    ∃! f : singularCochains ℤ X ⟶ (ℚResC).obj (singularCochains ℚ X),
      ∀ (n : ℕ) (φ : (singularCochains ℤ X).X n)
        (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)),
        singularCochainEquiv ℚ X n (f.f n φ) σ =
          ULift.up (((singularCochainEquiv ℤ X n φ σ).down : ℤ) : ℚ) := by
  /- Stage 1: use singularCochainEquiv to view each original integer
  cochain as its values on the actual continuous singular simplices.
  Include every such integer value into ℚ, and extend ℚ-linearly to
  the actual rational chains using the inverse evaluation equivalence.
  This operation on cochains is integer-linear by the original formulas.
  Stage 2: the differential is the alternating sum of evaluations on
  the same faces. Coefficient inclusion preserves the sum and signs,
  so the degreewise maps form a morphism of the original cochain complexes.
  Stage 3: equality of all generator evaluations gives equality of
  cochains and then of cochain maps. The specified formula therefore
  fixes this map uniquely, including the coefficient of every vertex. -/
  classical
  -- Include each integer value on the original simplex into the rationals.
  let component (n : ℕ) : (singularCochains ℤ X).X n →ₗ[ℤ]
      (singularCochains ℚ X).X n :=
    { toFun := fun φ ↦ (singularCochainEquiv ℚ X n).symm
        (fun σ ↦ ULift.up ((singularCochainEquiv ℤ X n φ σ).down : ℚ))
      map_add' := by
        intro φ ψ
        apply (singularCochainEquiv ℚ X n).injective
        funext σ
        simp only [map_add, LinearEquiv.apply_symm_apply, Pi.add_apply]
        apply ULift.ext
        simp
      map_smul' := by
        intro r φ
        apply (singularCochainEquiv ℚ X n).injective
        funext σ
        simp only [map_zsmul, LinearEquiv.apply_symm_apply, Pi.smul_apply]
        apply ULift.ext
        simp }
  have heval (n : ℕ) (φ : (singularCochains ℤ X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) :
      singularCochainEquiv ℚ X n (component n φ) σ =
        ULift.up ((singularCochainEquiv ℤ X n φ σ).down : ℚ) :=
    congrFun ((singularCochainEquiv ℚ X n).apply_symm_apply _) σ
  -- The unchanged differential is the alternating sum on those same faces.
  have hdiff (R : Type) [CommRing R] (n : ℕ) (φ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n + 1⦌)) :
      singularCochainEquiv R X (n + 1) ((singularCochains R X).d n (n + 1) φ) σ =
        ∑ i : Fin (n + 2), (-1 : R) ^ i.val • singularCochainEquiv R X n φ
          ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X n ⟶ singularCoefficient R from φ)
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (singularCoefficient R)).d (n + 1) n) (ULift.up 1)) = _
    rw [SSet.ιChainComplex_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    change ((-1 : ℤ) ^ i.val) •
      singularCochainEquiv R X n φ ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = _
    rw [← Int.cast_smul_eq_zsmul R]
    simp
  let F : singularCochains ℤ X ⟶ (ℚResC).obj (singularCochains ℚ X) :=
    { f := fun n ↦ ModuleCat.ofHom (component n)
      comm' := by
        intro n m hnm
        change n + 1 = m at hnm
        subst m
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply (singularCochainEquiv ℚ X (n + 1)).injective
        funext σ
        change singularCochainEquiv ℚ X (n + 1)
          ((singularCochains ℚ X).d n (n + 1) (component n φ)) σ =
            singularCochainEquiv ℚ X (n + 1)
              (component (n + 1) ((singularCochains ℤ X).d n (n + 1) φ)) σ
        rw [hdiff ℚ n (component n φ) σ, heval, hdiff ℤ n φ σ]
        apply ULift.ext
        change (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ) _ =
          (((ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ) _) : ℚ)
        simp [heval, map_sum, map_smul] }
  refine ⟨F, heval, ?_⟩
  -- Original generator evaluations determine every component and hence the whole map.
  intro G hG
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (singularCochainEquiv ℚ X n).injective
  funext σ
  exact (hG n φ σ).trans (heval n φ σ).symm

/-- The actual cochain coefficient inclusion fixed by its original simplex values. -/
def singularCochainsRationalization (X : Type u) [TopologicalSpace X] :
    singularCochains ℤ X ⟶ (ℚResC).obj (singularCochains ℚ X) :=
  Classical.choose (existsUnique_singularCochainsRationalization X).exists

/-- The coefficient homomorphism into the original rational singular cohomology. -/
def singularCohomologyRationalization (X : Type u) [TopologicalSpace X] (n : ℕ) :
    singularCohomology ℤ X n ⟶ (ℚRes).obj (singularCohomology ℚ X n) :=
  HomologicalComplex.homologyMap (singularCochainsRationalization X) n ≫
    (((singularCochains ℚ X).sc n).mapHomologyIso ℚRes).hom

/-- Coefficient inclusion commutes with pullback along the given continuous map. -/
theorem singularCohomologyRationalization_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (a : singularCohomology ℤ Y n) :
    singularCohomologyRationalization X n (singularCohomologyPullback ℤ f n a) =
      singularCohomologyPullback ℚ f n (singularCohomologyRationalization Y n a) := by
  /- Evaluate the two cochain composites on a singular simplex σ.
  Both values are the image in ℚ of the original integer evaluation
  on f∘σ. The uniqueness certificate gives the cochain naturality
  square for these very maps. Apply homology and its canonical
  restriction-of-scalars comparison, and evaluate the resulting square
  on a. Neither a replacement space nor an arbitrary isomorphism occurs. -/
  -- Check coefficient inclusion on the very simplex composed with the given map.
  let PZ := (singularCochainsFunctor ℤ).map (TopCat.ofHom f).op
  let PQ := (singularCochainsFunctor ℚ).map (TopCat.ofHom f).op
  have heval (Z : Type u) [TopologicalSpace Z] :=
    Classical.choose_spec (existsUnique_singularCochainsRationalization Z).exists
  have hpull (R : Type) [CommRing R] (k : ℕ) (χ : (singularCochains R Y).X k)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k⦌)) :
      singularCochainEquiv R X k
        (((singularCochainsFunctor R).map (TopCat.ofHom f).op).f k χ) σ =
          singularCochainEquiv R Y k χ
            ((TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋k⦌) σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
      (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
          (singularCoefficient R)).f k) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  have hsquare : PZ ≫ singularCochainsRationalization X =
      singularCochainsRationalization Y ≫ (ℚResC).map PQ := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    apply (singularCochainEquiv ℚ X k).injective
    funext σ
    change singularCochainEquiv ℚ X k
      ((singularCochainsRationalization X).f k (PZ.f k χ)) σ =
        singularCochainEquiv ℚ X k
          (PQ.f k ((singularCochainsRationalization Y).f k χ)) σ
    let castValue (v : ULift.{u} ℤ) : ULift.{u} ℚ := ULift.up (v.down : ℚ)
    exact (heval X k (PZ.f k χ) σ).trans
      ((congrArg castValue (hpull ℤ k χ σ)).trans
        ((heval Y k χ ((TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋k⦌) σ)).symm.trans
          (hpull ℚ k ((singularCochainsRationalization Y).f k χ) σ).symm))
  -- Homology respects that square; its scalar-restriction comparison is natural.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F a) hmap
  change HomologicalComplex.homologyMap (singularCochainsRationalization X) n
    (HomologicalComplex.homologyMap PZ n a) =
      HomologicalComplex.homologyMap ((ℚResC).map PQ) n
        (HomologicalComplex.homologyMap (singularCochainsRationalization Y) n a) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℚ)
      (ComplexShape.up ℕ) n).map PQ) ℚRes
  have hnatValue := congrArg
    (fun F ↦ F (HomologicalComplex.homologyMap (singularCochainsRationalization Y) n a))
    hnat
  change (((singularCochains ℚ X).sc n).mapHomologyIso ℚRes).hom
    (HomologicalComplex.homologyMap ((ℚResC).map PQ) n
      (HomologicalComplex.homologyMap (singularCochainsRationalization Y) n a)) =
        singularCohomologyPullback ℚ f n (singularCohomologyRationalization Y n a)
    at hnatValue
  exact (congrArg (((singularCochains ℚ X).sc n).mapHomologyIso ℚRes).hom hvalue).trans
    hnatValue

/-- The coefficient homomorphism preserves the original cohomological cup product. -/
theorem singularCohomologyRationalization_cup
    (X : Type u) [TopologicalSpace X] (p q : ℕ)
    (a : singularCohomology ℤ X p) (b : singularCohomology ℤ X q) :
    singularCohomologyRationalization X (p + q) (singularCohomologyCup ℤ X p q a b) =
      singularCohomologyCup ℚ X p q
        (singularCohomologyRationalization X p a)
        (singularCohomologyRationalization X q b) := by
  /- Stage 1: represent a and b by the original integer cocycles.
  The Alexander--Whitney formula evaluates their cup product on the
  same front and back faces. Integer inclusion preserves multiplication,
  so the cochain coefficient map preserves exactly that product.
  Stage 2: pass through the original cocycle/boundary quotients and
  their canonical categorical homology comparisons. This gives the
  displayed equality in degree p+q, with no degree transport or new sign. -/
  -- Work with the original cocycle quotients, including the scalar-restriction comparison.
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
  have hordinary (R : Type) [CommRing R] (p q : ℕ)
      (a : singularCocycles R X p) (b : singularCocycles R X q) :
      singularCohomologyCup R X p q
          (singularCocycleClass R X p a) (singularCocycleClass R X q b) =
        singularCocycleClass R X (p + q) (singularCocycleCup R X p q a b) := by
    let product := (singularCocycleCup R X p q).compr₂
      (singularCoboundaries R X (p + q)).mkQ
    have hLeft : singularCoboundaries R X p ≤ product.ker := by
      intro a ha
      apply LinearMap.ext
      intro b
      change (singularCoboundaries R X (p + q)).mkQ
          (singularCocycleCup R X p q a b) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (singularCocycleCup_mem_coboundaries R X p q a b (Or.inl ha))
    have hRight : singularCoboundaries R X q ≤ product.flip.ker := by
      intro b hb
      apply LinearMap.ext
      intro a
      change (singularCoboundaries R X (p + q)).mkQ
          (singularCocycleCup R X p q a b) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (singularCocycleCup_mem_coboundaries R X p q a b (Or.inr hb))
    -- Descend by both actual boundary submodules and use their canonical homology comparisons.
    let descended := product.liftQ₂
      (singularCoboundaries R X p) (singularCoboundaries R X q) hLeft hRight
    let I := ((singularCochains R X).sc p).moduleCatHomologyIso
    let J := ((singularCochains R X).sc q).moduleCatHomologyIso
    let K := ((singularCochains R X).sc (p + q)).moduleCatHomologyIso
    change K.inv (descended (I.hom (I.inv ((singularCoboundaries R X p).mkQ a)))
      (J.hom (J.inv ((singularCoboundaries R X q).mkQ b)))) =
        K.inv ((singularCoboundaries R X (p + q)).mkQ
          (singularCocycleCup R X p q a b))
    have hI : I.hom (I.inv ((singularCoboundaries R X p).mkQ a)) =
        (singularCoboundaries R X p).mkQ a :=
      congrArg (fun f ↦ f ((singularCoboundaries R X p).mkQ a)) I.inv_hom_id
    have hJ : J.hom (J.inv ((singularCoboundaries R X q).mkQ b)) =
        (singularCoboundaries R X q).mkQ b := by
      exact congrArg (fun f ↦ f ((singularCoboundaries R X q).mkQ b)) J.inv_hom_id
    rw [hI, hJ]
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
  -- Choose representatives through the actual quotient, then use the canonical comparisons.
  obtain ⟨α, hα⟩ := hrep ℤ (singularCochains ℤ X) p a
  obtain ⟨β, hβ⟩ := hrep ℤ (singularCochains ℤ X) q b
  obtain ⟨αQ, hαQ⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ)
    (singularCochains ℤ X) (singularCochains ℚ X) F p α
  obtain ⟨βQ, hβQ⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ)
    (singularCochains ℤ X) (singularCochains ℚ X) F q β
  have hαclass : singularCohomologyRationalization X p (singularCocycleClass ℤ X p α) =
      singularCocycleClass ℚ X p αQ :=
    hclass ℤ ℚ (Int.castRingHom ℚ) _ _ F p α αQ hαQ.symm
  have hβclass : singularCohomologyRationalization X q (singularCocycleClass ℤ X q β) =
      singularCocycleClass ℚ X q βQ :=
    hclass ℤ ℚ (Int.castRingHom ℚ) _ _ F q β βQ hβQ.symm
  have hproduct : singularCohomologyRationalization X (p + q)
      (singularCocycleClass ℤ X (p + q) (singularCocycleCup ℤ X p q α β)) =
        singularCocycleClass ℚ X (p + q) (singularCocycleCup ℚ X p q αQ βQ) := by
    apply hclass ℤ ℚ (Int.castRingHom ℚ) _ _ F (p + q)
    change F.f (p + q) (singularCochainCup ℤ X p q α.val β.val) =
      singularCochainCup ℚ X p q αQ.val βQ.val
    rw [hαQ, hβQ]
    exact hcup α.val β.val
  change singularCocycleClass ℤ X p α = a at hα
  change singularCocycleClass ℤ X q β = b at hβ
  rw [← hα, ← hβ, hordinary ℤ, hαclass, hβclass, hordinary ℚ]
  exact hproduct

/-- The coefficient homomorphism sends the constant-one integral class to the rational unit. -/
theorem singularCohomologyRationalization_one
    (X : Type u) [TopologicalSpace X] :
    singularCohomologyRationalization X 0 (singularCohomologyOne ℤ X) =
      singularCohomologyOne ℚ X := by
  /- The original integer zero-cocycle evaluates to 1 at every vertex.
  Its rationalized cochain has the same constant-one evaluations,
  since the coefficient inclusion sends 1 to 1. Equality of cochains
  descends to equality of their original classes, including for X empty. -/
  -- Use the original quotient comparison for this same coefficient map.
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
  -- The original constant-one cocycles agree after including their vertex values.
  apply hclass ℤ ℚ (Int.castRingHom ℚ) (singularCochains ℤ X)
    (singularCochains ℚ X) (singularCochainsRationalization X) 0
    (singularCocycleOne ℤ X) (singularCocycleOne ℚ X)
  apply (singularCochainEquiv ℚ X 0).injective
  funext σ
  have h := Classical.choose_spec (existsUnique_singularCochainsRationalization X).exists
    0 (singularCochainOne ℤ X) σ
  have honeZ : singularCochainEquiv ℤ X 0 (singularCochainOne ℤ X) σ = 1 :=
    congrFun ((singularCochainEquiv ℤ X 0).apply_symm_apply _) σ
  have honeQ : singularCochainEquiv ℚ X 0 (singularCochainOne ℚ X) σ = 1 :=
    congrFun ((singularCochainEquiv ℚ X 0).apply_symm_apply _) σ
  refine h.trans (?_ : ULift.up
    ((singularCochainEquiv ℤ X 0 (singularCochainOne ℤ X) σ).down : ℚ) = _)
  exact (congrArg (fun z : ULift.{u} ℤ ↦ (ULift.up (z.down : ℚ) : ULift.{u} ℚ))
    honeZ).trans honeQ.symm

end AtiyahSinger
