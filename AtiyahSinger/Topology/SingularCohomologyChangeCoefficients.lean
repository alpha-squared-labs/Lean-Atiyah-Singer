/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyRationalization
public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Change from integral to arbitrary commutative coefficients

Public module ID: M2127.

Each original simplex value is sent along the canonical map from the integers
to the specified coefficient ring. The cochain map and its homology comparison
retain the original complexes, pullbacks, Alexander--Whitney cup and unit.
No tensor-product comparison or finiteness hypothesis is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

local notation "RRes" => ModuleCat.restrictScalars (Int.castRingHom R)
local notation "RResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom R)) (ComplexShape.up ℕ)

/-- Coefficient change uniquely specifies the cochain map on every original simplex. -/
theorem existsUnique_singularCochainsChangeCoefficients
    (X : Type u) [TopologicalSpace X] :
    ∃! f : singularCochains ℤ X ⟶ (RResC).obj (singularCochains R X),
      ∀ (n : ℕ) (φ : (singularCochains ℤ X).X n)
        (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)),
        singularCochainEquiv R X n (f.f n φ) σ =
          ULift.up (((singularCochainEquiv ℤ X n φ σ).down : ℤ) : R) := by
  /- Stage 1: use singularCochainEquiv to view each original integer
  cochain as its values on the actual continuous singular simplices.
  Send every such integer value into R, and extend R-linearly to
  the actual target-ring chains using the inverse evaluation equivalence.
  This operation on cochains is integer-linear by the original formulas.
  Stage 2: the differential is the alternating sum of evaluations on
  the same faces. Coefficient change preserves the sum and signs,
  so the degreewise maps form a morphism of the original cochain complexes.
  Stage 3: equality of all generator evaluations gives equality of
  cochains and then of cochain maps. The specified formula therefore
  fixes this map uniquely, including the coefficient of every vertex. -/
  classical
  -- Map each integer value on the original simplex into the specified ring.
  let component (n : ℕ) : (singularCochains ℤ X).X n →ₛₗ[Int.castRingHom R]
      (singularCochains R X).X n :=
    { toFun := fun φ ↦ (singularCochainEquiv R X n).symm
        (fun σ ↦ ULift.up ((singularCochainEquiv ℤ X n φ σ).down : R))
      map_add' := by
        intro φ ψ
        apply (singularCochainEquiv R X n).injective
        funext σ
        simp only [map_add, LinearEquiv.apply_symm_apply, Pi.add_apply]
        apply ULift.ext
        simp
      map_smul' := by
        intro r φ
        apply (singularCochainEquiv R X n).injective
        funext σ
        simp only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply]
        apply ULift.ext
        simp }
  have heval (n : ℕ) (φ : (singularCochains ℤ X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) :
      singularCochainEquiv R X n (component n φ) σ =
        ULift.up ((singularCochainEquiv ℤ X n φ σ).down : R) :=
    congrFun ((singularCochainEquiv R X n).apply_symm_apply _) σ
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
  let F : singularCochains ℤ X ⟶ (RResC).obj (singularCochains R X) :=
    { f := fun n ↦ ModuleCat.semilinearMapAddEquiv (Int.castRingHom R)
        ((singularCochains ℤ X).X n) ((singularCochains R X).X n) (component n)
      comm' := by
        intro n m hnm
        change n + 1 = m at hnm
        subst m
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply (singularCochainEquiv R X (n + 1)).injective
        funext σ
        change singularCochainEquiv R X (n + 1)
          ((singularCochains R X).d n (n + 1) (component n φ)) σ =
            singularCochainEquiv R X (n + 1)
              (component (n + 1) ((singularCochains ℤ X).d n (n + 1) φ)) σ
        rw [hdiff R n (component n φ) σ, heval, hdiff ℤ n φ σ]
        apply ULift.ext
        change (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R) _ =
          (((ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ) _) : R)
        simp [heval, map_sum, map_smul] }
  refine ⟨F, heval, ?_⟩
  -- Original generator evaluations determine every component and hence the whole map.
  intro G hG
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (singularCochainEquiv R X n).injective
  funext σ
  exact (hG n φ σ).trans (heval n φ σ).symm

/-- The actual cochain coefficient homomorphism fixed by its original simplex values. -/
def singularCochainsChangeCoefficients (X : Type u) [TopologicalSpace X] :
    singularCochains ℤ X ⟶ (RResC).obj (singularCochains R X) :=
  Classical.choose (existsUnique_singularCochainsChangeCoefficients R X).exists

/-- The coefficient homomorphism into the original target singular cohomology. -/
def singularCohomologyChangeCoefficients (X : Type u) [TopologicalSpace X] (n : ℕ) :
    singularCohomology ℤ X n ⟶ (RRes).obj (singularCohomology R X n) :=
  HomologicalComplex.homologyMap (singularCochainsChangeCoefficients R X) n ≫
    (((singularCochains R X).sc n).mapHomologyIso RRes).hom

/-- The actual cochain coefficient map commutes with pullback on the same simplices. -/
theorem singularCochainsChangeCoefficients_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (singularCochainsFunctor ℤ).map (TopCat.ofHom f).op ≫
        singularCochainsChangeCoefficients R X =
      singularCochainsChangeCoefficients R Y ≫ (RResC).map
        ((singularCochainsFunctor R).map (TopCat.ofHom f).op) := by
  -- Check coefficient homomorphism on the very simplex composed with the given map.
  let PZ := (singularCochainsFunctor ℤ).map (TopCat.ofHom f).op
  let PQ := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  have heval (Z : Type u) [TopologicalSpace Z] :=
    Classical.choose_spec (existsUnique_singularCochainsChangeCoefficients R Z).exists
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
  have hsquare : PZ ≫ singularCochainsChangeCoefficients R X =
      singularCochainsChangeCoefficients R Y ≫ (RResC).map PQ := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    apply (singularCochainEquiv R X k).injective
    funext σ
    change singularCochainEquiv R X k
      ((singularCochainsChangeCoefficients R X).f k (PZ.f k χ)) σ =
        singularCochainEquiv R X k
          (PQ.f k ((singularCochainsChangeCoefficients R Y).f k χ)) σ
    let castValue (v : ULift.{u} ℤ) : ULift.{u} R := ULift.up (v.down : R)
    exact (heval X k (PZ.f k χ) σ).trans
      ((congrArg castValue (hpull ℤ k χ σ)).trans
        ((heval Y k χ ((TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋k⦌) σ)).symm.trans
          (hpull R k ((singularCochainsChangeCoefficients R Y).f k χ) σ).symm))
  exact hsquare

/-- Coefficient change commutes with pullback along the given continuous map. -/
theorem singularCohomologyChangeCoefficients_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (a : singularCohomology ℤ Y n) :
    singularCohomologyChangeCoefficients R X n (singularCohomologyPullback ℤ f n a) =
      singularCohomologyPullback R f n (singularCohomologyChangeCoefficients R Y n a) := by
  /- Evaluate the two cochain composites on a singular simplex σ.
  Both values are the image in R of the original integer evaluation
  on f∘σ. The uniqueness certificate gives the cochain naturality
  square for these very maps. Apply homology and its canonical
  restriction-of-scalars comparison, and evaluate the resulting square
  on a. Neither a replacement space nor an arbitrary isomorphism occurs. -/
  let PZ := (singularCochainsFunctor ℤ).map (TopCat.ofHom f).op
  let PQ := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  have hsquare := singularCochainsChangeCoefficients_naturality R f
  -- Homology respects that square; its scalar-restriction comparison is natural.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F a) hmap
  change HomologicalComplex.homologyMap (singularCochainsChangeCoefficients R X) n
    (HomologicalComplex.homologyMap PZ n a) =
      HomologicalComplex.homologyMap ((RResC).map PQ) n
        (HomologicalComplex.homologyMap (singularCochainsChangeCoefficients R Y) n a) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map PQ) RRes
  have hnatValue := congrArg
    (fun F ↦ F (HomologicalComplex.homologyMap (singularCochainsChangeCoefficients R Y) n a))
    hnat
  change (((singularCochains R X).sc n).mapHomologyIso RRes).hom
    (HomologicalComplex.homologyMap ((RResC).map PQ) n
      (HomologicalComplex.homologyMap (singularCochainsChangeCoefficients R Y) n a)) =
        singularCohomologyPullback R f n (singularCohomologyChangeCoefficients R Y n a)
    at hnatValue
  exact (congrArg (((singularCochains R X).sc n).mapHomologyIso RRes).hom hvalue).trans
    hnatValue


/-- The value of coefficient change on each original singular simplex. -/
theorem singularCochainsChangeCoefficients_apply (X : Type u) [TopologicalSpace X]
    (n : ℕ) (a : (singularCochains ℤ X).X n)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) :
    singularCochainEquiv R X n ((singularCochainsChangeCoefficients R X).f n a) σ =
      ULift.up ((singularCochainEquiv ℤ X n a σ).down : R) :=
  (existsUnique_singularCochainsChangeCoefficients R X).exists.choose_spec n a σ

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A map into a restricted-scalar complex sends a represented cycle to the class
of its actual image, through the canonical scalar-restriction comparison. -/
theorem homologyMap_restrictScalars_cocycleClass (R S : Type) [CommRing R] [CommRing S]
    (ι : R →+* S) {shape : ComplexShape ℕ}
    (C : HomologicalComplex (ModuleCat.{u} R) shape)
    (D : HomologicalComplex (ModuleCat.{u} S) shape)
    (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
      shape).obj D) (n : ℕ)
    (a : (C.sc n).moduleCatLeftHomologyData.K)
    (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
    ((D.sc n).mapHomologyIso (ModuleCat.restrictScalars ι)).hom
      (HomologicalComplex.homologyMap F n
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a))) =
      (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
    shape n).map F
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

/-- Apply the actual integer coefficient homomorphism to the specified singular cocycle. -/
def singularCocycleChangeCoefficients (X : Type u) [TopologicalSpace X] (n : ℕ)
    (a : singularCocycles ℤ X n) : singularCocycles R X n :=
  let F := singularCochainsChangeCoefficients R X
  ⟨F.f n a.val, by
    change (singularCochains R X).dFrom n (F.f n a.val) = 0
    have h := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change (singularCochains R X).dFrom n (F.f n a.val) =
      F.next n ((singularCochains ℤ X).dFrom n a.val) at h
    have ha : (singularCochains ℤ X).dFrom n a.val = 0 := a.property
    rw [h, ha, map_zero]
    rfl⟩

/-- The original scalar-restriction homology comparison sends the changed cocycle
class to the class of the same changed cocycle. -/
theorem singularCohomologyChangeCoefficients_cocycleClass
    (X : Type u) [TopologicalSpace X] (n : ℕ) (a : singularCocycles ℤ X n) :
    singularCohomologyChangeCoefficients R X n (singularCocycleClass ℤ X n a) =
      singularCocycleClass R X n (singularCocycleChangeCoefficients R X n a) :=
  homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _
    (singularCochainsChangeCoefficients R X) n a _ rfl

/-- Coefficient change preserves the ordered Alexander--Whitney product on cochains. -/
theorem singularCochainsChangeCoefficients_cup (X : Type u) [TopologicalSpace X]
    (p q : ℕ) (a : (singularCochains ℤ X).X p) (b : (singularCochains ℤ X).X q) :
    (singularCochainsChangeCoefficients R X).f (p + q) (singularCochainCup ℤ X p q a b) =
      singularCochainCup R X p q ((singularCochainsChangeCoefficients R X).f p a)
        ((singularCochainsChangeCoefficients R X).f q b) := by
  -- Coefficient change preserves the product on the same front and back faces.
  let F := singularCochainsChangeCoefficients R X
  have heval := Classical.choose_spec (existsUnique_singularCochainsChangeCoefficients R X).exists
  have hevalCup (R : Type) [CommRing R] (a : (singularCochains R X).X p)
      (b : (singularCochains R X).X q)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋p + q⦌)) :
      singularCochainEquiv R X (p + q) (singularCochainCup R X p q a b) σ =
        singularCochainEquiv R X p a
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op σ) *
        singularCochainEquiv R X q b
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ) :=
    congrFun ((singularCochainEquiv R X (p + q)).apply_symm_apply _) σ
  apply (singularCochainEquiv R X (p + q)).injective
  funext σ
  let castValue (v : ULift.{u} ℤ) : ULift.{u} R := ULift.up (v.down : R)
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
        (heval q b back).symm).trans (hevalCup R (F.f p a) (F.f q b) σ).symm)))

/-- Coefficient change preserves the original cohomological cup product. -/
theorem singularCohomologyChangeCoefficients_cup (X : Type u) [TopologicalSpace X]
    (p q : ℕ) (a : singularCohomology ℤ X p) (b : singularCohomology ℤ X q) :
    singularCohomologyChangeCoefficients R X (p + q) (singularCohomologyCup ℤ X p q a b) =
      singularCohomologyCup R X p q (singularCohomologyChangeCoefficients R X p a)
        (singularCohomologyChangeCoefficients R X q b) := by
  -- Choose representatives in the original quotient and use the mapped-cocycle formula.
  have hrep (R : Type) [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  obtain ⟨α, hα⟩ := hrep ℤ (singularCochains ℤ X) p a
  obtain ⟨β, hβ⟩ := hrep ℤ (singularCochains ℤ X) q b
  change singularCocycleClass ℤ X p α = a at hα
  change singularCocycleClass ℤ X q β = b at hβ
  rw [← hα, ← hβ, singularCohomologyCup_cocycleClass,
    singularCohomologyChangeCoefficients_cocycleClass,
    singularCohomologyChangeCoefficients_cocycleClass,
    singularCohomologyChangeCoefficients_cocycleClass, singularCohomologyCup_cocycleClass]
  apply congrArg (singularCocycleClass R X (p + q))
  apply Subtype.ext
  exact singularCochainsChangeCoefficients_cup R X p q α.val β.val

/-- Coefficient change sends the original constant-one cocycle to constant one. -/
theorem singularCocycleChangeCoefficients_one (X : Type u) [TopologicalSpace X] :
    singularCocycleChangeCoefficients R X 0 (singularCocycleOne ℤ X) =
      singularCocycleOne R X := by
  apply Subtype.ext
  apply (singularCochainEquiv R X 0).injective
  funext σ
  change singularCochainEquiv R X 0
    ((singularCochainsChangeCoefficients R X).f 0 (singularCochainOne ℤ X)) σ =
      singularCochainEquiv R X 0 (singularCochainOne R X) σ
  rw [singularCochainsChangeCoefficients_apply]
  have hZ : singularCochainEquiv ℤ X 0 (singularCochainOne ℤ X) σ = 1 :=
    congrFun ((singularCochainEquiv ℤ X 0).apply_symm_apply _) σ
  have hR : singularCochainEquiv R X 0 (singularCochainOne R X) σ = 1 :=
    congrFun ((singularCochainEquiv R X 0).apply_symm_apply _) σ
  rw [hZ, hR]
  apply ULift.ext
  simp

/-- Coefficient change preserves the original unreduced cohomological unit. -/
theorem singularCohomologyChangeCoefficients_one (X : Type u) [TopologicalSpace X] :
    singularCohomologyChangeCoefficients R X 0 (singularCohomologyOne ℤ X) =
      singularCohomologyOne R X := by
  change singularCohomologyChangeCoefficients R X 0
    (singularCocycleClass ℤ X 0 (singularCocycleOne ℤ X)) = _
  rw [singularCohomologyChangeCoefficients_cocycleClass, singularCocycleChangeCoefficients_one]
  rfl

/-- Coefficient change commutes with the original pullback of the specified cocycle. -/
theorem singularCocycleChangeCoefficients_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (c : singularCocycles ℤ Y n) :
    singularCocycleChangeCoefficients R X n (singularCocyclePullback ℤ f n c) =
      singularCocyclePullback R f n (singularCocycleChangeCoefficients R Y n c) := by
  apply Subtype.ext
  exact congrArg (fun F ↦ F.f n c.val) (singularCochainsChangeCoefficients_naturality R f)

/-- At rational coefficients the generic map is the previously normalized original map. -/
theorem singularCochainsChangeCoefficients_rat (X : Type u) [TopologicalSpace X] :
    singularCochainsChangeCoefficients ℚ X = singularCochainsRationalization X := by
  exact (existsUnique_singularCochainsRationalization X).unique
    ((existsUnique_singularCochainsChangeCoefficients ℚ X).exists.choose_spec)
    ((existsUnique_singularCochainsRationalization X).exists.choose_spec)

/-- The generic rational specialization uses exactly the original rationalization witness. -/
theorem singularCohomologyChangeCoefficients_rat (X : Type u) [TopologicalSpace X] (n : ℕ) :
    singularCohomologyChangeCoefficients ℚ X n = singularCohomologyRationalization X n := by
  rw [singularCohomologyChangeCoefficients, singularCochainsChangeCoefficients_rat]
  rfl

end AtiyahSinger
