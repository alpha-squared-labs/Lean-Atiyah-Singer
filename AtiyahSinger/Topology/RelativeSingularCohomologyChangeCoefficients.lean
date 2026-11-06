/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyRationalization
public import AtiyahSinger.Topology.SingularCohomologyChangeCoefficients

/-!
# Integral coefficient change for the actual relative complex

Public module ID: M2088.

The specified ordinary coefficient map preserves the cochains vanishing on
an arbitrary subspace. Its restriction defines the original relative map,
with the same quotient projection, pair pullbacks and ordered cup action.
The target is an arbitrary commutative ring; no tensor description of its
cohomology or injectivity of the integer coefficient homomorphism is assumed.
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

/-- The original ordinary coefficient map uniquely restricts to the actual relative cochains. -/
theorem existsUnique_relativeSingularCochainsChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    ∃! f : relativeSingularCochains ℤ A ⟶ (RResC).obj (relativeSingularCochains R A),
      f ≫ (RResC).map
          ((singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op) =
        (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op ≫
          singularCochainsChangeCoefficients R X := by
  /- Stage 1: relativeSingularCochainEquiv identifies each original relative
  cochain with its actual ordinary cochain vanishing on A. The specified
  singularCochainsChangeCoefficients R changes each original simplex value by
  integer coefficient change. In particular, a zero evaluation on a simplex of A
  stays zero. Its target cochain therefore belongs to the same relative
  kernel, and the inverse relative cochain equivalence gives the required
  degreewise map, linear over the original integer coefficients.
  Stage 2: both original inclusions into ordinary cochains commute with
  the differentials. The ordinary coefficient change does as well. Their
  injective degreewise inclusions therefore show that the restricted maps
  commute with differentials, giving the displayed cochain-map square.
  Stage 3: an original relative cochain is determined by its composite
  with the relative chain quotient projection. Thus the square fixes every
  degreewise value and proves uniqueness of the whole map. No generator
  of a cohomology group or independent target scale is chosen. -/
  classical
  let JZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JQ := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let FX := singularCochainsChangeCoefficients R X
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
  -- Integer coefficient change preserves the actual vanishing kernel on A.
  have hvanish (n : ℕ) (φ : (relativeSingularCochains ℤ A).X n) :
      ((singularCochainDualFunctor R).map (singularSubspaceChains R A).op).f n
        (FX.f n (JZ.f n φ)) = 0 := by
    apply (singularCochainEquiv R A n).injective
    funext σ
    let τ := (TopCat.toSSet.map (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))).app (op ⦋n⦌) σ
    have hz := (relativeSingularCochainEquiv ℤ A n φ).property
    have hvalue := congrArg (fun χ ↦ singularCochainEquiv ℤ A n χ σ) hz
    have hzero : singularCochainEquiv ℤ X n (JZ.f n φ) τ = 0 :=
      (hpull ℤ n (JZ.f n φ) σ).symm.trans
        (hvalue.trans (congrFun (singularCochainEquiv ℤ A n).map_zero σ))
    have hcoeff := Classical.choose_spec
      (existsUnique_singularCochainsChangeCoefficients R X).exists
      n (JZ.f n φ) τ
    have hcast := congrArg
      (fun z : ULift.{u} ℤ ↦ (ULift.up (z.down : R) : ULift.{u} R)) hzero
    have hcastZero : (ULift.up ((0 : ULift.{u} ℤ).down : R) : ULift.{u} R) = 0 := by
      apply ULift.ext
      simp
    exact (hpull R n (FX.f n (JZ.f n φ)) σ).trans
      (hcoeff.trans (hcast.trans (hcastZero.trans
        (congrFun (singularCochainEquiv R A n).map_zero σ).symm)))
  let component (n : ℕ) : (relativeSingularCochains ℤ A).X n →ₛₗ[Int.castRingHom R]
      (relativeSingularCochains R A).X n :=
    { toFun := fun φ ↦ (relativeSingularCochainEquiv R A n).symm
        ⟨FX.f n (JZ.f n φ), hvanish n φ⟩
      map_add' := by
        intro φ ψ
        apply (relativeSingularCochainEquiv R A n).injective
        simp only [map_add, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        rfl
      map_smul' := by
        intro r φ
        apply (relativeSingularCochainEquiv R A n).injective
        simp only [map_smul, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        change FX.f n (JZ.f n (r • φ)) =
          (r : R) • (show (singularCochains R X).X n from FX.f n (JZ.f n φ))
        rw [map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
        rfl }
  have hcomponent (n : ℕ) (φ : (relativeSingularCochains ℤ A).X n) :
      JQ.f n (component n φ) = FX.f n (JZ.f n φ) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A n).apply_symm_apply _)
  -- The injective quotient-dual inclusion checks all differential squares.
  let F : relativeSingularCochains ℤ A ⟶ (RResC).obj (relativeSingularCochains R A) :=
    { f := fun n ↦ ModuleCat.semilinearMapAddEquiv (Int.castRingHom R)
        ((relativeSingularCochains ℤ A).X n) ((relativeSingularCochains R A).X n) (component n)
      comm' := by
        intro n m _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply (relativeSingularCochainEquiv R A m).injective
        apply Subtype.ext
        change JQ.f m ((relativeSingularCochains R A).d n m (component n φ)) =
          JQ.f m (component m ((relativeSingularCochains ℤ A).d n m φ))
        have hJQ := congrArg (fun f ↦ f (component n φ)) (JQ.comm n m)
        have hJZ := congrArg (fun f ↦ f φ) (JZ.comm n m)
        have hFX := congrArg (fun f ↦ f (JZ.f n φ)) (FX.comm n m)
        exact hJQ.symm.trans
          ((congrArg ((singularCochains R X).d n m) (hcomponent n φ)).trans
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
    apply (relativeSingularCochainEquiv R A n).injective
    apply Subtype.ext
    exact (congrArg (fun f ↦ f.f n φ) hG).trans (hcomponent n φ).symm

/-- The actual relative coefficient change fixed by the original ordinary cochain square. -/
def relativeSingularCochainsChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    relativeSingularCochains ℤ A ⟶ (RResC).obj (relativeSingularCochains R A) :=
  Classical.choose (existsUnique_relativeSingularCochainsChangeCoefficients R A).exists

/-- Relative coefficient change followed by the canonical homology comparison. -/
def relativeSingularCohomologyChangeCoefficients
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    relativeSingularCohomology ℤ A n ⟶ (RRes).obj (relativeSingularCohomology R A n) :=
  HomologicalComplex.homologyMap (relativeSingularCochainsChangeCoefficients R A) n ≫
    (((relativeSingularCochains R A).sc n).mapHomologyIso RRes).hom

/-- Relative coefficient change commutes with pullback along the same continuous pair map. -/
theorem relativeSingularCohomologyChangeCoefficients_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ)
    (b : relativeSingularCohomology ℤ B n) :
    relativeSingularCohomologyChangeCoefficients R A n
        (relativeSingularCohomologyPullback ℤ f hf n b) =
      relativeSingularCohomologyPullback R f hf n
        (relativeSingularCohomologyChangeCoefficients R B n b) := by
  /- Stage 1: the ordinary coefficient map commutes with precomposition
  by the same continuous f, since both composites evaluate a cochain on
  f composed with the original simplex and then map that integer into R.
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
          singularCochainsChangeCoefficients R V =
        singularCochainsChangeCoefficients R W ≫ (RResC).map
          ((singularCochainsFunctor R).map (TopCat.ofHom g).op) :=
    singularCochainsChangeCoefficients_naturality R g
  -- The two pair pullbacks commute with their original quotient-dual inclusions.
  let PZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsMap ℤ f hf).op
  let PQ := (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op
  let JZA := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JZB := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ B).op
  let JQA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JQB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  let OZ := (singularCochainsFunctor ℤ).map (TopCat.ofHom f).op
  let OQ := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  let FA := relativeSingularCochainsChangeCoefficients R A
  let FB := relativeSingularCochainsChangeCoefficients R B
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
  have hFA := Classical.choose_spec
    (existsUnique_relativeSingularCochainsChangeCoefficients R A).exists
  have hFB := Classical.choose_spec
    (existsUnique_relativeSingularCochainsChangeCoefficients R B).exists
  have hsquare : PZ ≫ FA = FB ≫ (RResC).map PQ := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    apply (relativeSingularCochainEquiv R A k).injective
    apply Subtype.ext
    change JQA.f k (FA.f k (PZ.f k χ)) = JQA.f k (PQ.f k (FB.f k χ))
    have h₁ := congrArg (fun F ↦ F.f k (PZ.f k χ)) hFA
    have h₂ := congrArg (fun F ↦ F.f k χ) (hprojection ℤ)
    have h₃ := congrArg (fun F ↦ F.f k (JZB.f k χ)) (hordinarySquare f)
    have h₄ := congrArg (fun F ↦ F.f k χ) hFB
    have h₅ := congrArg (fun F ↦ F.f k (FB.f k χ)) (hprojection R)
    exact h₁.trans ((congrArg ((singularCochainsChangeCoefficients R X).f k) h₂).trans
      (h₃.trans ((congrArg (OQ.f k) h₄.symm).trans h₅.symm)))
  -- Pass through homology and its natural comparison for restriction of scalars.
  have hmap := congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun F ↦ F b) hmap
  change HomologicalComplex.homologyMap FA n (HomologicalComplex.homologyMap PZ n b) =
    HomologicalComplex.homologyMap ((RResC).map PQ) n
      (HomologicalComplex.homologyMap FB n b) at hvalue
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map PQ) RRes
  have hnatValue := congrArg (fun F ↦ F (HomologicalComplex.homologyMap FB n b)) hnat
  change (((relativeSingularCochains R A).sc n).mapHomologyIso RRes).hom
    (HomologicalComplex.homologyMap ((RResC).map PQ) n
      (HomologicalComplex.homologyMap FB n b)) =
        relativeSingularCohomologyPullback R f hf n
          (relativeSingularCohomologyChangeCoefficients R B n b) at hnatValue
  exact (congrArg (((relativeSingularCochains R A).sc n).mapHomologyIso RRes).hom
    hvalue).trans hnatValue

/-- Forgetting the original relative condition commutes with normalized coefficient change. -/
theorem relativeSingularCohomologyChangeCoefficients_toOrdinary
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (a : relativeSingularCohomology ℤ A n) :
    singularCohomologyChangeCoefficients R X n (relativeSingularCohomologyToOrdinary ℤ A n a) =
      relativeSingularCohomologyToOrdinary R A n
        (relativeSingularCohomologyChangeCoefficients R A n a) := by
  /- The unique cochain map was chosen to commute with precisely the
  duals of the original relative quotient projections. Those dual maps
  induce relativeSingularCohomologyToOrdinary. Apply homology to the
  defining square, then use naturality of the canonical restriction-of-
  scalars comparison to identify its two targets with the original
  target cohomology modules. Evaluate on a to obtain this equality. -/
  -- Use exactly the square specifying the original relative coefficient map.
  let F := relativeSingularCochainsChangeCoefficients R A
  let JZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JQ := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  have hsquare : JZ ≫ singularCochainsChangeCoefficients R X = F ≫ (RResC).map JQ :=
    (Classical.choose_spec
      (existsUnique_relativeSingularCochainsChangeCoefficients R A).exists).symm
  have hmap := congrArg (fun G ↦ HomologicalComplex.homologyMap G n) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hmap
  have hvalue := congrArg (fun G ↦ G a) hmap
  change HomologicalComplex.homologyMap (singularCochainsChangeCoefficients R X) n
    (HomologicalComplex.homologyMap JZ n a) =
      HomologicalComplex.homologyMap ((RResC).map JQ) n
        (HomologicalComplex.homologyMap F n a) at hvalue
  -- The native comparison returns to the same ordinary cohomology object over R.
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map JQ) RRes
  have hnatValue := congrArg (fun G ↦ G (HomologicalComplex.homologyMap F n a)) hnat
  change (((singularCochains R X).sc n).mapHomologyIso RRes).hom
    (HomologicalComplex.homologyMap ((RResC).map JQ) n
      (HomologicalComplex.homologyMap F n a)) =
        relativeSingularCohomologyToOrdinary R A n
          (relativeSingularCohomologyChangeCoefficients R A n a) at hnatValue
  exact (congrArg (((singularCochains R X).sc n).mapHomologyIso RRes).hom hvalue).trans
    hnatValue

/-- Coefficient change preserves the original ordinary-relative cup action and its order. -/
theorem relativeSingularCohomologyChangeCoefficients_action
    {X : Type u} [TopologicalSpace X] (A : Set X) (p q : ℕ)
    (a : singularCohomology ℤ X p) (b : relativeSingularCohomology ℤ A q) :
    relativeSingularCohomologyChangeCoefficients R A (p + q)
        (relativeSingularCohomologyAction ℤ A p q a b) =
      relativeSingularCohomologyAction R A p q
        (singularCohomologyChangeCoefficients R X p a)
        (relativeSingularCohomologyChangeCoefficients R A q b) := by
  /- Stage 1: choose original cocycles for a and b. The relative cocycle
  is an ordinary cocycle vanishing on A through the same quotient-dual
  inclusion. The original Alexander--Whitney formula evaluates a on the
  front face and b on the back face. Integer coefficient change preserves this
  product, the face maps and the vanishing condition on A.
  Stage 2: the unique relative coefficient square identifies that actual
  changed-coefficient product with the product of the two coefficient images.
  Passing through the original cocycle/coboundary quotients and canonical
  homology comparisons gives the stated formula. The ordinary factor
  remains first and the relative factor second; no graded interchange,
  degree subtraction, excision or tensor-cohomology isomorphism is used. -/
  -- Retain the original quotient classes and the mapped homology comparison.
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
  -- Coefficient change preserves the product on the same front and back faces.
  let F := singularCochainsChangeCoefficients R X
  have heval := Classical.choose_spec (existsUnique_singularCochainsChangeCoefficients R X).exists
  have hcup (a : (singularCochains ℤ X).X p) (b : (singularCochains ℤ X).X q) :
      F.f (p + q) (singularCochainCup ℤ X p q a b) =
        singularCochainCup R X p q (F.f p a) (F.f q b) := by
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
  -- Compare the ordered relative action after its injective ordinary inclusion.
  let FR := relativeSingularCochainsChangeCoefficients R A
  let JZ := (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op
  let JQ := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  have hsquare := Classical.choose_spec
    (existsUnique_relativeSingularCochainsChangeCoefficients R A).exists
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
        relativeSingularCochainAction R A p q (F.f p a) (FR.f q b) := by
    apply (relativeSingularCochainEquiv R A (p + q)).injective
    apply Subtype.ext
    have h₁ := congrArg
      (fun G ↦ G.f (p + q) (relativeSingularCochainAction ℤ A p q a b)) hsquare
    have h₂ := haction ℤ a b
    have h₃ := hcup a (JZ.f q b)
    have h₄ := congrArg (fun G ↦ G.f q b) hsquare
    have h₅ := haction R (F.f p a) (FR.f q b)
    exact h₁.trans ((congrArg (F.f (p + q)) h₂).trans
      (h₃.trans ((congrArg (singularCochainCup R X p q (F.f p a)) h₄.symm).trans h₅.symm)))
  -- Choose original ordinary and relative cocycles and descend the same cochain identity.
  obtain ⟨α, hα⟩ := hrep ℤ (singularCochains ℤ X) p a
  obtain ⟨β, hβ⟩ := hrep ℤ (relativeSingularCochains ℤ A) q b
  obtain ⟨αQ, hαQ⟩ := hcycles ℤ R (Int.castRingHom R)
    (singularCochains ℤ X) (singularCochains R X) F p α
  obtain ⟨βQ, hβQ⟩ := hcycles ℤ R (Int.castRingHom R)
    (relativeSingularCochains ℤ A) (relativeSingularCochains R A) FR q β
  have hαclass : singularCohomologyChangeCoefficients R X p (singularCocycleClass ℤ X p α) =
      singularCocycleClass R X p αQ :=
    homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _ F p α αQ hαQ.symm
  have hβclass : relativeSingularCohomologyChangeCoefficients R A q
      (relativeSingularCocycleClass ℤ A q β) = relativeSingularCocycleClass R A q βQ :=
    homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _ FR q β βQ hβQ.symm
  have hproduct : relativeSingularCohomologyChangeCoefficients R A (p + q)
      (relativeSingularCocycleClass ℤ A (p + q)
        (relativeSingularCocycleAction ℤ A p q α β)) =
      relativeSingularCocycleClass R A (p + q)
        (relativeSingularCocycleAction R A p q αQ βQ) := by
    apply homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _ FR (p + q)
    change FR.f (p + q) (relativeSingularCochainAction ℤ A p q α.val β.val) =
      relativeSingularCochainAction R A p q αQ.val βQ.val
    rw [hαQ, hβQ]
    exact hrelative α.val β.val
  change singularCocycleClass ℤ X p α = a at hα
  change relativeSingularCocycleClass ℤ A q β = b at hβ
  rw [← hα, ← hβ, relativeSingularCohomologyAction_cocycleClass, hαclass, hβclass,
    relativeSingularCohomologyAction_cocycleClass]
  exact hproduct

/-- The specified integral relative cocycle changes coefficients on its actual vanishing cochain. -/
def relativeSingularCocycleChangeCoefficients {X : Type u} [TopologicalSpace X]
    (A : Set X) (n : ℕ) (a : relativeSingularCocycles ℤ A n) :
    relativeSingularCocycles R A n :=
  let F := relativeSingularCochainsChangeCoefficients R A
  ⟨F.f n a.val, by
    change (relativeSingularCochains R A).dFrom n (F.f n a.val) = 0
    have h := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change (relativeSingularCochains R A).dFrom n (F.f n a.val) =
      F.next n ((relativeSingularCochains ℤ A).dFrom n a.val) at h
    have ha : (relativeSingularCochains ℤ A).dFrom n a.val = 0 := a.property
    rw [h, ha, map_zero]
    rfl⟩

/-- Relative coefficient change preserves the class of the actual mapped cocycle. -/
theorem relativeSingularCohomologyChangeCoefficients_cocycleClass
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (a : relativeSingularCocycles ℤ A n) :
    relativeSingularCohomologyChangeCoefficients R A n (relativeSingularCocycleClass ℤ A n a) =
      relativeSingularCocycleClass R A n (relativeSingularCocycleChangeCoefficients R A n a) :=
  homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _
    (relativeSingularCochainsChangeCoefficients R A) n a _ rfl

/-- The generic rational specialization is the original relative cochain rationalization. -/
theorem relativeSingularCochainsChangeCoefficients_rat {X : Type u} [TopologicalSpace X]
    (A : Set X) :
    relativeSingularCochainsChangeCoefficients ℚ A = relativeSingularCochainsRationalization A := by
  have h := (existsUnique_relativeSingularCochainsChangeCoefficients ℚ A).exists.choose_spec
  change relativeSingularCochainsChangeCoefficients ℚ A ≫
      ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        ((singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op) =
    (singularCochainDualFunctor ℤ).map (relativeSingularChainsProjection ℤ A).op ≫
      singularCochainsChangeCoefficients ℚ X at h
  rw [singularCochainsChangeCoefficients_rat] at h
  exact (existsUnique_relativeSingularCochainsRationalization A).unique h
    (existsUnique_relativeSingularCochainsRationalization A).exists.choose_spec

/-- Relative rational specialization retains the original cohomology comparison and witness. -/
theorem relativeSingularCohomologyChangeCoefficients_rat {X : Type u} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    relativeSingularCohomologyChangeCoefficients ℚ A n =
      relativeSingularCohomologyRationalization A n := by
  rw [relativeSingularCohomologyChangeCoefficients, relativeSingularCochainsChangeCoefficients_rat]
  rfl

end AtiyahSinger
