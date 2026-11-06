/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportCohomologyThom

/-!
# The ordinary left action and supported Thom multiplication

Public module ID: M2212.

The ordinary action associates with the two-relative union cup product on the
actual singular chain quotients. Applying this identity to the specified Thom
class proves the projection formula at each compact support and in the original
compact-support colimit. The ordinary factor is arbitrary: no relative lift or
compactness of the base is required.

Sources: Hatcher, Algebraic Topology, Section 3.2, for the Alexander--Whitney
product and relative products, and Section 3.3 for compact supports. The joint
quotient action below is an implementation of the same cochain product, used
to commute the canonical open-union comparison with ordinary multiplication.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- Ordinary cochains act on the actual dual quotient by the two subspace chain images. -/
def relativeUnionSingularCochainAction (A B : Set X) (p q : ℕ) :
    (singularCochains R X).X p →ₗ[R]
      (relativeUnionSingularCochains R A B).X q →ₗ[R]
        (relativeUnionSingularCochains R A B).X (p + q) := by
  let J := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsProjection R A B).op
  -- The right factor vanishes on each subspace, and so does its ordinary left product.
  have hkillA : singularSubspaceChains R A ≫
      relativeUnionSingularChainsProjection R A B = 0 := by
    have h := congrArg
      (fun f ↦ (biprod.inl : singularChains R A ⟶
        singularChains R A ⊞ singularChains R B) ≫ f)
      (cokernel.condition (singularSubspaceSumChains R A B))
    dsimp only [singularSubspaceSumChains] at h
    simp only [biprod.inl_desc_assoc] at h
    exact h
  have hkillB : singularSubspaceChains R B ≫
      relativeUnionSingularChainsProjection R A B = 0 := by
    have h := congrArg
      (fun f ↦ (biprod.inr : singularChains R B ⟶
        singularChains R A ⊞ singularChains R B) ≫ f)
      (cokernel.condition (singularSubspaceSumChains R A B))
    dsimp only [singularSubspaceSumChains] at h
    simp only [biprod.inr_desc_assoc] at h
    exact h
  have hvanish (C : Set X)
      (hC : singularSubspaceChains R C ≫ relativeUnionSingularChainsProjection R A B = 0)
      (a : (singularCochains R X).X p)
      (b : (relativeUnionSingularCochains R A B).X q) :
      (singularSubspaceChains R C).f (p + q) ≫
        singularCochainCup R X p q a (J.f q b) = 0 := by
    have hb : (((singularCochainDualFunctor R).map
        (singularSubspaceChains R C).op).f q) (J.f q b) = 0 := by
      change (singularSubspaceChains R C).f q ≫
        ((relativeUnionSingularChainsProjection R A B).f q ≫ b) = 0
      rw [← Category.assoc]
      have h := congrArg (fun f ↦ f.f q) hC
      change (singularSubspaceChains R C).f q ≫
        (relativeUnionSingularChainsProjection R A B).f q = 0 at h
      rw [h, zero_comp]
    let bC := (relativeSingularCochainEquiv R C q).symm ⟨J.f q b, hb⟩
    have heq : (relativeSingularCochainEquiv R C q bC).val = J.f q b :=
      congrArg Subtype.val ((relativeSingularCochainEquiv R C q).apply_symm_apply _)
    have h := singularCochainCup_mem_relative R C p q a bC
    rw [heq] at h
    exact h
  have hmem (a : (singularCochains R X).X p)
      (b : (relativeUnionSingularCochains R A B).X q) :
      (((singularCochainDualFunctor R).map
        (singularSubspaceSumChains R A B).op).f (p + q))
          (singularCochainCup R X p q a (J.f q b)) = 0 := by
    have hA := hvanish A hkillA a b
    have hB := hvanish B hkillB a b
    change (biprod.desc (singularSubspaceChains R A)
      (singularSubspaceChains R B)).f (p + q) ≫ _ = 0
    rw [biprod.desc_eq, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Preadditive.add_comp,
      Category.assoc, Category.assoc, hA, hB, comp_zero, comp_zero, add_zero]
  -- Factor exactly the ordinary cup cochain through the original joint quotient.
  exact
    { toFun := fun a ↦
        { toFun := fun b ↦ (relativeUnionSingularCochainEquiv R A B (p + q)).symm
            ⟨singularCochainCup R X p q a (J.f q b), hmem a b⟩
          map_add' := by
            intro b c
            apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
            apply Subtype.ext
            simp only [Functor.comp_obj, Functor.op_obj, map_add,
              LinearEquiv.apply_symm_apply, AddMemClass.mk_add_mk]
            exact (singularCochainCup R X p q a).map_add (J.f q b) (J.f q c)
          map_smul' := by
            intro t b
            apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
            apply Subtype.ext
            simp [map_smul] }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
        apply Subtype.ext
        simp only [Functor.comp_obj, Functor.op_obj, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply, LinearMap.add_apply, map_add, AddMemClass.mk_add_mk]
        exact congrArg (fun f ↦ f (J.f q c)) ((singularCochainCup R X p q).map_add a b)
      map_smul' := by
        intro t a
        apply LinearMap.ext
        intro b
        apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
        apply Subtype.ext
        simp only [Functor.comp_obj, Functor.op_obj, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply, RingHom.id_apply, LinearMap.smul_apply, map_smul,
          SetLike.mk_smul_mk]
        exact congrArg (fun f ↦ f (J.f q b)) ((singularCochainCup R X p q).map_smul t a) }

/-- Forgetting the two relative conditions retains the original ordinary cup cochain. -/
theorem relativeUnionSingularCochainAction_to_ordinary (A B : Set X) (p q : ℕ)
    (a : (singularCochains R X).X p)
    (b : (relativeUnionSingularCochains R A B).X q) :
    (((singularCochainDualFunctor R).map
      (relativeUnionSingularChainsProjection R A B).op).f (p + q))
        (relativeUnionSingularCochainAction R A B p q a b) =
      singularCochainCup R X p q a
        ((((singularCochainDualFunctor R).map
          (relativeUnionSingularChainsProjection R A B).op).f q) b) := by
  exact congrArg Subtype.val
    ((relativeUnionSingularCochainEquiv R A B (p + q)).apply_symm_apply _)

/-- The joint quotient action has the original Leibniz differential and degree sign. -/
theorem relativeUnionSingularCochainAction_leibniz (A B : Set X) (p q : ℕ)
    (a : (singularCochains R X).X p)
    (b : (relativeUnionSingularCochains R A B).X q) :
    (relativeUnionSingularCochains R A B).d (p + q) (p + q + 1)
        (relativeUnionSingularCochainAction R A B p q a b) =
      ((relativeUnionSingularCochains R A B).XIsoOfEq (Nat.add_right_comm p 1 q)).hom
          (relativeUnionSingularCochainAction R A B (p + 1) q
            ((singularCochains R X).d p (p + 1) a) b) +
        (-1 : R) ^ p •
          ((relativeUnionSingularCochains R A B).XIsoOfEq (Nat.add_assoc p q 1).symm).hom
            (relativeUnionSingularCochainAction R A B p (q + 1) a
              ((relativeUnionSingularCochains R A B).d q (q + 1) b)) := by
  -- The injective joint pullback commutes with differentials and degree transports.
  let C := relativeUnionSingularCochains R A B
  let J := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsProjection R A B).op
  have hd (i j : ℕ) (c : C.X i) :
      J.f j (C.d i j c) = (singularCochains R X).d i j (J.f i c) :=
    (congrArg (fun f ↦ f c) (J.comm i j)).symm
  have ht {i j : ℕ} (h : i = j) (c : C.X i) :
      J.f j ((C.XIsoOfEq h).hom c) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f i c) := by
    subst j
    rfl
  have ha := relativeUnionSingularCochainAction_to_ordinary R A B
  apply (relativeUnionSingularCochainEquiv R A B (p + q + 1)).injective
  apply Subtype.ext
  change J.f (p + q + 1) _ = J.f (p + q + 1) _
  rw [hd, ha, map_add, map_smul, ht, ht, ha, ha, hd]
  exact singularCochainCup_leibniz R X p q a (J.f q b)

/-- The Alexander--Whitney cochain product is associative on the same three faces. -/
theorem singularCochainCup_assoc (p q r : ℕ) (a : (singularCochains R X).X p)
    (b : (singularCochains R X).X q) (c : (singularCochains R X).X r) :
    ((singularCochains R X).XIsoOfEq (Nat.add_assoc p q r)).hom
      (singularCochainCup R X (p + q) r (singularCochainCup R X p q a b) c) =
        singularCochainCup R X p (q + r) a (singularCochainCup R X q r b c) := by
  have htransport {n m : ℕ} (h : n = m) (φ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋m⦌)) :
      singularCochainEquiv R X m (((singularCochains R X).XIsoOfEq h).hom φ) σ =
        singularCochainEquiv R X n φ
          ((TopCat.toSSet.obj (TopCat.of X)).map
            (eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).op σ) := by
    subst m
    simp [HomologicalComplex.XIsoOfEq]
  have hcup (i j : ℕ) (χ : (singularCochains R X).X i)
      (η : (singularCochains R X).X j)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋i + j⦌)) :
      singularCochainEquiv R X (i + j) (singularCochainCup R X i j χ η) σ =
        singularCochainEquiv R X i χ
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace i j).op σ) *
        singularCochainEquiv R X j η
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace i j).op σ) :=
    congrFun ((singularCochainEquiv R X (i + j)).apply_symm_apply _) σ
  have hmap {i j k : SimplexCategory} (f : i ⟶ j) (g : j ⟶ k)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op k)) :
      (TopCat.toSSet.obj (TopCat.of X)).map f.op
          ((TopCat.toSSet.obj (TopCat.of X)).map g.op σ) =
        (TopCat.toSSet.obj (TopCat.of X)).map (f ≫ g).op σ := by
    rw [op_comp, Functor.map_comp]
    rfl
  have hfront (i j : ℕ) (v : Fin (i + 1)) :
      ((singularCupFrontFace i j).toOrderHom v).val = v.val := rfl
  have hback (i j : ℕ) (v : Fin (j + 1)) :
      ((singularCupBackFace i j).toOrderHom v).val = i + v.val := rfl
  have hcast {i j : ℕ} (h : i = j) (v : Fin (i + 1)) :
      ((eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).toOrderHom v).val = v.val := by
    subst j
    rfl
  let e : ⦋(p + q) + r⦌ ⟶ ⦋p + (q + r)⦌ :=
    eqToHom (congrArg (fun k ↦ ⦋k⦌) (Nat.add_assoc p q r))
  have hfirst : singularCupFrontFace p q ≫ (singularCupFrontFace (p + q) r ≫ e) =
      singularCupFrontFace p (q + r) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext v
    apply Fin.ext
    change (e.toOrderHom ((singularCupFrontFace (p + q) r).toOrderHom
      ((singularCupFrontFace p q).toOrderHom v))).val = _
    rw [hcast (Nat.add_assoc p q r), hfront, hfront, hfront]
  have hmiddle : singularCupBackFace p q ≫ (singularCupFrontFace (p + q) r ≫ e) =
      singularCupFrontFace q r ≫ singularCupBackFace p (q + r) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext v
    apply Fin.ext
    change (e.toOrderHom ((singularCupFrontFace (p + q) r).toOrderHom
      ((singularCupBackFace p q).toOrderHom v))).val =
        ((singularCupBackFace p (q + r)).toOrderHom
          ((singularCupFrontFace q r).toOrderHom v)).val
    rw [hcast (Nat.add_assoc p q r), hfront, hback, hback, hfront]
  have hlast : singularCupBackFace (p + q) r ≫ e =
      singularCupBackFace q r ≫ singularCupBackFace p (q + r) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext v
    apply Fin.ext
    change (e.toOrderHom ((singularCupBackFace (p + q) r).toOrderHom v)).val =
      ((singularCupBackFace p (q + r)).toOrderHom
        ((singularCupBackFace q r).toOrderHom v)).val
    rw [hcast (Nat.add_assoc p q r), hback, hback, hback, Nat.add_assoc]
  apply (singularCochainEquiv R X (p + (q + r))).injective
  funext σ
  rw [htransport, hcup, hcup, hcup, hcup]
  simp only [hmap]
  rw [hfirst, hmiddle, hlast, mul_assoc]

/-- Ordinary left multiplication associates with the actual two-relative union cup product. -/
theorem relativeSingularCohomologyUnionCup_action_assoc
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q r : ℕ)
    (a : singularCohomology R X p) (b : relativeSingularCohomology R A q)
    (c : relativeSingularCohomology R B r) :
    (eqToIso (by rw [Nat.add_assoc]) :
      relativeSingularCohomology R (A ∪ B) ((p + q) + r) ≅
        relativeSingularCohomology R (A ∪ B) (p + (q + r))).hom
      (relativeSingularCohomologyUnionCup R A B hA hB (p + q) r
        (relativeSingularCohomologyAction R A p q a b) c) =
      relativeSingularCohomologyAction R (A ∪ B) p (q + r) a
        (relativeSingularCohomologyUnionCup R A B hA hB q r b c) := by
  /- Work first in the dual quotient by C_*(A)+C_*(B), where the ordinary
  left action is the actual cochain product. Its signed Leibniz formula
  preserves cycles and boundaries. The canonical union comparison commutes
  with that action because its composite with the ordinary cochain inclusion
  is the original relative inclusion. Finally use the same three consecutive
  simplex faces and injectivity of the open-union comparison. -/
  let O := singularCochains R X
  let C := relativeUnionSingularCochains R A B
  let D := relativeSingularCochains R (A ∪ B)
  let J := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsProjection R A B).op
  let F := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsToRelative R A B).op
  -- Use the original cocycle quotients and their canonical homology comparisons.
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
  have htransport (C : CochainComplex (ModuleCat.{u} R) ℕ) (n m : ℕ) (h : n = m)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (C.sc m).moduleCatLeftHomologyData.K)
      (hab : (C.XIsoOfEq h).hom a.val = b.val) :
      (eqToIso (congrArg (fun k ↦ C.homology k) h)).hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc m).moduleCatHomologyIso.inv ((C.sc m).moduleCatToCycles.range.mkQ b) := by
    subst m
    change a.val = b.val at hab
    have heq : a = b := Subtype.ext hab
    subst b
    rfl
  have hclosed (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (χ : (D.sc k).moduleCatLeftHomologyData.K) : D.d k (k + 1) χ.val = 0 := by
    let v : D.X k := χ.val
    have hχ : D.dFrom k v = 0 := χ.property
    have hχ' := congrArg (D.xNextIso
      (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl)).hom hχ
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at hχ'
    exact hχ'
  have hzero (D : CochainComplex (ModuleCat.{u} R) ℕ)
      (χ : (D.sc 0).moduleCatLeftHomologyData.K) (hχ : χ ∈ (D.sc 0).moduleCatToCycles.range) :
      χ = 0 := by
    obtain ⟨β, hβ⟩ := hχ
    have hval := congrArg Subtype.val hβ
    change D.dTo 0 β = χ.val at hval
    have hd : D.dTo 0 = 0 := D.shape _ _ (by
      change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
      omega)
    rw [hd] at hval
    apply Subtype.ext
    exact hval.symm
  have hprimitive (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (χ : (D.sc (k + 1)).moduleCatLeftHomologyData.K)
      (hχ : χ ∈ (D.sc (k + 1)).moduleCatToCycles.range) :
      ∃ β : D.X k, D.d k (k + 1) β = χ.val := by
    obtain ⟨β, hβ⟩ := hχ
    have hval := congrArg Subtype.val hβ
    change D.dTo (k + 1) β = χ.val at hval
    have hrel : (ComplexShape.up ℕ).Rel k (k + 1) := rfl
    refine ⟨(D.xPrevIso hrel).hom β, ?_⟩
    have hcomp := congrArg (fun f : D.xPrev (k + 1) ⟶ D.X (k + 1) ↦ f β)
      (D.dTo_eq hrel)
    exact hcomp.symm.trans hval
  have hboundary (D : CochainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ)
      (hij : (ComplexShape.up ℕ).Rel i j)
      (χ : (D.sc j).moduleCatLeftHomologyData.K) (β : D.X i) (hβ : D.d i j β = χ.val) :
      χ ∈ (D.sc j).moduleCatToCycles.range := by
    refine ⟨(D.xPrevIso hij).inv β, ?_⟩
    apply Subtype.ext
    change D.dTo j ((D.xPrevIso hij).inv β) = χ.val
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo]
    exact hβ
  obtain ⟨α, hα⟩ := hrep O p a
  change singularCocycleClass R X p α = a at hα
  -- Fix the ordinary cocycle and descend its action on the joint right factor.
  let act := relativeUnionSingularCochainAction R A B
  have hactclosed (n : ℕ) (δ : (C.sc n).moduleCatLeftHomologyData.K) :
      C.dFrom (p + n) (act p n α.val δ.val) = 0 := by
    have h := relativeUnionSingularCochainAction_leibniz R A B p n α.val δ.val
    rw [hclosed O p α, hclosed C n δ] at h
    simp only [map_zero, LinearMap.zero_apply, zero_add, smul_zero] at h
    rw [HomologicalComplex.dFrom_eq
      (r := show (ComplexShape.up ℕ).Rel (p + n) (p + n + 1) from rfl),
      ModuleCat.comp_apply, h, map_zero]
  let actc (n : ℕ) : (C.sc n).moduleCatLeftHomologyData.K →ₗ[R]
      (C.sc (p + n)).moduleCatLeftHomologyData.K :=
    { toFun := fun δ ↦ ⟨act p n α.val δ.val, hactclosed n δ⟩
      map_add' := by
        intro δ ε
        apply Subtype.ext
        exact (act p n α.val).map_add δ.val ε.val
      map_smul' := by
        intro t δ
        apply Subtype.ext
        exact (act p n α.val).map_smul t δ.val }
  have hactboundary (n : ℕ) (δ : (C.sc n).moduleCatLeftHomologyData.K)
      (hδ : δ ∈ (C.sc n).moduleCatToCycles.range) :
      actc n δ ∈ (C.sc (p + n)).moduleCatToCycles.range := by
    cases n with
    | zero =>
      rw [hzero C δ hδ, map_zero]
      exact Submodule.zero_mem _
    | succ k =>
      obtain ⟨ε, hε⟩ := hprimitive C k δ hδ
      have h := relativeUnionSingularCochainAction_leibniz R A B p k α.val ε
      rw [hclosed O p α, hε] at h
      simp only [map_zero, LinearMap.zero_apply, zero_add] at h
      -- The sign is its own inverse, so the actual joint primitive is (-1)^p α cup ε.
      apply hboundary C (p + k) (p + (k + 1)) (by
        change p + k + 1 = p + (k + 1)
        omega) (actc (k + 1) δ) ((-1 : R) ^ p • act p k α.val ε)
      change C.d (p + k) (p + (k + 1))
        ((-1 : R) ^ p • act p k α.val ε) = act p (k + 1) α.val δ.val
      apply (ModuleCat.mono_iff_injective
        (C.XIsoOfEq (Nat.add_assoc p k 1).symm).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom,
        map_smul, h, smul_smul, ← pow_add]
      have hsign : (-1 : R) ^ (p + p) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hsign, one_smul]
  let actQ (n : ℕ) := (C.sc n).moduleCatToCycles.range.liftQ
    (((C.sc (p + n)).moduleCatToCycles.range).mkQ.comp (actc n)) (by
      intro δ hδ
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hactboundary n δ hδ))
  let actH (n : ℕ) : C.homology n →ₗ[R] C.homology (p + n) :=
    (((C.sc (p + n)).moduleCatHomologyIso.inv.hom).comp (actQ n)).comp
      (C.sc n).moduleCatHomologyIso.hom.hom
  have hactH (n : ℕ) (δ : (C.sc n).moduleCatLeftHomologyData.K) :
      actH n ((C.sc n).moduleCatHomologyIso.inv
        ((C.sc n).moduleCatToCycles.range.mkQ δ)) =
      (C.sc (p + n)).moduleCatHomologyIso.inv
        ((C.sc (p + n)).moduleCatToCycles.range.mkQ (actc n δ)) := by
    change (C.sc (p + n)).moduleCatHomologyIso.inv
      (actQ n ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv
          ((C.sc n).moduleCatToCycles.range.mkQ δ)))) = _
    rw [Iso.inv_hom_id_apply]
    rfl
  -- The same original quotient map intertwines relative and joint multiplication.
  let JD := (singularCochainDualFunctor R).map
    (relativeSingularChainsProjection R (A ∪ B)).op
  have hprojection : F ≫ J = JD := by
    change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp]
    have h : relativeUnionSingularChainsProjection R A B ≫
        relativeUnionSingularChainsToRelative R A B =
      relativeSingularChainsProjection R (A ∪ B) := cokernel.π_desc _ _ _
    rw [h]
  have hFJ (n : ℕ) (δ : D.X n) : J.f n (F.f n δ) = JD.f n δ :=
    congrArg (fun f ↦ f.f n δ) hprojection
  have hrelative (T : Set X) (i j : ℕ) (η : O.X i)
      (δ : (relativeSingularCochains R T).X j) :
      (((singularCochainDualFunctor R).map
        (relativeSingularChainsProjection R T).op).f (i + j))
          (relativeSingularCochainAction R T i j η δ) =
        singularCochainCup R X i j η
          ((((singularCochainDualFunctor R).map
            (relativeSingularChainsProjection R T).op).f j) δ) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R T (i + j)).apply_symm_apply _)
  have hFcochain (n : ℕ) (δ : D.X n) :
      F.f (p + n) (relativeSingularCochainAction R (A ∪ B) p n α.val δ) =
        act p n α.val (F.f n δ) := by
    apply (relativeUnionSingularCochainEquiv R A B (p + n)).injective
    apply Subtype.ext
    change J.f (p + n) _ = J.f (p + n) _
    rw [hFJ, hrelative, relativeUnionSingularCochainAction_to_ordinary, hFJ]
  have hcompare (n : ℕ) (x : D.homology n) :
      relativeUnionCohomologyComparison R A B (p + n)
        (relativeSingularCohomologyAction R (A ∪ B) p n
          (singularCocycleClass R X p α) x) =
        actH n (relativeUnionCohomologyComparison R A B n x) := by
    obtain ⟨δ, hδ⟩ := hrep D n x
    let ε : (C.sc n).moduleCatLeftHomologyData.K := ⟨F.f n δ.val, by
      change C.dFrom n (F.f n δ.val) = 0
      have h := congrArg (fun f ↦ f δ.val) (F.comm_from n)
      change C.dFrom n (F.f n δ.val) = F.next n (D.dFrom n δ.val) at h
      rw [h, show D.dFrom n δ.val = 0 from δ.property, map_zero]⟩
    have hε := hclass D C F n δ ε rfl
    change relativeUnionCohomologyComparison R A B n
      (relativeSingularCocycleClass R (A ∪ B) n δ) = _ at hε
    change relativeSingularCocycleClass R (A ∪ B) n δ = x at hδ
    rw [← hδ, relativeSingularCohomologyAction_cocycleClass, hε, hactH]
    apply hclass D C F (p + n)
    exact hFcochain n δ.val
  -- Associate the three original cochains before taking their same quotient classes.
  let JA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  have hjoint (i j : ℕ) (β : (relativeSingularCochains R A).X i)
      (γ : (relativeSingularCochains R B).X j) :
      J.f (i + j) (relativeUnionSingularCochainCup R A B i j β γ) =
        singularCochainCup R X i j (JA.f i β) (JB.f j γ) :=
    congrArg Subtype.val
      ((relativeUnionSingularCochainEquiv R A B (i + j)).apply_symm_apply _)
  have ht {i j : ℕ} (h : i = j) (δ : C.X i) :
      J.f j ((C.XIsoOfEq h).hom δ) = (O.XIsoOfEq h).hom (J.f i δ) := by
    subst j
    rfl
  have hcompt {i j : ℕ} (h : i = j) (x : D.homology i) :
      relativeUnionCohomologyComparison R A B j
          ((eqToIso (congrArg (fun n ↦ D.homology n) h)).hom x) =
        (eqToIso (congrArg (fun n ↦ C.homology n) h)).hom
          (relativeUnionCohomologyComparison R A B i x) := by
    subst j
    rfl
  obtain ⟨β, hβ⟩ := hrep (relativeSingularCochains R A) q b
  obtain ⟨γ, hγ⟩ := hrep (relativeSingularCochains R B) r c
  change relativeSingularCocycleClass R A q β = b at hβ
  change relativeSingularCocycleClass R B r γ = c at hγ
  rw [← hα, ← hβ, ← hγ, relativeSingularCohomologyAction_cocycleClass]
  apply (relativeUnionCohomologyComparison_bijective R A B hA hB (p + (q + r))).injective
  rw [hcompt (Nat.add_assoc p q r), relativeSingularCohomologyUnionCup_cocycleClass,
    hcompare, relativeSingularCohomologyUnionCup_cocycleClass]
  refine (htransport C ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    (relativeUnionSingularCocycleCup R A B (p + q) r
      (relativeSingularCocycleAction R A p q α β) γ)
    (actc (q + r) (relativeUnionSingularCocycleCup R A B q r β γ)) ?_).trans
      (hactH (q + r) (relativeUnionSingularCocycleCup R A B q r β γ)).symm
  apply (relativeUnionSingularCochainEquiv R A B (p + (q + r))).injective
  apply Subtype.ext
  change J.f (p + (q + r)) ((C.XIsoOfEq (Nat.add_assoc p q r)).hom
    (relativeUnionSingularCochainCup R A B (p + q) r
      (relativeSingularCochainAction R A p q α.val β.val) γ.val)) =
      J.f (p + (q + r)) (act p (q + r) α.val
        (relativeUnionSingularCochainCup R A B q r β.val γ.val))
  rw [ht, hjoint, hrelative, relativeUnionSingularCochainAction_to_ordinary, hjoint]
  exact singularCochainCup_assoc R p q r α.val (JA.f q β.val) (JB.f r γ.val)

section Bundle

variable (r : ℕ) [T2Space X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

/-- Supported Thom multiplication intertwines the ordinary left action on the same support. -/
theorem supportedCohomologyThomMap_action (K : Compacts X) (q p : ℕ)
    (b : singularCohomology R X q)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) p) :
    (eqToIso (by rw [Nat.add_assoc]) :
      relativeSingularCohomology R
        ((supportedCohomologyThomSupport r E K : Set
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) ((q + p) + r) ≅
      relativeSingularCohomology R
        ((supportedCohomologyThomSupport r E K : Set
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) (q + (p + r))).hom
      (supportedCohomologyThomMap R r E o K (q + p)
        (relativeSingularCohomologyAction R ((K : Set X)ᶜ) q p b a)) =
      relativeSingularCohomologyAction R
        ((supportedCohomologyThomSupport r E K : Set
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) q (p + r)
        (singularCohomologyPullback R (bundleProjection r E) q b)
        (supportedCohomologyThomMap R r E o K p a) := by
  /- Pullback commutes with the ordinary-relative action. Associate that
  action with the actual two-relative cup with the specified Thom class.
  The equality identifying the union with the zero-section support complement
  only transports the relative subset; it changes neither factor nor support. -/
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
  let B := bundleNonzero r E
  let S := ((supportedCohomologyThomSupport r E K : Set T)ᶜ)
  let hOpen := isOpen_supportedCohomologyThomSubspaces r E K
  let hS : A ∪ B = S := supportedCohomologyThomSupport_compl r E K
  let hπ : Set.MapsTo (bundleProjection r E) A ((K : Set X)ᶜ) := fun _ hx ↦ hx
  let compare (n : ℕ) := eqToIso
    (congrArg (fun C ↦ relativeSingularCohomology R C n) hS)
  have hset (C D : Set T) (h : C = D) (i j : ℕ)
      (x : singularCohomology R T i) (y : relativeSingularCohomology R C j) :
      (eqToIso (congrArg (fun U ↦ relativeSingularCohomology R U (i + j)) h)).hom
        (relativeSingularCohomologyAction R C i j x y) =
      relativeSingularCohomologyAction R D i j x
        ((eqToIso (congrArg (fun U ↦ relativeSingularCohomology R U j) h)).hom y) := by
    subst D
    rfl
  have hdegree (C D : Set T) (h : C = D) {i j : ℕ} (hij : i = j)
      (x : relativeSingularCohomology R C i) :
      (eqToIso (congrArg (fun n ↦ relativeSingularCohomology R D n) hij)).hom
        ((eqToIso (congrArg (fun U ↦ relativeSingularCohomology R U i) h)).hom x) =
      (eqToIso (congrArg (fun U ↦ relativeSingularCohomology R U j) h)).hom
        ((eqToIso (congrArg (fun n ↦ relativeSingularCohomology R C n) hij)).hom x) := by
    subst D
    subst j
    rfl
  change (eqToIso (congrArg (fun n ↦ relativeSingularCohomology R S n)
      (Nat.add_assoc q p r))).hom
    ((compare ((q + p) + r)).hom
      (relativeSingularCohomologyUnionCup R A B hOpen.1 hOpen.2 (q + p) r
        (relativeSingularCohomologyPullback R (bundleProjection r E) hπ (q + p)
          (relativeSingularCohomologyAction R ((K : Set X)ᶜ) q p b a))
        (cohomologyThomClass R r E o))) =
    relativeSingularCohomologyAction R S q (p + r)
      (singularCohomologyPullback R (bundleProjection r E) q b)
      ((compare (p + r)).hom
        (relativeSingularCohomologyUnionCup R A B hOpen.1 hOpen.2 p r
          (relativeSingularCohomologyPullback R (bundleProjection r E) hπ p a)
          (cohomologyThomClass R r E o)))
  rw [relativeSingularCohomologyPullback_action,
    hdegree (A ∪ B) S hS (Nat.add_assoc q p r), ← hset (A ∪ B) S hS]
  exact congrArg (compare (q + (p + r))).hom
    (relativeSingularCohomologyUnionCup_action_assoc R A B hOpen.1 hOpen.2 q p r
      (singularCohomologyPullback R (bundleProjection r E) q b)
      (relativeSingularCohomologyPullback R (bundleProjection r E) hπ p a)
      (cohomologyThomClass R r E o))

/-- The actual compact-support Thom map intertwines arbitrary ordinary left multiplication. -/
theorem compactSupportCohomologyThomMap_action (q p : ℕ)
    (b : singularCohomology R X q) (a : compactSupportCohomology R X p) :
    (eqToIso (by rw [Nat.add_assoc]) :
      compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) ((q + p) + r) ≅
        compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
          (q + (p + r))).hom
      (compactSupportCohomologyThomMap R r E o (q + p)
        (compactSupportCohomologyAction R X q p b a)) =
      compactSupportCohomologyAction R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
        q (p + r) (singularCohomologyPullback R (bundleProjection r E) q b)
        (compactSupportCohomologyThomMap R r E o p a) := by
  -- Both sides use the same representative K and the same zero-section support over K.
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  have htransport (K : Compacts T) {i j : ℕ} (h : i = j)
      (c : relativeSingularCohomology R ((K : Set T)ᶜ) i) :
      (eqToIso (congrArg (fun n ↦ compactSupportCohomology R T n) h)).hom
          (compactSupportCohomologyClass R T K i c) =
        compactSupportCohomologyClass R T K j
          ((eqToIso (congrArg
            (fun n ↦ relativeSingularCohomology R ((K : Set T)ᶜ) n) h)).hom c) := by
    subst j
    rfl
  obtain ⟨K, α, hα⟩ := compactSupportCohomology_exists_representative R X p a
  rw [← hα, compactSupportCohomologyAction_representative,
    compactSupportCohomologyThomMap_representative,
    compactSupportCohomologyThomMap_representative,
    compactSupportCohomologyAction_representative,
    htransport (supportedCohomologyThomSupport r E K) (Nat.add_assoc q p r)]
  exact congrArg (compactSupportCohomologyClass R T
    (supportedCohomologyThomSupport r E K) (q + (p + r)))
      (supportedCohomologyThomMap_action R r E o K q p b α)

end Bundle

end AtiyahSinger
