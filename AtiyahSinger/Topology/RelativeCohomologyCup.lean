/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCochainCup
public import AtiyahSinger.Topology.SingularCohomologyCup

/-!
# Ordinary singular cohomology acting on the original relative cohomology

Public module ID: M2061.

Hatcher, Algebraic Topology, section 3.2, pp.209--210. The actual
ordinary-relative cochain product descends through the two original
cocycle quotients, giving H^p(X;R) × H^q(X,A;R) → H^(p+q)(X,A;R).
The canonical ModuleCat homology comparisons transport this product to
the already defined singularCohomology and relativeSingularCohomology.

The resulting operation is associative as an action of the ordinary
cohomology ring, has the original constant-one class as left unit, and
is natural for the specified maps of pairs. Forgetting the relative
condition gives precisely the original ordinary cup product.
This is the order used by the Thom map a ↦ π*a cup U.

No relative unit is asserted for a general pair. This construction
requires no geometric assumptions on A and does not assert the more
general product for two different subspaces and their union.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- A relative cocycle's class in the original relative cohomology group. -/
def relativeSingularCocycleClass (A : Set X) (n : ℕ) :
    relativeSingularCocycles R A n →ₗ[R] relativeSingularCohomology R A n :=
  (((relativeSingularCochains R A).sc n).moduleCatHomologyIso.inv.hom).comp
    (relativeSingularCoboundaries R A n).mkQ

/-- Ordinary cohomology acts on the original relative cohomology by the descended cup product. -/
def relativeSingularCohomologyAction (A : Set X) (p q : ℕ) :
    singularCohomology R X p →ₗ[R] relativeSingularCohomology R A q →ₗ[R]
      relativeSingularCohomology R A (p + q) := by
  -- Take the original relative class of the same ordinary-relative cocycle product.
  let product := (relativeSingularCocycleAction R A p q).compr₂
    (relativeSingularCoboundaries R A (p + q)).mkQ
  have hLeft : singularCoboundaries R X p ≤ product.ker := by
    intro a ha
    apply LinearMap.ext
    intro b
    change (relativeSingularCoboundaries R A (p + q)).mkQ
        (relativeSingularCocycleAction R A p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCocycleAction_mem_coboundaries R A p q a b (Or.inl ha))
  have hRight : relativeSingularCoboundaries R A q ≤ product.flip.ker := by
    intro b hb
    apply LinearMap.ext
    intro a
    change (relativeSingularCoboundaries R A (p + q)).mkQ
        (relativeSingularCocycleAction R A p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCocycleAction_mem_coboundaries R A p q a b (Or.inr hb))
  -- Descend by both actual boundary submodules and use their canonical homology comparisons.
  let descended := product.liftQ₂
    (singularCoboundaries R X p) (relativeSingularCoboundaries R A q) hLeft hRight
  let comparison := descended.compr₂
    ((relativeSingularCochains R A).sc (p + q)).moduleCatHomologyIso.inv.hom
  exact (comparison.compl₂ ((relativeSingularCochains R A).sc q).moduleCatHomologyIso.hom.hom).comp
    ((singularCochains R X).sc p).moduleCatHomologyIso.hom.hom

/-- The action is represented by the actual product of the given ordinary and relative cocycles. -/
theorem relativeSingularCohomologyAction_cocycleClass (A : Set X) (p q : ℕ)
    (a : singularCocycles R X p) (b : relativeSingularCocycles R A q) :
    relativeSingularCohomologyAction R A p q
        (singularCocycleClass R X p a) (relativeSingularCocycleClass R A q b) =
      relativeSingularCocycleClass R A (p + q) (relativeSingularCocycleAction R A p q a b) := by
  /- Cancel the original ordinary and relative homology comparison
  isomorphisms. The double quotient lift evaluated on these same
  cocycles is the class of their actual relative product. The target
  homology comparison is exactly the one in relativeSingularCocycleClass. -/
  let product := (relativeSingularCocycleAction R A p q).compr₂
    (relativeSingularCoboundaries R A (p + q)).mkQ
  have hLeft : singularCoboundaries R X p ≤ product.ker := by
    intro a ha
    apply LinearMap.ext
    intro b
    change (relativeSingularCoboundaries R A (p + q)).mkQ
        (relativeSingularCocycleAction R A p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCocycleAction_mem_coboundaries R A p q a b (Or.inl ha))
  have hRight : relativeSingularCoboundaries R A q ≤ product.flip.ker := by
    intro b hb
    apply LinearMap.ext
    intro a
    change (relativeSingularCoboundaries R A (p + q)).mkQ
        (relativeSingularCocycleAction R A p q a b) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCocycleAction_mem_coboundaries R A p q a b (Or.inr hb))
  -- Descend by both actual boundary submodules and use their canonical homology comparisons.
  let descended := product.liftQ₂
    (singularCoboundaries R X p) (relativeSingularCoboundaries R A q) hLeft hRight
  let I := ((singularCochains R X).sc p).moduleCatHomologyIso
  let J := ((relativeSingularCochains R A).sc q).moduleCatHomologyIso
  let K := ((relativeSingularCochains R A).sc (p + q)).moduleCatHomologyIso
  change K.inv (descended (I.hom (I.inv ((singularCoboundaries R X p).mkQ a)))
    (J.hom (J.inv ((relativeSingularCoboundaries R A q).mkQ b)))) =
      K.inv ((relativeSingularCoboundaries R A (p + q)).mkQ
        (relativeSingularCocycleAction R A p q a b))
  have hI : I.hom (I.inv ((singularCoboundaries R X p).mkQ a)) =
      (singularCoboundaries R X p).mkQ a :=
    congrArg (fun f ↦ f ((singularCoboundaries R X p).mkQ a)) I.inv_hom_id
  have hJ : J.hom (J.inv ((relativeSingularCoboundaries R A q).mkQ b)) =
      (relativeSingularCoboundaries R A q).mkQ b := by
    exact congrArg (fun f ↦ f ((relativeSingularCoboundaries R A q).mkQ b)) J.inv_hom_id
  rw [hI, hJ]
  rfl

/-- The ordinary-relative action is associative with the actual ordinary cup product. -/
theorem relativeSingularCohomologyAction_assoc (A : Set X) (p q r : ℕ)
    (a : singularCohomology R X p) (b : singularCohomology R X q)
    (c : relativeSingularCohomology R A r) :
    (eqToIso (by rw [Nat.add_assoc]) :
        relativeSingularCohomology R A ((p + q) + r) ≅
          relativeSingularCohomology R A (p + (q + r))).hom
      (relativeSingularCohomologyAction R A (p + q) r
        (singularCohomologyCup R X p q a b) c) =
    relativeSingularCohomologyAction R A p (q + r) a
      (relativeSingularCohomologyAction R A q r b c) := by
  /- Choose representatives in the original ordinary and relative
  cocycle quotients. Pull the two relative cochain products back along
  the original chain quotient projection. Both evaluate on the same
  three consecutive simplex faces, so associativity of coefficient
  multiplication identifies them. The pullback is injective, hence
  they agree as relative cochains. Passing to the same relative classes
  proves the displayed action law with only reassociation of the degree. -/
  -- The canonical quotient comparison supplies actual cocycle representatives.
  have hrep (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- Equality of degrees transports the same cocycle class, including its kernel witness.
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
  -- Evaluate the original ordinary product directly on its cocycle classes.
  have hordinary (p q : ℕ)
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
  -- Identify all three consecutive faces before using associativity of coefficients.
  have hassoc (p q r : ℕ) (a : (singularCochains R X).X p)
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
  -- Pass from the three same consecutive simplex faces to the original relative classes.
  let C := relativeSingularCochains R A
  let J := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  have haction (i j : ℕ) (a : (singularCochains R X).X i) (b : C.X j) :
      J.f (i + j) (relativeSingularCochainAction R A i j a b) =
        singularCochainCup R X i j a (J.f j b) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A (i + j)).apply_symm_apply _)
  have ht {i j : ℕ} (h : i = j) (a : C.X i) :
      J.f j ((C.XIsoOfEq h).hom a) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f i a) := by
    subst j
    rfl
  obtain ⟨α, hα⟩ := hrep (singularCochains R X) p a
  obtain ⟨β, hβ⟩ := hrep (singularCochains R X) q b
  obtain ⟨γ, hγ⟩ := hrep C r c
  change singularCocycleClass R X p α = a at hα
  change singularCocycleClass R X q β = b at hβ
  change relativeSingularCocycleClass R A r γ = c at hγ
  rw [← hα, ← hβ, ← hγ, hordinary, relativeSingularCohomologyAction_cocycleClass,
    relativeSingularCohomologyAction_cocycleClass, relativeSingularCohomologyAction_cocycleClass]
  apply htransport C ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
  apply (relativeSingularCochainEquiv R A (p + (q + r))).injective
  apply Subtype.ext
  change J.f (p + (q + r)) ((C.XIsoOfEq (Nat.add_assoc p q r)).hom
    (relativeSingularCochainAction R A (p + q) r
      (singularCochainCup R X p q α.val β.val) γ.val)) =
      J.f (p + (q + r)) (relativeSingularCochainAction R A p (q + r) α.val
        (relativeSingularCochainAction R A q r β.val γ.val))
  rw [ht, haction (p + q) r (singularCochainCup R X p q α.val β.val) γ.val,
    haction p (q + r) α.val (relativeSingularCochainAction R A q r β.val γ.val),
    haction q r β.val γ.val]
  exact hassoc p q r α.val β.val (J.f r γ.val)

/-- The original ordinary constant-one class acts as the identity on relative cohomology. -/
theorem relativeSingularCohomologyAction_one (A : Set X) (q : ℕ)
    (b : relativeSingularCohomology R A q) :
    (eqToIso (by rw [Nat.zero_add]) :
        relativeSingularCohomology R A (0 + q) ≅ relativeSingularCohomology R A q).hom
      (relativeSingularCohomologyAction R A 0 q (singularCohomologyOne R X) b) = b := by
  /- The original constant-one zero-cochain evaluates to one at the
  first vertex. Thus its ordinary-relative product has exactly the
  same ordinary pullback as the original relative representative.
  Injectivity of relative pullback identifies these relative cochains,
  and passing to their classes proves the left-unit identity. This
  includes degree zero and empty spaces without a nonempty assumption. -/
  -- The canonical quotient comparison supplies actual cocycle representatives.
  have hrep (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- Equality of degrees transports the same cocycle class, including its kernel witness.
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
  -- The original constant-one cochain leaves the full back face unchanged.
  have hone (q : ℕ) (b : (singularCochains R X).X q) :
      ((singularCochains R X).XIsoOfEq (Nat.zero_add q)).hom
        (singularCochainCup R X 0 q (singularCochainOne R X) b) = b := by
    have htransport {n m : ℕ} (h : n = m) (φ : (singularCochains R X).X n)
        (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋m⦌)) :
        singularCochainEquiv R X m (((singularCochains R X).XIsoOfEq h).hom φ) σ =
          singularCochainEquiv R X n φ
            ((TopCat.toSSet.obj (TopCat.of X)).map
              (eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).op σ) := by
      subst m
      simp [HomologicalComplex.XIsoOfEq]
    apply (singularCochainEquiv R X q).injective
    funext σ
    rw [htransport]
    change singularCochainEquiv R X (0 + q)
      ((singularCochainEquiv R X (0 + q)).symm _) _ = _
    rw [LinearEquiv.apply_symm_apply]
    change singularCochainEquiv R X 0 ((singularCochainEquiv R X 0).symm _) _ * _ = _
    rw [LinearEquiv.apply_symm_apply, one_mul]
    have hface : singularCupBackFace 0 q ≫
        eqToHom (congrArg (fun k ↦ ⦋k⦌) (Nat.zero_add q)) = 𝟙 ⦋q⦌ := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      apply Fin.ext
      simp [singularCupBackFace]
    have hm := congrArg (fun f ↦ (TopCat.toSSet.obj (TopCat.of X)).map f.op σ) hface
    simp only [op_comp, Functor.map_comp, op_id] at hm
    have hi : (TopCat.toSSet.obj (TopCat.of X)).map (𝟙 (op ⦋q⦌)) σ = σ :=
      congrArg (fun f ↦ f σ) ((TopCat.toSSet.obj (TopCat.of X)).map_id (op ⦋q⦌))
    exact congrArg (singularCochainEquiv R X q b) (hm.trans hi)
  -- Choose an actual representative, then verify the unit on its original simplex values.
  obtain ⟨β, hβ⟩ := hrep (relativeSingularCochains R A) q b
  change relativeSingularCocycleClass R A q β = b at hβ
  rw [← hβ]
  simp only [singularCohomologyOne]
  rw [relativeSingularCohomologyAction_cocycleClass]
  apply htransport (relativeSingularCochains R A) (0 + q) q (Nat.zero_add q)
  let J := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  have ht {i j : ℕ} (h : i = j) (a : (relativeSingularCochains R A).X i) :
      J.f j (((relativeSingularCochains R A).XIsoOfEq h).hom a) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f i a) := by
    subst j
    rfl
  apply (relativeSingularCochainEquiv R A q).injective
  apply Subtype.ext
  change J.f q (((relativeSingularCochains R A).XIsoOfEq (Nat.zero_add q)).hom
    (relativeSingularCochainAction R A 0 q (singularCochainOne R X) β.val)) = J.f q β.val
  rw [ht]
  have haction : J.f (0 + q)
      (relativeSingularCochainAction R A 0 q (singularCochainOne R X) β.val) =
        singularCochainCup R X 0 q (singularCochainOne R X) (J.f q β.val) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A (0 + q)).apply_symm_apply _)
  rw [haction]
  exact hone q (J.f q β.val)

/-- Forgetting the relative condition sends the action to the same ordinary cup product. -/
theorem relativeSingularCohomologyToOrdinary_action (A : Set X) (p q : ℕ)
    (a : singularCohomology R X p) (b : relativeSingularCohomology R A q) :
    relativeSingularCohomologyToOrdinary R A (p + q)
        (relativeSingularCohomologyAction R A p q a b) =
      singularCohomologyCup R X p q a (relativeSingularCohomologyToOrdinary R A q b) := by
  /- The map to ordinary cohomology is induced by dualizing the same
  original chain quotient projection. The cokernel extension used in
  relativeSingularCochainEquiv has precisely the prescribed ordinary
  cup product as its composite with that projection. Therefore the
  cochain equality uses the actual comparison map, not an arbitrary
  identification. Naturality of the homology quotient comparisons
  passes this equality to the displayed original cohomology groups. -/
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
  -- Evaluate the original ordinary product directly on its cocycle classes.
  have hordinary (p q : ℕ)
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
  -- Representatives and both comparison maps belong to the original quotient complexes.
  let C := relativeSingularCochains R A
  let O := singularCochains R X
  let J := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  obtain ⟨α, hα⟩ := hrep O p a
  obtain ⟨β, hβ⟩ := hrep C q b
  change singularCocycleClass R X p α = a at hα
  change relativeSingularCocycleClass R A q β = b at hβ
  obtain ⟨β', hβ'⟩ := hcycles C O J q β
  have hb := hclass C O J q β β' hβ'.symm
  change relativeSingularCohomologyToOrdinary R A q
    (relativeSingularCocycleClass R A q β) = singularCocycleClass R X q β' at hb
  rw [← hα, ← hβ, relativeSingularCohomologyAction_cocycleClass, hb, hordinary]
  apply hclass C O J (p + q)
  change J.f (p + q) (relativeSingularCochainAction R A p q α.val β.val) =
    singularCochainCup R X p q α.val β'.val
  rw [hβ']
  exact congrArg Subtype.val ((relativeSingularCochainEquiv R A (p + q)).apply_symm_apply _)

/-- The action is natural for the specified continuous map of pairs. -/
theorem relativeSingularCohomologyPullback_action {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (p q : ℕ)
    (a : singularCohomology R Y p) (b : relativeSingularCohomology R B q) :
    relativeSingularCohomologyPullback R f hf (p + q)
        (relativeSingularCohomologyAction R B p q a b) =
      relativeSingularCohomologyAction R A p q
        (singularCohomologyPullback R f p a) (relativeSingularCohomologyPullback R f hf q b) := by
  /- Hatcher Proposition 3.10 applies to the same map of pairs.
  Restricting an original simplex to its front/back faces commutes
  with composition with f. The relative chain map is induced from
  this same f by the actual cokernel square, so the two relative
  cochain products have identical pullbacks along the source quotient
  projection. Its injectivity gives equality as relative cochains.
  Pass to the original quotient classes using naturality of the
  canonical homology comparisons. Only MapsTo f A B is required. -/
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
  let C := relativeSingularCochains R B
  let D := relativeSingularCochains R A
  let F := (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op
  let JX := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JY := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  have hchain : relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
      (singularChainsFunctor R).map (TopCat.ofHom f) ≫ relativeSingularChainsProjection R B := by
    simp [relativeSingularChainsProjection, relativeSingularChainsMap]
  have hprojection : F ≫ JX = JY ≫ P := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ =
      (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf).op =
        (singularCochainDualFunctor R).map
          ((singularChainsFunctor R).map (TopCat.ofHom f) ≫
            relativeSingularChainsProjection R B).op
    rw [hchain]
  have haction {Z : Type u} [TopologicalSpace Z] (T : Set Z) (i j : ℕ)
      (a : (singularCochains R Z).X i) (b : (relativeSingularCochains R T).X j) :
      ((singularCochainDualFunctor R).map (relativeSingularChainsProjection R T).op).f
        (i + j) (relativeSingularCochainAction R T i j a b) =
          singularCochainCup R Z i j a
            (((singularCochainDualFunctor R).map
              (relativeSingularChainsProjection R T).op).f j b) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R T (i + j)).apply_symm_apply _)
  -- Choose representatives and apply homology to these same cochain maps.
  obtain ⟨α, hα⟩ := hrep (singularCochains R Y) p a
  obtain ⟨β, hβ⟩ := hrep C q b
  change singularCocycleClass R Y p α = a at hα
  change relativeSingularCocycleClass R B q β = b at hβ
  obtain ⟨α', hα'⟩ := hcycles (singularCochains R Y) (singularCochains R X) P p α
  obtain ⟨β', hβ'⟩ := hcycles C D F q β
  have ha := hclass (singularCochains R Y) (singularCochains R X) P p α α' hα'.symm
  have hb := hclass C D F q β β' hβ'.symm
  change singularCohomologyPullback R f p (singularCocycleClass R Y p α) =
    singularCocycleClass R X p α' at ha
  change relativeSingularCohomologyPullback R f hf q (relativeSingularCocycleClass R B q β) =
    relativeSingularCocycleClass R A q β' at hb
  rw [← hα, ← hβ, relativeSingularCohomologyAction_cocycleClass, ha, hb,
    relativeSingularCohomologyAction_cocycleClass]
  apply hclass C D F (p + q)
  apply (relativeSingularCochainEquiv R A (p + q)).injective
  apply Subtype.ext
  change JX.f (p + q) (F.f (p + q)
    (relativeSingularCochainAction R B p q α.val β.val)) =
      JX.f (p + q) (relativeSingularCochainAction R A p q α'.val β'.val)
  have hcomp (n : ℕ) (v : C.X n) : JX.f n (F.f n v) = P.f n (JY.f n v) :=
    congrArg (fun t ↦ t.f n v) hprojection
  rw [hcomp, haction B p q α.val β.val, haction A p q α'.val β'.val,
    hcup p q α.val (JY.f q β.val), hα', hβ', hcomp q β.val]

end AtiyahSinger
