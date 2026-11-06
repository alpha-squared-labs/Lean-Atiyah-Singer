/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCochainReversal
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The cup product on the original singular cohomology

Public module ID: M2128.

D11: Hatcher section 3.2. The original front-face/back-face cochain
product descends through the actual cocycle quotient. The comparison
with mathlib's categorical homology is the canonical module homology
isomorphism, so this operation acts on the already defined H^n(X;R).

The construction uses the original bilinear cochain product and the
coboundary ideal property. It does not select an unspecified product
with ring laws as input. Degree changes in the graded identities use
only the canonical equality isomorphisms. The graded-commutativity
sign is retained for all degrees and all commutative coefficient rings.

This supplies ordinary cup products. Relative/compact-support products,
coefficient-change maps, characteristic classes and the locally finite
fundamental-class pairing remain separate parts of D11. The representative formula,
associativity, graded commutativity, both unit laws and both pullback laws are proved below.
Commutativity uses the geometric signed-reversal homotopy on the original chains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The original cohomology class of a cocycle, via the canonical module homology comparison. -/
def singularCocycleClass (n : ℕ) :
    singularCocycles R X n →ₗ[R] singularCohomology R X n :=
  (((singularCochains R X).sc n).moduleCatHomologyIso.inv.hom).comp
    (singularCoboundaries R X n).mkQ

/-- The actual Alexander-Whitney cup product descended to the original singular cohomology. -/
def singularCohomologyCup (p q : ℕ) :
    singularCohomology R X p →ₗ[R] singularCohomology R X q →ₗ[R]
      singularCohomology R X (p + q) := by
  -- First form the class of the original product of the two cocycles.
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
  -- Descend on both sides, then use the canonical comparisons with the original H groups.
  let descended := product.liftQ₂
    (singularCoboundaries R X p) (singularCoboundaries R X q) hLeft hRight
  let comparison := descended.compr₂
    ((singularCochains R X).sc (p + q)).moduleCatHomologyIso.inv.hom
  exact (comparison.compl₂ ((singularCochains R X).sc q).moduleCatHomologyIso.hom.hom).comp
    ((singularCochains R X).sc p).moduleCatHomologyIso.hom.hom

/-- The unit class is the class of the original constant-one degree-zero singular cocycle. -/
def singularCohomologyOne : singularCohomology R X 0 :=
  singularCocycleClass R X 0 (singularCocycleOne R X)

/-- The induced product is represented by the original cup product of the given cocycles. -/
theorem singularCohomologyCup_cocycleClass (p q : ℕ)
    (a : singularCocycles R X p) (b : singularCocycles R X q) :
    singularCohomologyCup R X p q (singularCocycleClass R X p a)
        (singularCocycleClass R X q b) =
      singularCocycleClass R X (p + q) (singularCocycleCup R X p q a b) := by
  /- Cancel the two canonical homology comparison isomorphisms. The
  double quotient lift evaluates on the displayed cocycle classes as
  the class of their original product. The comparison in the target
  is precisely the one defining singularCocycleClass. -/
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

/-- Cup product is associative, with the canonical reassociation of its total degree. -/
theorem singularCohomologyCup_assoc (p q r : ℕ)
    (a : singularCohomology R X p) (b : singularCohomology R X q)
    (c : singularCohomology R X r) :
    (eqToIso (by rw [Nat.add_assoc]) :
        singularCohomology R X ((p + q) + r) ≅ singularCohomology R X (p + (q + r))).hom
      (singularCohomologyCup R X (p + q) r (singularCohomologyCup R X p q a b) c) =
    singularCohomologyCup R X p (q + r) a (singularCohomologyCup R X q r b c) := by
  /- Choose cocycle representatives using the actual quotient map.
  Both iterated cochain products evaluate on a simplex as the product
  of its same three consecutive faces, sharing the two division vertices.
  Coefficient multiplication is associative, so these cochains agree
  after the canonical degree identification. Pass to their original
  cohomology classes; no sign appears in reassociating the product. -/
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
  -- Descend the equality of the same three faces through the original cocycle quotients.
  obtain ⟨α, hα⟩ := hrep (singularCochains R X) p a
  obtain ⟨β, hβ⟩ := hrep (singularCochains R X) q b
  obtain ⟨γ, hγ⟩ := hrep (singularCochains R X) r c
  change singularCocycleClass R X p α = a at hα
  change singularCocycleClass R X q β = b at hβ
  change singularCocycleClass R X r γ = c at hγ
  rw [← hα, ← hβ, ← hγ, singularCohomologyCup_cocycleClass,
    singularCohomologyCup_cocycleClass, singularCohomologyCup_cocycleClass,
    singularCohomologyCup_cocycleClass]
  apply htransport (singularCochains R X) ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
  exact hassoc p q r α.val β.val γ.val

/-- Singular cohomology is graded commutative, with the sign determined by both degrees. -/
theorem singularCohomologyCup_comm (p q : ℕ)
    (a : singularCohomology R X p) (b : singularCohomology R X q) :
    (eqToIso (by rw [Nat.add_comm p q]) :
        singularCohomology R X (p + q) ≅ singularCohomology R X (q + p)).hom
      (singularCohomologyCup R X p q a b) =
    (-1 : R) ^ (p * q) • singularCohomologyCup R X q p b a := by
  /- Stage 1: follow Hatcher Theorem 3.11. Reverse the vertices of
  each original n-simplex and multiply by (-1)^(n*(n+1)/2). The
  simplex cone construction in singularReversalHomotopy joins this
  signed reversal to the identity. Its dual therefore acts identically
  on cohomology.
  Stage 2: reversal interchanges the original front and back faces.
  The reversal signs in degrees p, q and p+q differ by (-1)^(p*q).
  Coefficient commutativity therefore identifies the reversed products
  with precisely the displayed sign. Pass to the original cocycle
  classes and use the canonical degree transport for the equality.
  Cochains themselves need not commute; commutativity is asserted only
  after passing to cohomology. -/
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
  -- Signed reversal preserves each representative's class through its geometric homotopy.
  let C := singularCochains R X
  let F := singularCochainReversal R X
  have hrev (n : ℕ) (γ δ : singularCocycles R X n)
      (hδ : δ.val = F.f n γ.val) :
      singularCocycleClass R X n δ = singularCocycleClass R X n γ := by
    have h := hclass C C F n γ δ hδ.symm
    change HomologicalComplex.homologyMap (singularCochainReversal R X) n
      (singularCocycleClass R X n γ) = singularCocycleClass R X n δ at h
    rw [homologyMap_singularCochainReversal] at h
    exact h.symm
  obtain ⟨α, hα⟩ := hrep C p a
  obtain ⟨β, hβ⟩ := hrep C q b
  change singularCocycleClass R X p α = a at hα
  change singularCocycleClass R X q β = b at hβ
  obtain ⟨α', hα'⟩ := hcycles C C F p α
  obtain ⟨β', hβ'⟩ := hcycles C C F q β
  let γ := singularCocycleCup R X p q α β
  obtain ⟨γ', hγ'⟩ := hcycles C C F (p + q) γ
  rw [← hα, ← hβ, singularCohomologyCup_cocycleClass]
  -- Exchange the two original faces before passing through the same cocycle quotient.
  change (eqToIso (congrArg (fun n ↦ C.homology n) (Nat.add_comm p q))).hom
    (singularCocycleClass R X (p + q) γ) = _
  rw [← hrev (p + q) γ γ' hγ']
  have hcochain : (C.XIsoOfEq (Nat.add_comm p q)).hom γ'.val =
      ((-1 : R) ^ (p * q) • singularCocycleCup R X q p β' α').val := by
    rw [hγ']
    change ((singularCochains R X).XIsoOfEq (Nat.add_comm p q)).hom
      ((singularCochainReversal R X).f (p + q)
        (singularCochainCup R X p q α.val β.val)) =
        (-1 : R) ^ (p * q) • singularCochainCup R X q p β'.val α'.val
    rw [hα', hβ']
    exact singularCochainReversal_cup R X p q α.val β.val
  have ht := htransport C (p + q) (q + p) (Nat.add_comm p q) γ'
    ((-1 : R) ^ (p * q) • singularCocycleCup R X q p β' α') hcochain
  change _ = singularCocycleClass R X (q + p)
    ((-1 : R) ^ (p * q) • singularCocycleCup R X q p β' α') at ht
  refine ht.trans ?_
  rw [map_smul, ← singularCohomologyCup_cocycleClass,
    hrev q β β' hβ', hrev p α α' hα']

/-- The constant-one class is a left unit, including the degree-zero identification. -/
theorem singularCohomologyOne_cup (p : ℕ) (a : singularCohomology R X p) :
    (eqToIso (by rw [Nat.zero_add]) :
        singularCohomology R X (0 + p) ≅ singularCohomology R X p).hom
      (singularCohomologyCup R X 0 p (singularCohomologyOne R X) a) = a := by
  /- On each simplex the first factor evaluates to one at its initial
  vertex; the remaining face is the same whole simplex. This is the
  original cochain representative of a. Descend through the quotient
  and use the identity degree comparison. -/
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
  -- Apply the unit identity to an actual representative of the original class.
  obtain ⟨α, hα⟩ := hrep (singularCochains R X) p a
  change singularCocycleClass R X p α = a at hα
  rw [← hα, singularCohomologyOne, singularCohomologyCup_cocycleClass]
  apply htransport (singularCochains R X) (0 + p) p (Nat.zero_add p)
  exact hone p α.val

/-- The constant-one class is a right unit for the original cohomological product. -/
theorem singularCohomologyCup_one (p : ℕ) (a : singularCohomology R X p) :
    singularCohomologyCup R X p 0 a (singularCohomologyOne R X) = a := by
  /- The last factor is the constant-one cocycle evaluated at the
  terminal vertex, so multiplication preserves the original cochain.
  Descend to its class; p+0 is definitionally the same degree as p. -/
  -- The canonical quotient comparison supplies actual cocycle representatives.
  have hrep (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- The original front face in bidegree (p, 0) is the entire simplex.
  have hone (b : (singularCochains R X).X p) :
      singularCochainCup R X p 0 b (singularCochainOne R X) = b := by
    apply (singularCochainEquiv R X p).injective
    funext σ
    change singularCochainEquiv R X p ((singularCochainEquiv R X p).symm _) σ = _
    rw [LinearEquiv.apply_symm_apply]
    change _ * singularCochainEquiv R X 0 ((singularCochainEquiv R X 0).symm _) _ = _
    rw [LinearEquiv.apply_symm_apply, mul_one]
    have hface : singularCupFrontFace p 0 = 𝟙 ⦋p⦌ := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      apply Fin.ext
      rfl
    rw [hface, op_id]
    exact congrArg (singularCochainEquiv R X p b)
      (congrArg (fun t ↦ t σ) ((TopCat.toSSet.obj (TopCat.of X)).map_id (op ⦋p⦌)))
  -- The canonical quotient preserves this equality of the original cocycles.
  obtain ⟨α, hα⟩ := hrep (singularCochains R X) p a
  change singularCocycleClass R X p α = a at hα
  rw [← hα, singularCohomologyOne, singularCohomologyCup_cocycleClass]
  apply congrArg (singularCocycleClass R X p)
  apply Subtype.ext
  exact hone α.val

variable {X}

/-- Pullback along the specified continuous map preserves the original cup product. -/
theorem singularCohomologyPullback_cup {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (p q : ℕ)
    (a : singularCohomology R Y p) (b : singularCohomology R Y q) :
    singularCohomologyPullback R f (p + q) (singularCohomologyCup R Y p q a b) =
      singularCohomologyCup R X p q
        (singularCohomologyPullback R f p a) (singularCohomologyPullback R f q b) := by
  /- Restricting a simplex to each front/back face commutes with the
  specified map f. Hence the original cochain pullback preserves the
  displayed product. Naturality of the canonical homology comparison
  passes this equality to the same original cohomology pullbacks. -/
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
  -- Choose the original representatives and their images under this same pullback.
  obtain ⟨α, hα⟩ := hrep (singularCochains R Y) p a
  obtain ⟨β, hβ⟩ := hrep (singularCochains R Y) q b
  change singularCocycleClass R Y p α = a at hα
  change singularCocycleClass R Y q β = b at hβ
  obtain ⟨α', hα'⟩ := hcycles (singularCochains R Y) (singularCochains R X) P p α
  obtain ⟨β', hβ'⟩ := hcycles (singularCochains R Y) (singularCochains R X) P q β
  have ha := hclass (singularCochains R Y) (singularCochains R X) P p α α' hα'.symm
  have hb := hclass (singularCochains R Y) (singularCochains R X) P q β β' hβ'.symm
  change singularCohomologyPullback R f p (singularCocycleClass R Y p α) =
    singularCocycleClass R X p α' at ha
  change singularCohomologyPullback R f q (singularCocycleClass R Y q β) =
    singularCocycleClass R X q β' at hb
  rw [← hα, ← hβ, singularCohomologyCup_cocycleClass, ha, hb,
    singularCohomologyCup_cocycleClass]
  apply hclass (singularCochains R Y) (singularCochains R X) P (p + q)
  change P.f (p + q) (singularCochainCup R Y p q α.val β.val) =
    singularCochainCup R X p q α'.val β'.val
  exact (hcup p q α.val β.val).trans
    (congrArg₂ (fun x y ↦ singularCochainCup R X p q x y) hα'.symm hβ'.symm)

/-- Pullback preserves the original constant-one cohomology class. -/
theorem singularCohomologyPullback_one {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) :
    singularCohomologyPullback R f 0 (singularCohomologyOne R Y) =
      singularCohomologyOne R X := by
  /- Pulling back the constant-one zero-cochain along the same f
  still evaluates to one on every vertex. Its original cocycle class
  is the unit constructed above, without requiring X or Y nonempty. -/
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
  -- Pullback of the actual constant-one cochain evaluates to one at every source vertex.
  let P := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  apply hclass (singularCochains R Y) (singularCochains R X) P 0
  change P.f 0 (singularCochainOne R Y) = singularCochainOne R X
  apply (singularCochainEquiv R X 0).injective
  funext σ
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  have heval (χ : (singularCochains R Y).X 0) :
      singularCochainEquiv R X 0 (P.f 0 χ) σ =
        singularCochainEquiv R Y 0 χ (g.app (op ⦋0⦌) σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex
      (singularCoefficient R)).X 0 ⟶ singularCoefficient R from χ)
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
        (SSet.chainComplexMap g (singularCoefficient R)).f 0) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  rw [heval]
  simp only [singularCochainOne, LinearEquiv.apply_symm_apply]

end AtiyahSinger
