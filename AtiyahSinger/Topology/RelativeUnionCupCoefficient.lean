/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyGradedCommutativity
public import AtiyahSinger.Topology.SimplexLocalHomology
public import AtiyahSinger.Topology.SupportedThomAction

/-!
# Ordinary coefficients in a relative cup product

Public module ID: M2101.

Moving an ordinary coefficient past a relative factor is justified on the
original cochain quotient, using the geometric reversal homotopy. The
forgetful map to ordinary cohomology need not be injective. This is needed
to compare products of two specified Thom representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Any actual right cup cocycle represents the signed ordinary left action. -/
theorem relativeSingularCocycleClass_cup_right (A : Set X) (p q : ℕ)
    (α : relativeSingularCocycles R A p) (β : singularCocycles R X q)
    (γ : relativeSingularCocycles R A (p + q))
    (hγ : (relativeSingularCochainEquiv R A (p + q) γ.val).val =
      singularCochainCup R X p q (relativeSingularCochainEquiv R A p α.val).val β.val) :
    (eqToIso (congrArg (relativeSingularCohomology R A) (Nat.add_comm p q))).hom
      (relativeSingularCocycleClass R A (p + q) γ) =
    (-1 : R) ^ (p * q) • relativeSingularCohomologyAction R A q p
      (singularCocycleClass R X q β) (relativeSingularCocycleClass R A p α) := by
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
  let C := relativeSingularCochains R A
  let D := singularCochains R X
  let F : C ⟶ C := (singularCochainDualFunctor R).map (relativeSingularReversal R A).op
  let G := singularCochainReversal R X
  let J : C ⟶ D :=
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  have hhom (n : ℕ) : HomologicalComplex.homologyMap F n = 𝟙 _ := by
    let dual := ((linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)).rightOp
    have H := (dual.mapHomotopy (relativeSingularReversalHomotopy R A)).unop
    change Homotopy ((singularCochainDualFunctor R).map (𝟙 (relativeSingularChains R A)).op)
      F at H
    have h := H.homologyMap_eq n
    rw [show (𝟙 (relativeSingularChains R A)).op =
      𝟙 (op (relativeSingularChains R A)) from rfl,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at h
    exact h.symm
  have hrev (n : ℕ) (γ δ : relativeSingularCocycles R A n)
      (hδ : δ.val = F.f n γ.val) :
      relativeSingularCocycleClass R A n δ = relativeSingularCocycleClass R A n γ := by
    have h := homologyMap_cycleClass R C C F n γ δ hδ.symm
    change HomologicalComplex.homologyMap F n (relativeSingularCocycleClass R A n γ) =
      relativeSingularCocycleClass R A n δ at h
    rw [hhom] at h
    exact h.symm
  have hprojection : F ≫ J = J ≫ G := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ =
      (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R A ≫ relativeSingularReversal R A).op =
      (singularCochainDualFunctor R).map
        (singularReversal R X ≫ relativeSingularChainsProjection R A).op
    rw [relativeSingularChainsProjection_reversal]
  have hcomp (n : ℕ) (v : C.X n) : J.f n (F.f n v) = G.f n (J.f n v) :=
    congrArg (fun f ↦ f.f n v) hprojection
  have haction (i j : ℕ) (α : D.X i) (β : C.X j) :
      J.f (i + j) (relativeSingularCochainAction R A i j α β) =
        singularCochainCup R X i j α (J.f j β) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A (i + j)).apply_symm_apply _)
  have hdegree {i j : ℕ} (h : i = j) (α : C.X i) :
      J.f j ((C.XIsoOfEq h).hom α) = (D.XIsoOfEq h).hom (J.f i α) := by
    subst j
    rfl
  -- Reverse the actual right product before passing to its relative cohomology class.
  have hcomm : (C.XIsoOfEq (Nat.add_comm p q)).hom (F.f (p + q) γ.val) =
      (-1 : R) ^ (p * q) • relativeSingularCochainAction R A q p
        (G.f q β.val) (F.f p α.val) := by
    apply (relativeSingularCochainEquiv R A (q + p)).injective
    apply Subtype.ext
    change J.f (q + p) _ = J.f (q + p) _
    rw [hdegree, hcomp]
    change (D.XIsoOfEq (Nat.add_comm p q)).hom
      (G.f (p + q) ((relativeSingularCochainEquiv R A (p + q) γ.val).val)) = _
    rw [hγ, map_smul, haction, hcomp]
    exact singularCochainReversal_cup R X p q (J.f p α.val) β.val
  obtain ⟨α', hα'⟩ := hcycles C C F p α
  obtain ⟨β', hβ'⟩ := hcycles D D G q β
  obtain ⟨γ', hγ'⟩ := hcycles C C F (p + q) γ
  have hβclass : singularCocycleClass R X q β' = singularCocycleClass R X q β := by
    have h := homologyMap_cycleClass R D D G q β β' hβ'.symm
    change HomologicalComplex.homologyMap G q (singularCocycleClass R X q β) =
      singularCocycleClass R X q β' at h
    rw [homologyMap_singularCochainReversal] at h
    exact h.symm
  have hcochain : (C.XIsoOfEq (Nat.add_comm p q)).hom γ'.val =
      ((-1 : R) ^ (p * q) • relativeSingularCocycleAction R A q p β' α').val := by
    rw [hγ']
    change (C.XIsoOfEq (Nat.add_comm p q)).hom (F.f (p + q) γ.val) =
      (-1 : R) ^ (p * q) • relativeSingularCochainAction R A q p β'.val α'.val
    rw [hβ', hα']
    exact hcomm
  -- Reversal is the identity on these original relative and ordinary cohomology objects.
  rw [← hrev (p + q) γ γ' hγ']
  have h := htransport C (p + q) (q + p) (Nat.add_comm p q) γ'
    ((-1 : R) ^ (p * q) • relativeSingularCocycleAction R A q p β' α') hcochain
  change (eqToIso (congrArg (relativeSingularCohomology R A) (Nat.add_comm p q))).hom
    (relativeSingularCocycleClass R A (p + q) γ') =
      relativeSingularCocycleClass R A (q + p)
        ((-1 : R) ^ (p * q) • relativeSingularCocycleAction R A q p β' α') at h
  rw [h, map_smul, ← relativeSingularCohomologyAction_cocycleClass,
    hβclass, hrev p α α' hα']

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original right Alexander--Whitney product has a relative cocycle with its signed class. -/
theorem exists_relativeSingularCocycle_cup_right (A : Set X) (p q : ℕ)
    (α : relativeSingularCocycles R A p) (β : singularCocycles R X q) :
    ∃ γ : relativeSingularCocycles R A (p + q),
      (relativeSingularCochainEquiv R A (p + q) γ.val).val =
        singularCochainCup R X p q (relativeSingularCochainEquiv R A p α.val).val β.val ∧
      (eqToIso (congrArg (relativeSingularCohomology R A) (Nat.add_comm p q))).hom
        (relativeSingularCocycleClass R A (p + q) γ) =
      (-1 : R) ^ (p * q) • relativeSingularCohomologyAction R A q p
        (singularCocycleClass R X q β) (relativeSingularCocycleClass R A p α) := by
  let C := relativeSingularCochains R A
  let D := singularCochains R X
  let J : C ⟶ D :=
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let w := singularCochainCup R X p q (J.f p α.val) β.val
  -- On an A-simplex the front face stays in A, so the original first factor vanishes.
  have hvanish : ((singularCochainDualFunctor R).map (singularSubspaceChains R A).op).f
      (p + q) w = 0 := by
    let f := TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
    let P := (singularCochainDualFunctor R).map (singularSubspaceChains R A).op
    have heval (k : ℕ) (χ : (singularCochains R X).X k)
        (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋k⦌)) :
        singularCochainEquiv R A k (P.f k χ) σ =
          singularCochainEquiv R X k χ (f.app (op ⦋k⦌) σ) := by
      change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
        (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
          (SSet.chainComplexMap f (singularCoefficient R)).f k) (ULift.up 1)) = _
      rw [SSet.ι_chainComplexMap_f]
      rfl
    apply (singularCochainEquiv R A (p + q)).injective
    funext σ
    rw [heval]
    change singularCochainEquiv R X (p + q)
      ((singularCochainEquiv R X (p + q)).symm _) _ = _
    rw [LinearEquiv.apply_symm_apply]
    dsimp only
    have hzero := congrArg
      (fun χ : (singularCochains R A).X p ↦ singularCochainEquiv R A p χ
        ((TopCat.toSSet.obj (TopCat.of A)).map (singularCupFrontFace p q).op σ))
      (relativeSingularCochainEquiv R A p α.val).property
    rw [heval] at hzero
    have hface := congrArg (fun g ↦ g σ) (f.naturality (singularCupFrontFace p q).op)
    change f.app (op ⦋p⦌) ((TopCat.toSSet.obj (TopCat.of A)).map
      (singularCupFrontFace p q).op σ) =
        (TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op
          (f.app (op ⦋p + q⦌) σ) at hface
    erw [← hface, hzero]
    erw [map_zero, map_zero]
    simp
  let v := (relativeSingularCochainEquiv R A (p + q)).symm ⟨w, hvanish⟩
  have hv : J.f (p + q) v = w :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A (p + q)).apply_symm_apply _)
  have hinj (n : ℕ) : Function.Injective (J.f n) := by
    intro a b h
    apply (relativeSingularCochainEquiv R A n).injective
    exact Subtype.ext h
  -- The ordinary cup is closed, and injectivity of cochains detects its relative differential.
  let α₀ : singularCocycles R X p := ⟨J.f p α.val, by
    change D.dFrom p (J.f p α.val) = 0
    rw [J.comm_from_apply]
    change J.next p (C.dFrom p α.val) = 0
    rw [show C.dFrom p α.val = 0 from α.property, map_zero]⟩
  have hclosed (T : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
      (a : (T.sc n).moduleCatLeftHomologyData.K) : T.d n (n + 1) a.val = 0 := by
    have h : T.dFrom n a.val = 0 := a.property
    have h' := congrArg (T.xNextIso (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hd : C.d (p + q) (p + q + 1) v = 0 := by
    apply hinj (p + q + 1)
    rw [map_zero]
    have hcomm := congrArg (fun f ↦ f v) (J.comm (p + q) (p + q + 1)).symm
    change J.f (p + q + 1) (C.d (p + q) (p + q + 1) v) =
      D.d (p + q) (p + q + 1) (J.f (p + q) v) at hcomm
    rw [hcomm, hv]
    exact hclosed D (p + q) (singularCocycleCup R X p q α₀ β)
  let γ : relativeSingularCocycles R A (p + q) := ⟨v, by
    change C.dFrom (p + q) v = 0
    rw [HomologicalComplex.dFrom_eq
      (r := show (ComplexShape.up ℕ).Rel (p + q) (p + q + 1) from rfl),
      ModuleCat.comp_apply, hd, map_zero]⟩
  exact ⟨γ, hv, relativeSingularCocycleClass_cup_right R A p q α β γ hv⟩

set_option maxHeartbeats 600000 in
-- The original joint quotient compares the two products before taking cohomology.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An ordinary coefficient moves across the first relative factor with the graded sign. -/
theorem relativeSingularCohomologyUnionCup_action_right
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q r : ℕ)
    (a : relativeSingularCohomology R A p) (b : singularCohomology R X q)
    (c : relativeSingularCohomology R B r) :
    cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R (A ∪ B) n))
      (show p + (q + r) = q + (p + r) by omega))
      (relativeSingularCohomologyUnionCup R A B hA hB p (q + r) a
        (relativeSingularCohomologyAction R B q r b c)) =
    (-1 : R) ^ (p * q) • relativeSingularCohomologyAction R (A ∪ B) q (p + r) b
      (relativeSingularCohomologyUnionCup R A B hA hB p r a c) := by
  let CA : CochainComplex (ModuleCat.{u} R) ℕ := relativeSingularCochains R A
  let CB : CochainComplex (ModuleCat.{u} R) ℕ := relativeSingularCochains R B
  let D : CochainComplex (ModuleCat.{u} R) ℕ := singularCochains R X
  let C : CochainComplex (ModuleCat.{u} R) ℕ := relativeUnionSingularCochains R A B
  let JA : CA ⟶ D :=
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB : CB ⟶ D :=
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  let J : C ⟶ D :=
    (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A B).op
  have hrep (T : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (z : T.homology n) :
      ∃ a : (T.sc n).moduleCatLeftHomologyData.K,
        (T.sc n).moduleCatHomologyIso.inv ((T.sc n).moduleCatToCycles.range.mkQ a) = z := by
    obtain ⟨a, ha⟩ := (T.sc n).moduleCatToCycles.range.mkQ_surjective
      ((T.sc n).moduleCatHomologyIso.hom z)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f z) (T.sc n).moduleCatHomologyIso.hom_inv_id
  have htransport (T : CochainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ) (h : i = j)
      (a : (T.sc i).moduleCatLeftHomologyData.K)
      (b : (T.sc j).moduleCatLeftHomologyData.K)
      (hab : (T.XIsoOfEq h).hom a.val = b.val) :
      cast (congrArg (fun n ↦ ↥(T.homology n)) h)
        ((T.sc i).moduleCatHomologyIso.inv ((T.sc i).moduleCatToCycles.range.mkQ a)) =
      (T.sc j).moduleCatHomologyIso.inv ((T.sc j).moduleCatToCycles.range.mkQ b) := by
    subst j
    change a.val = b.val at hab
    have heq : a = b := Subtype.ext hab
    subst b
    rfl
  have hcup (i j : ℕ) (α : CA.X i) (β : CB.X j) :
      J.f (i + j) (relativeUnionSingularCochainCup R A B i j α β) =
        singularCochainCup R X i j (JA.f i α) (JB.f j β) :=
    congrArg Subtype.val ((relativeUnionSingularCochainEquiv R A B (i + j)).apply_symm_apply _)
  have haction (i j : ℕ) (α : D.X i) (β : CB.X j) :
      JB.f (i + j) (relativeSingularCochainAction R B i j α β) =
        singularCochainCup R X i j α (JB.f j β) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R B (i + j)).apply_symm_apply _)
  have hdegree {i j : ℕ} (h : i = j) (α : C.X i) :
      J.f j ((C.XIsoOfEq h).hom α) = (D.XIsoOfEq h).hom (J.f i α) := by
    subst j
    rfl
  obtain ⟨α, hα⟩ := hrep CA p a
  obtain ⟨β, hβ⟩ := hrep D q b
  obtain ⟨γ, hγ⟩ := hrep CB r c
  -- Record the same chosen cocycle classes in their original cohomology objects.
  have hαClass : relativeSingularCocycleClass R A p α = a := hα
  have hβClass : singularCocycleClass R X q β = b := hβ
  have hγClass : relativeSingularCocycleClass R B r γ = c := hγ
  obtain ⟨δ, hδ, hδclass⟩ := exists_relativeSingularCocycle_cup_right R A p q α β
  change JA.f (p + q) δ.val = singularCochainCup R X p q (JA.f p α.val) β.val at hδ
  let η : relativeUnionSingularCocycles R A B ((p + q) + r) :=
    relativeUnionSingularCocycleCup R A B (p + q) r δ γ
  let θ : relativeUnionSingularCocycles R A B (p + (q + r)) :=
    relativeUnionSingularCocycleCup R A B p (q + r) α
      (relativeSingularCocycleAction R B q r β γ)
  -- Associativity holds already on the common joint quotient of the original chains.
  have hcochain : (C.XIsoOfEq (Nat.add_assoc p q r)).hom η.val = θ.val := by
    apply (relativeUnionSingularCochainEquiv R A B (p + (q + r))).injective
    apply Subtype.ext
    change J.f (p + (q + r)) _ = J.f (p + (q + r)) _
    rw [hdegree]
    change (D.XIsoOfEq (Nat.add_assoc p q r)).hom
      (J.f ((p + q) + r) (relativeUnionSingularCochainCup R A B (p + q) r δ.val γ.val)) =
      J.f (p + (q + r)) (relativeUnionSingularCochainCup R A B p (q + r) α.val
        (relativeSingularCochainAction R B q r β.val γ.val))
    rw [hcup, hcup, hδ, haction]
    exact singularCochainCup_assoc R p q r (JA.f p α.val) β.val (JB.f r γ.val)
  have hcomparison (i j : ℕ) (h : i = j)
      (z : relativeSingularCohomology R (A ∪ B) i) :
      relativeUnionCohomologyComparison R A B j
        (cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R (A ∪ B) n)) h) z) =
      cast (congrArg (fun n ↦ ↥(C.homology n)) h)
        (relativeUnionCohomologyComparison R A B i z) := by
    subst j
    rfl
  have hassoc :
      cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R (A ∪ B) n))
        (Nat.add_assoc p q r))
        (relativeSingularCohomologyUnionCup R A B hA hB (p + q) r
          (relativeSingularCocycleClass R A (p + q) δ) c) =
      relativeSingularCohomologyUnionCup R A B hA hB p (q + r) a
        (relativeSingularCohomologyAction R B q r b c) := by
    apply (relativeUnionCohomologyEquiv R A B hA hB (p + (q + r))).injective
    change relativeUnionCohomologyComparison R A B (p + (q + r)) _ =
      relativeUnionCohomologyComparison R A B (p + (q + r)) _
    rw [hcomparison _ _ (Nat.add_assoc p q r), ← hαClass, ← hβClass, ← hγClass,
      relativeSingularCohomologyAction_cocycleClass,
      relativeSingularCohomologyUnionCup_cocycleClass,
      relativeSingularCohomologyUnionCup_cocycleClass]
    exact htransport C ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r) η θ hcochain
  have hcupCast (i j : ℕ) (h : i = j) (z : relativeSingularCohomology R A i) :
      cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R (A ∪ B) n))
        (congrArg (· + r) h))
        (relativeSingularCohomologyUnionCup R A B hA hB i r z c) =
      relativeSingularCohomologyUnionCup R A B hA hB j r
        (cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R A n)) h) z) c := by
    subst j
    rfl
  let T (n : ℕ) := ↥(relativeSingularCohomology R (A ∪ B) n)
  have hsmul (i j : ℕ) (h : i = j) (z : T i) (s : R) :
      cast (congrArg T h) (s • z) = s • cast (congrArg T h) z := by
    subst j
    rfl
  -- The relative reversal comparison moves the middle coefficient without forgetting support.
  rw [← hassoc]
  rw [cast_cast]
  have hsplit (z : T ((p + q) + r)) :
      cast (congrArg T (show (p + q) + r = q + (p + r) by omega)) z =
      cast (congrArg T (Nat.add_assoc q p r))
        (cast (congrArg T (congrArg (· + r) (Nat.add_comm p q))) z) := by
    rw [cast_cast]
  rw [hsplit, hcupCast _ _ (Nat.add_comm p q)]
  have hcastEq (S : Set X) (i j : ℕ) (h : i = j)
      (z : relativeSingularCohomology R S i) :
      (eqToIso (congrArg (relativeSingularCohomology R S) h)).hom z =
        cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R S n)) h) z := by
    subst j
    rfl
  rw [hcastEq A _ _ (Nat.add_comm p q)] at hδclass
  rw [hδclass, hαClass, hβClass, map_smul, LinearMap.smul_apply,
    hsmul _ _ (Nat.add_assoc q p r)]
  have hleft := relativeSingularCohomologyUnionCup_action_assoc R A B hA hB q p r b a c
  rw [hcastEq (A ∪ B) _ _ (Nat.add_assoc q p r)] at hleft
  exact congrArg (fun z : T (q + (p + r)) ↦ (-1 : R) ^ (p * q) • z) hleft

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Two relative classes with ordinary coefficients multiply with the exact middle-factor sign. -/
theorem relativeSingularCohomologyUnionCup_actions
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q r s : ℕ)
    (a : singularCohomology R X p) (b : singularCohomology R X q)
    (u : relativeSingularCohomology R A r) (v : relativeSingularCohomology R B s) :
    cast (congrArg (fun n ↦ ↥(relativeSingularCohomology R (A ∪ B) n))
      (show (p + r) + (q + s) = (p + q) + (r + s) by omega))
      (relativeSingularCohomologyUnionCup R A B hA hB (p + r) (q + s)
        (relativeSingularCohomologyAction R A p r a u)
        (relativeSingularCohomologyAction R B q s b v)) =
    (-1 : R) ^ (r * q) • relativeSingularCohomologyAction R (A ∪ B) (p + q) (r + s)
      (singularCohomologyCup R X p q a b)
      (relativeSingularCohomologyUnionCup R A B hA hB r s u v) := by
  let T (n : ℕ) := ↥(relativeSingularCohomology R (A ∪ B) n)
  have hcastEq (i j : ℕ) (h : i = j) (z : T i) :
      (eqToIso (congrArg (relativeSingularCohomology R (A ∪ B)) h)).hom z =
        cast (congrArg T h) z := by
    subst j
    rfl
  have hsmul (i j : ℕ) (h : i = j) (z : T i) (t : R) :
      cast (congrArg T h) (t • z) = t • cast (congrArg T h) z := by
    subst j
    rfl
  have hactCast (i j : ℕ) (h : i = j) (z : T i) :
      cast (congrArg T (congrArg (p + ·) h))
        (relativeSingularCohomologyAction R (A ∪ B) p i a z) =
      relativeSingularCohomologyAction R (A ∪ B) p j a (cast (congrArg T h) z) := by
    subst j
    rfl
  -- First extract the left coefficient, retaining the original relative cup in the other factor.
  have hfirst := relativeSingularCohomologyUnionCup_action_assoc R A B hA hB p r (q + s)
    a u (relativeSingularCohomologyAction R B q s b v)
  rw [hcastEq _ _ (Nat.add_assoc p r (q + s))] at hfirst
  have hmiddle := relativeSingularCohomologyUnionCup_action_right R A B hA hB r q s u b v
  have hlast := relativeSingularCohomologyAction_assoc R (A ∪ B) p q (r + s) a b
    (relativeSingularCohomologyUnionCup R A B hA hB r s u v)
  rw [hcastEq _ _ (Nat.add_assoc p q (r + s))] at hlast
  -- Work in the right-associated target degree so every remaining step keeps its own factor order.
  apply (Equiv.cast (congrArg T (Nat.add_assoc p q (r + s)))).injective
  change cast (congrArg T (Nat.add_assoc p q (r + s))) (cast _ _) =
    cast (congrArg T (Nat.add_assoc p q (r + s))) _
  rw [cast_cast, hsmul _ _ (Nat.add_assoc p q (r + s)), hlast]
  have hsplit (z : T ((p + r) + (q + s))) :
      cast (congrArg T (show (p + r) + (q + s) = p + (q + (r + s)) by omega)) z =
      cast (congrArg T (congrArg (p + ·) (show r + (q + s) = q + (r + s) by omega)))
        (cast (congrArg T (Nat.add_assoc p r (q + s))) z) := by
    rw [cast_cast]
  rw [hsplit, hfirst, hactCast _ _ (show r + (q + s) = q + (r + s) by omega),
    hmiddle, map_smul]

end AtiyahSinger
