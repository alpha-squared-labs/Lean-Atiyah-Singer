/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyCup
public import AtiyahSinger.Topology.RelativeSingularReversal
public import AtiyahSinger.Topology.SingularCochainReversal

/-!
# Graded commutativity for the same relative singular pair

Public module ID: M2064.

Both factors are classes of the original pair (X,A). The relative action takes
its first factor through the specified forgetful map, and its product remains
in the same relative group. Signed reversal and its quotient homotopy identify
the two products after exchanging degrees. Equality is checked on relative
cochains through the injective dual of the chain quotient projection; no
injectivity of the map from relative to ordinary cohomology is assumed.

This is the relative form of the standard reversal proof of the singular
cup-product commutativity theorem, as in Hatcher, section 3.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The product of two classes of the same relative pair is graded commutative. -/
theorem relativeSingularCohomologyAction_comm (A : Set X) (p q : ℕ)
    (a : relativeSingularCohomology R A p) (b : relativeSingularCohomology R A q) :
    (eqToIso (by rw [Nat.add_comm p q]) :
        relativeSingularCohomology R A (p + q) ≅ relativeSingularCohomology R A (q + p)).hom
      (relativeSingularCohomologyAction R A p q
        (relativeSingularCohomologyToOrdinary R A p a) b) =
      (-1 : R) ^ (p * q) • relativeSingularCohomologyAction R A q p
        (relativeSingularCohomologyToOrdinary R A q b) a := by
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
  let C := relativeSingularCochains R A
  let D := singularCochains R X
  let F : C ⟶ C := (singularCochainDualFunctor R).map (relativeSingularReversal R A).op
  let G := singularCochainReversal R X
  let J : C ⟶ D :=
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  -- The same quotient homotopy makes reversal the identity on relative cohomology itself.
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
    have h := hclass C C F n γ δ hδ.symm
    change HomologicalComplex.homologyMap F n (relativeSingularCocycleClass R A n γ) =
      relativeSingularCocycleClass R A n δ at h
    rw [hhom] at h
    exact h.symm
  -- The relative and ordinary reversals commute with this exact quotient projection.
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
  have hcomm (α : C.X p) (β : C.X q) :
      (C.XIsoOfEq (Nat.add_comm p q)).hom
          (F.f (p + q) (relativeSingularCochainAction R A p q (J.f p α) β)) =
        (-1 : R) ^ (p * q) • relativeSingularCochainAction R A q p
          (J.f q (F.f q β)) (F.f p α) := by
    -- Injectivity is used only for relative cochains, before taking cohomology.
    apply (relativeSingularCochainEquiv R A (q + p)).injective
    apply Subtype.ext
    change J.f (q + p) _ = J.f (q + p) _
    rw [hdegree, hcomp, haction, map_smul, haction, hcomp, hcomp]
    exact singularCochainReversal_cup R X p q (J.f p α) (J.f q β)
  -- Choose the actual relative representatives and their reversed and forgotten representatives.
  obtain ⟨α, hα⟩ := hrep C p a
  obtain ⟨β, hβ⟩ := hrep C q b
  change relativeSingularCocycleClass R A p α = a at hα
  change relativeSingularCocycleClass R A q β = b at hβ
  obtain ⟨α', hα'⟩ := hcycles C C F p α
  obtain ⟨β', hβ'⟩ := hcycles C C F q β
  obtain ⟨α₀, hα₀⟩ := hcycles C D J p α
  obtain ⟨β₀', hβ₀'⟩ := hcycles C D J q β'
  have ha := hclass C D J p α α₀ hα₀.symm
  have hb := (hclass C D J q β' β₀' hβ₀'.symm).symm
  change relativeSingularCohomologyToOrdinary R A p
    (relativeSingularCocycleClass R A p α) = singularCocycleClass R X p α₀ at ha
  change singularCocycleClass R X q β₀' = relativeSingularCohomologyToOrdinary R A q
    (relativeSingularCocycleClass R A q β') at hb
  let γ := relativeSingularCocycleAction R A p q α₀ β
  obtain ⟨γ', hγ'⟩ := hcycles C C F (p + q) γ
  rw [← hα, ← hβ, ha, relativeSingularCohomologyAction_cocycleClass]
  change (eqToIso (congrArg (fun n ↦ C.homology n) (Nat.add_comm p q))).hom
    (relativeSingularCocycleClass R A (p + q) γ) = _
  rw [← hrev (p + q) γ γ' hγ']
  have hcochain : (C.XIsoOfEq (Nat.add_comm p q)).hom γ'.val =
      ((-1 : R) ^ (p * q) • relativeSingularCocycleAction R A q p β₀' α').val := by
    rw [hγ']
    change (C.XIsoOfEq (Nat.add_comm p q)).hom
      (F.f (p + q) (relativeSingularCochainAction R A p q α₀.val β.val)) =
        (-1 : R) ^ (p * q) • relativeSingularCochainAction R A q p β₀'.val α'.val
    rw [hα₀, hβ₀', hα', hβ']
    exact hcomm α.val β.val
  have ht := htransport C (p + q) (q + p) (Nat.add_comm p q) γ'
    ((-1 : R) ^ (p * q) • relativeSingularCocycleAction R A q p β₀' α') hcochain
  change (eqToIso (congrArg (fun n ↦ C.homology n) (Nat.add_comm p q))).hom
    (relativeSingularCocycleClass R A (p + q) γ') = relativeSingularCocycleClass R A (q + p)
      ((-1 : R) ^ (p * q) • relativeSingularCocycleAction R A q p β₀' α') at ht
  rw [ht, map_smul, ← relativeSingularCohomologyAction_cocycleClass,
    hb, hrev q β β' hβ', hrev p α α' hα']

end AtiyahSinger
