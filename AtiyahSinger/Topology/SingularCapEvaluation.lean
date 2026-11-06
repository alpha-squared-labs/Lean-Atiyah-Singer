/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportLocallyFinitePairing
public import AtiyahSinger.Topology.RelativeSingularReversal
public import AtiyahSinger.Topology.SingularCochainReversal
public import AtiyahSinger.Topology.SingularHomologyEvaluation

/-!
# Kronecker evaluation of the original relative cap product

Public module ID: M2121.

The Alexander--Whitney front cap pairs with an ordinary class by putting that
class on the right of the relative cochain. Signed vertex reversal identifies
this evaluation with the existing ordinary-left relative action, with the
Koszul sign. The argument uses the same chain quotient and both actual
homology comparisons. In particular, it does not require an ordinary class
to lift to relative cohomology, or the relative forgetful map to be injective.

This is the cup--cap evaluation identity with the conventions of Hatcher,
Algebraic Topology, sections 3.2--3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The front cap pairs with ordinary-left relative cup with its graded sign. -/
theorem relativeSingularCapProduct_evaluation (R : Type) [CommRing R]
    {X : Type u} [TopologicalSpace X] (A : Set X) (p q : ℕ)
    (a : relativeSingularCohomology R A p) (b : singularCohomology R X q)
    (z : relativeSingularHomology R A (p + q)) :
    singularCochainHomologyEvaluation R (singularChains R X) q b
        (relativeSingularCapProduct R A p q a z) =
      (-1 : R) ^ (p * q) •
        singularCochainHomologyEvaluation R (relativeSingularChains R A) (q + p)
          (relativeSingularCohomologyAction R A q p b a)
          ((eqToIso (congrArg (relativeSingularHomology R A) (Nat.add_comm p q))).hom z) := by
  /- First compute cup--cap evaluation on the original free singular chains.
  Then reverse the ordinary-left cup and descend its actual relative quotient.
  Reversal is homotopic to the identity on each complex, so the two canonical
  quotient classes agree. The remaining sign is its own inverse. -/
  let C := relativeSingularChains R A
  let D := relativeSingularCochains R A
  let B := singularCochains R X
  let F : D ⟶ D := (singularCochainDualFunctor R).map (relativeSingularReversal R A).op
  let G := singularCochainReversal R X
  let J : D ⟶ B :=
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let ev (i : ℕ) (φ : B.X i) : (singularChains R X).X i →ₗ[R] singularCoefficient R :=
    (show (singularChains R X).X i ⟶ singularCoefficient R from φ).hom
  let evRel (i : ℕ) (φ : D.X i) : C.X i →ₗ[R] singularCoefficient R :=
    (show C.X i ⟶ singularCoefficient R from φ).hom
  -- The ordinary cup evaluates on exactly the front and back faces used by cap.
  have hcap (i j : ℕ) (α : B.X i) (β : B.X j)
      (c : (singularChains R X).X (i + j)) :
      ev j β (singularCochainCap R X i j α c) =
        ev (i + j) (singularCochainCup R X i j α β) c := by
    change (singularChains R X).X j ⟶ singularCoefficient R at β
    have h : ModuleCat.ofHom (β.hom.comp (singularCochainCap R X i j α)) =
        singularCochainCup R X i j α β := by
      apply (singularCochainEquiv R X (i + j)).injective
      funext σ
      change β (singularCochainCap R X i j α
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) σ (ULift.up 1))) = _
      rw [singularCochainCap_simplex]
      change β.hom (_ • _) = _
      rw [map_smul]
      have hcup := congrFun ((singularCochainEquiv R X (i + j)).apply_symm_apply
        (fun σ ↦ singularCochainEquiv R X i α
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace i j).op σ) *
          singularCochainEquiv R X j β
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace i j).op σ))) σ
      rw [show singularCochainEquiv R X (i + j) (singularCochainCup R X i j α β) σ = _
        from hcup]
      apply ULift.ext
      rfl
    exact congrArg (fun f : (singularChains R X).X (i + j) ⟶ singularCoefficient R ↦ f c) h
  -- All cycle representatives below belong to the original canonical homology quotients.
  have hrep {shape : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{u} R) shape)
      (i : ℕ) (x : K.homology i) :
      ∃ c : (K.sc i).moduleCatLeftHomologyData.K,
        (K.sc i).moduleCatHomologyIso.inv ((K.sc i).moduleCatToCycles.range.mkQ c) = x := by
    obtain ⟨c, hc⟩ := (K.sc i).moduleCatToCycles.range.mkQ_surjective
      ((K.sc i).moduleCatHomologyIso.hom x)
    refine ⟨c, ?_⟩
    rw [hc]
    exact congrArg (fun f ↦ f x) (K.sc i).moduleCatHomologyIso.hom_inv_id
  have hcycles (K L : CochainComplex (ModuleCat.{u} R) ℕ) (f : K ⟶ L) (i : ℕ)
      (α : (K.sc i).moduleCatLeftHomologyData.K) :
      ∃ β : (L.sc i).moduleCatLeftHomologyData.K, β.val = f.f i α.val := by
    refine ⟨⟨f.f i α.val, ?_⟩, rfl⟩
    change L.dFrom i (f.f i α.val) = 0
    have h := congrArg (fun g ↦ g α.val) (f.comm_from i)
    change L.dFrom i (f.f i α.val) = f.next i (K.dFrom i α.val) at h
    rw [h, show K.dFrom i α.val = 0 from α.property, map_zero]
  have hclass (K L : CochainComplex (ModuleCat.{u} R) ℕ) (f : K ⟶ L) (i : ℕ)
      (α : (K.sc i).moduleCatLeftHomologyData.K)
      (β : (L.sc i).moduleCatLeftHomologyData.K) (h : f.f i α.val = β.val) :
      HomologicalComplex.homologyMap f i
          ((K.sc i).moduleCatHomologyIso.inv ((K.sc i).moduleCatToCycles.range.mkQ α)) =
        (L.sc i).moduleCatHomologyIso.inv ((L.sc i).moduleCatToCycles.range.mkQ β) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) i).map f
    let H := ShortComplex.leftHomologyMapData S
      (K.sc i).moduleCatLeftHomologyData (L.sc i).moduleCatLeftHomologyData
    have hcycles : H.φK α = β := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f α) H.commi).trans h
    have hquot := congrArg (fun f ↦ f α) H.commπ
    change H.φH ((K.sc i).moduleCatToCycles.range.mkQ α) =
      (L.sc i).moduleCatToCycles.range.mkQ (H.φK α) at hquot
    rw [hcycles] at hquot
    have hmap := H.homologyMap_eq
    change HomologicalComplex.homologyMap f i = _ at hmap
    rw [hmap]
    change (L.sc i).moduleCatHomologyIso.inv
      (H.φH ((K.sc i).moduleCatHomologyIso.hom
        ((K.sc i).moduleCatHomologyIso.inv ((K.sc i).moduleCatToCycles.range.mkQ α)))) = _
    have hcancel : (K.sc i).moduleCatHomologyIso.hom
        ((K.sc i).moduleCatHomologyIso.inv ((K.sc i).moduleCatToCycles.range.mkQ α)) =
          (K.sc i).moduleCatToCycles.range.mkQ α :=
      congrArg (fun f ↦ f ((K.sc i).moduleCatToCycles.range.mkQ α))
        (K.sc i).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  -- The specified quotient homotopy makes relative reversal the identity on cohomology.
  have hhom (i : ℕ) : HomologicalComplex.homologyMap F i = 𝟙 _ := by
    let dual := ((linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)).rightOp
    have H := (dual.mapHomotopy (relativeSingularReversalHomotopy R A)).unop
    change Homotopy ((singularCochainDualFunctor R).map (𝟙 C).op) F at H
    have h := H.homologyMap_eq i
    rw [show (𝟙 C).op = 𝟙 (op C) from rfl,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at h
    exact h.symm
  have hrev (i : ℕ) (α β : relativeSingularCocycles R A i)
      (h : β.val = F.f i α.val) :
      relativeSingularCocycleClass R A i β = relativeSingularCocycleClass R A i α := by
    have hc := hclass D D F i α β h.symm
    change HomologicalComplex.homologyMap F i (relativeSingularCocycleClass R A i α) =
      relativeSingularCocycleClass R A i β at hc
    rw [hhom] at hc
    exact hc.symm
  have hprojection : F ≫ J = J ≫ G := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ =
      (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R A ≫ relativeSingularReversal R A).op =
      (singularCochainDualFunctor R).map
        (singularReversal R X ≫ relativeSingularChainsProjection R A).op
    rw [relativeSingularChainsProjection_reversal]
  have hcomp (i : ℕ) (α : D.X i) : J.f i (F.f i α) = G.f i (J.f i α) :=
    congrArg (fun f ↦ f.f i α) hprojection
  have haction (i j : ℕ) (α : B.X i) (β : D.X j) :
      J.f (i + j) (relativeSingularCochainAction R A i j α β) =
        singularCochainCup R X i j α (J.f j β) :=
    congrArg Subtype.val ((relativeSingularCochainEquiv R A (i + j)).apply_symm_apply _)
  have hdegree {i j : ℕ} (h : i = j) (α : D.X i) :
      J.f j ((D.XIsoOfEq h).hom α) = (B.XIsoOfEq h).hom (J.f i α) := by
    subst j
    rfl
  -- Reversing ordinary-left cup gives the exact cap evaluation after projecting chains.
  have hscalar (α : D.X p) (β : B.X q) (c : C.X (p + q)) :
      evRel (p + q) ((D.XIsoOfEq (Nat.add_comm q p)).hom
          (F.f (q + p) (relativeSingularCochainAction R A q p β α))) c =
        (-1 : R) ^ (q * p) •
          ev q (G.f q β) (relativeSingularCochainCap R A p q (F.f p α) c) := by
    obtain ⟨d, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relativeSingularChainsProjection R A).f (p + q))).mp inferInstance c
    rw [relativeSingularCochainCap_projection]
    change ev (p + q) (J.f (p + q) _) d = _
    rw [hdegree, hcomp, haction, singularCochainReversal_cup]
    change ev (p + q)
      ((-1 : R) ^ (q * p) • singularCochainCup R X p q (G.f p (J.f p α)) (G.f q β)) d = _
    rw [← hcomp]
    change (-1 : R) ^ (q * p) • ev (p + q)
      (singularCochainCup R X p q (J.f p (F.f p α)) (G.f q β)) d = _
    rw [← hcap]
    rfl
  have hevalTransport (i j : ℕ) (h : i = j)
      (φ : relativeSingularCocycles R A j) (c : relativeSingularCycles R A i) :
      singularCochainHomologyEvaluation R C j (relativeSingularCocycleClass R A j φ)
          ((eqToIso (congrArg (relativeSingularHomology R A) h)).hom
            (relativeSingularCycleClass R A i c)) =
        evRel i ((D.XIsoOfEq h.symm).hom φ.val) c.val := by
    subst j
    exact singularCochainHomologyEvaluation_cycleClass R C i φ c
  obtain ⟨α, rfl⟩ := hrep D p a
  obtain ⟨β, rfl⟩ := hrep B q b
  obtain ⟨c, rfl⟩ := hrep C (p + q) z
  obtain ⟨α', hα'⟩ := hcycles D D F p α
  obtain ⟨β', hβ'⟩ := hcycles B B G q β
  let γ := relativeSingularCocycleAction R A q p β α
  obtain ⟨γ', hγ'⟩ := hcycles D D F (q + p) γ
  have hβclass : singularCocycleClass R X q β' = singularCocycleClass R X q β := by
    have h := hclass B B G q β β' hβ'.symm
    change HomologicalComplex.homologyMap (singularCochainReversal R X) q
      (singularCocycleClass R X q β) = singularCocycleClass R X q β' at h
    rw [homologyMap_singularCochainReversal] at h
    exact h.symm
  -- Evaluate the reversed product on the same cycle, then descend the cap on both inputs.
  have hpair :
      singularCochainHomologyEvaluation R C (q + p)
          (relativeSingularCohomologyAction R A q p
            (singularCocycleClass R X q β) (relativeSingularCocycleClass R A p α))
          ((eqToIso (congrArg (relativeSingularHomology R A) (Nat.add_comm p q))).hom
            (relativeSingularCycleClass R A (p + q) c)) =
        (-1 : R) ^ (q * p) • singularCochainHomologyEvaluation R (singularChains R X) q
          (singularCocycleClass R X q β)
          (relativeSingularCapProduct R A p q (relativeSingularCocycleClass R A p α)
            (relativeSingularCycleClass R A (p + q) c)) := by
    rw [relativeSingularCohomologyAction_cocycleClass]
    change singularCochainHomologyEvaluation R C (q + p)
      (relativeSingularCocycleClass R A (q + p) γ) _ = _
    rw [← hrev (q + p) γ γ' hγ',
      hevalTransport (p + q) (q + p) (Nat.add_comm p q) γ' c, hγ']
    change evRel (p + q) ((D.XIsoOfEq (Nat.add_comm q p)).hom
      (F.f (q + p) (relativeSingularCochainAction R A q p β.val α.val))) c.val = _
    rw [hscalar, ← hα', ← hβ']
    congr 1
    rw [← hβclass, ← hrev p α α' hα', relativeSingularCapProduct_cycleClass]
    exact (singularCochainHomologyEvaluation_cycleClass R (singularChains R X) q β'
      (relativeSingularCycleCap R A p q α' c)).symm
  have h := congrArg (fun v : singularCoefficient R ↦ (-1 : R) ^ (p * q) • v) hpair
  have hsign : (-1 : R) ^ (p * q) * (-1 : R) ^ (p * q) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [Nat.mul_comm q p, smul_smul, hsign, one_smul] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pairing cap duality with an ordinary class is integration of the same supported action. -/
theorem compactPoincareDuality_evaluation {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (O : HomologicalOrientation n M) (p q : ℕ) (h : p + q = n)
    (a : compactSupportCohomology ℚ M p) (b : singularCohomology ℚ M q) :
    (singularCochainHomologyEvaluation ℚ (singularChains ℚ M) q b
        (compactPoincareDuality O p q h a)).down =
      (-1 : ℚ) ^ (p * q) * compactSupportCohomologyIntegral O
        ((eqToIso (congrArg (compactSupportCohomology ℚ M)
          ((Nat.add_comm q p).trans h))).hom
          (compactSupportCohomologyAction ℚ M q p b a)) := by
  /- Both global operations descend from the very same compact representative.
  The normalized locally finite class restricts to its original relative
  fundamental class. The relative cup--cap evaluation formula then applies,
  with the degree equality transporting the class and its test cycle dually. -/
  subst n
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative ℚ M p a
  have htransport (i j : ℕ) (hij : i = j)
      (c : relativeSingularCohomology ℚ ((K : Set M)ᶜ) i) :
      (eqToIso (congrArg (compactSupportCohomology ℚ M) hij)).hom
          (compactSupportCohomologyClass ℚ M K i c) =
        compactSupportCohomologyClass ℚ M K j
          ((eqToIso (congrArg (relativeSingularCohomology ℚ ((K : Set M)ᶜ)) hij)).hom c) := by
    subst j
    rfl
  have heval (i j : ℕ) (hij : i = j)
      (c : relativeSingularCohomology ℚ ((K : Set M)ᶜ) i)
      (z : relativeSingularHomology ℚ ((K : Set M)ᶜ) j) :
      singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ((K : Set M)ᶜ)) j
          ((eqToIso (congrArg (relativeSingularCohomology ℚ ((K : Set M)ᶜ)) hij)).hom c) z =
        singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ((K : Set M)ᶜ)) i c
          ((eqToIso (congrArg (relativeSingularHomology ℚ ((K : Set M)ᶜ)) hij.symm)).hom z) := by
    subst j
    rfl
  rw [compactSupportCohomologyAction_representative,
    htransport (q + p) (p + q) (Nat.add_comm q p),
    compactSupportCohomologyIntegral_eq_duality_augmentation,
    compactPoincareDuality_representative, compactPoincareDuality_representative]
  change (singularCochainHomologyEvaluation ℚ (singularChains ℚ M) q b
    (relativeSingularCapProduct ℚ ((K : Set M)ᶜ) p q α
      (rationalCompactRelativeFundamentalClass O K))).down =
    (-1 : ℚ) ^ (p * q) *
      ((TopCat.of M).singularHomology₀ε (singularCoefficient ℚ)
        (relativeSingularCapProduct ℚ ((K : Set M)ᶜ) (p + q) 0
          ((eqToIso (congrArg (relativeSingularCohomology ℚ ((K : Set M)ᶜ))
            (Nat.add_comm q p))).hom (relativeSingularCohomologyAction ℚ ((K : Set M)ᶜ)
              q p b α)) (rationalCompactRelativeFundamentalClass O K))).down
  rw [relativeSingularCapProduct_augmentation,
    heval (q + p) (p + q) (Nat.add_comm q p)]
  exact congrArg ULift.down
    (relativeSingularCapProduct_evaluation ℚ ((K : Set M)ᶜ) p q α b
      (rationalCompactRelativeFundamentalClass O K))

end AtiyahSinger
