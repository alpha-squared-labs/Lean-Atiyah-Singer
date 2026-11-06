/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCapProduct
public import AtiyahSinger.Topology.RelativeSingularFunctoriality

/-!
# Naturality of the original relative cap product

Public module ID: M2057.

A map of pairs commutes with front-face evaluation and back-face pushforward.
The identity is proved on the original chain coproduct, then on the relative
cokernel, and finally on the actual cycle quotients. It applies over any
commutative coefficient ring and retains the front-face cap convention.

This is the standard cap naturality identity in Hatcher, Algebraic Topology,
section 3.3. It is needed for open extension of the specified fundamental
classes and for the comparison of integration with geometric pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A continuous map commutes with the actual front/back cap operation on singular chains. -/
theorem singularCochainCap_naturality (f : C(X, Y)) (p q : ℕ)
    (φ : (singularCochains R Y).X p) (c : (singularChains R X).X (p + q)) :
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f q
      (singularCochainCap R X p q
        (((singularCochainsFunctor R).map (TopCat.ofHom f).op).f p φ) c) =
      singularCochainCap R Y p q φ
        (((singularChainsFunctor R).map (TopCat.ofHom f)).f (p + q) c) := by
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  let P := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  let SX := TopCat.toSSet.obj (TopCat.of X)
  let SY := TopCat.toSSet.obj (TopCat.of Y)
  have hgen (k : ℕ) (σ : SX.obj (op ⦋k⦌)) :
      F.f k (SX.ιChainComplex (R := singularCoefficient R) σ (ULift.up 1)) =
        SY.ιChainComplex (R := singularCoefficient R)
          (g.app (op ⦋k⦌) σ) (ULift.up 1) := by
    change (SX.ιChainComplex σ ≫ (SSet.chainComplexMap g (singularCoefficient R)).f k)
      (ULift.up 1) = _
    rw [SSet.ι_chainComplexMap_f]
  have heval (σ : SX.obj (op ⦋p⦌)) :
      singularCochainEquiv R X p (P.f p φ) σ =
        singularCochainEquiv R Y p φ (g.app (op ⦋p⦌) σ) := by
    change (show (singularChains R Y).X p ⟶ singularCoefficient R from φ)
      (F.f p (SX.ιChainComplex (R := singularCoefficient R) σ (ULift.up 1))) = _
    rw [hgen]
    rfl
  -- Equality on coefficient-one generators determines each linear map out of the coproduct.
  have hmaps : ModuleCat.ofHom ((F.f q).hom.comp
      (singularCochainCap R X p q (P.f p φ))) =
      ModuleCat.ofHom ((singularCochainCap R Y p q φ).comp (F.f (p + q)).hom) := by
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have ha : a = a.down • (ULift.up 1 : ULift.{u} R) := by
      apply ULift.ext
      simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change F.f q (singularCochainCap R X p q (P.f p φ)
      (SX.ιChainComplex (R := singularCoefficient R) σ (ULift.up 1))) =
      singularCochainCap R Y p q φ
        (F.f (p + q) (SX.ιChainComplex (R := singularCoefficient R) σ (ULift.up 1)))
    rw [hgen, singularCochainCap_simplex, singularCochainCap_simplex]
    change (F.f q).hom (_ • _) = _
    erw [map_smul, hgen, heval]
    have hfront := congrArg (fun t ↦ t σ) (g.naturality (singularCupFrontFace p q).op)
    have hback := congrArg (fun t ↦ t σ) (g.naturality (singularCupBackFace p q).op)
    exact congrArg₂ (fun s t ↦ (singularCochainEquiv R Y p φ s).down •
      SY.ιChainComplex (R := singularCoefficient R) t (ULift.up 1))
      hfront.symm hback.symm
  exact congrArg (fun h ↦ h c) hmaps

/-- The original relative cap product is natural under a continuous map of pairs. -/
theorem relativeSingularCapProduct_naturality (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (p q : ℕ)
    (a : relativeSingularCohomology R B p) (z : relativeSingularHomology R A (p + q)) :
    singularHomologyMap R f q
      (relativeSingularCapProduct R A p q (relativeSingularCohomologyPullback R f hf p a) z) =
      relativeSingularCapProduct R B p q a (relativeSingularHomologyMap R f hf (p + q) z) := by
  -- Choose actual quotient representatives in either of the original homological complexes.
  have hrep {shape : ComplexShape ℕ} (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- Naturality of the fixed homology comparisons computes classes under the specified maps.
  have hclass {shape : ComplexShape ℕ}
      (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) shape n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
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
  -- The same chain or cochain map sends the original outgoing kernel into its counterpart.
  have hcycles {shape : ComplexShape ℕ}
      (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  let F := relativeSingularChainsMap R f hf
  let G := (singularCochainDualFunctor R).map F.op
  let O := (singularChainsFunctor R).map (TopCat.ofHom f)
  let P := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  let JA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  -- The quotient square dualizes to the exact same cochain pullback square.
  have hchain : relativeSingularChainsProjection R A ≫ F =
      O ≫ relativeSingularChainsProjection R B := by
    simp [F, O, relativeSingularChainsProjection, relativeSingularChainsMap]
  have hdual : G ≫ JA = JB ≫ P := by
    change (singularCochainDualFunctor R).map F.op ≫
      (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op =
        (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op ≫
          (singularCochainDualFunctor R).map O.op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hchain]
  have hcap (α : (relativeSingularCochains R B).X p)
      (c : (relativeSingularChains R A).X (p + q)) :
      O.f q (relativeSingularCochainCap R A p q (G.f p α) c) =
        relativeSingularCochainCap R B p q α (F.f (p + q) c) := by
    -- Lift only the chain, using the actual quotient projection's surjectivity.
    obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relativeSingularChainsProjection R A).f (p + q))).mp inferInstance c
    have hchainval := congrArg (fun h ↦ h.f (p + q) v) hchain
    change F.f (p + q) ((relativeSingularChainsProjection R A).f (p + q) v) =
      (relativeSingularChainsProjection R B).f (p + q) (O.f (p + q) v) at hchainval
    rw [hchainval, relativeSingularCochainCap_projection, relativeSingularCochainCap_projection]
    have hdualval := congrArg (fun h ↦ h.f p α) hdual
    change (relativeSingularCochainEquiv R A p (G.f p α)).val =
      P.f p (relativeSingularCochainEquiv R B p α).val at hdualval
    rw [hdualval]
    exact singularCochainCap_naturality R f p q _ v
  -- Descend through the original cocycle and cycle representatives.
  obtain ⟨α, hα⟩ := hrep (relativeSingularCochains R B) p a
  obtain ⟨c, hc⟩ := hrep (relativeSingularChains R A) (p + q) z
  change relativeSingularCocycleClass R B p α = a at hα
  change relativeSingularCycleClass R A (p + q) c = z at hc
  obtain ⟨α', hα'⟩ := hcycles (relativeSingularCochains R B)
    (relativeSingularCochains R A) G p α
  obtain ⟨c', hc'⟩ := hcycles (relativeSingularChains R A)
    (relativeSingularChains R B) F (p + q) c
  have ha := hclass (relativeSingularCochains R B) (relativeSingularCochains R A)
    G p α α' hα'.symm
  have hz := hclass (relativeSingularChains R A) (relativeSingularChains R B)
    F (p + q) c c' hc'.symm
  change relativeSingularCohomologyPullback R f hf p
    (relativeSingularCocycleClass R B p α) = relativeSingularCocycleClass R A p α' at ha
  change relativeSingularHomologyMap R f hf (p + q)
    (relativeSingularCycleClass R A (p + q) c) = relativeSingularCycleClass R B (p + q) c' at hz
  rw [← hα, ← hc, ha, hz, relativeSingularCapProduct_cycleClass,
    relativeSingularCapProduct_cycleClass]
  apply hclass (singularChains R X) (singularChains R Y) O q
  change O.f q (relativeSingularCochainCap R A p q α'.val c.val) =
    relativeSingularCochainCap R B p q α.val c'.val
  rw [hα', hc']
  exact hcap α.val c.val

end AtiyahSinger
