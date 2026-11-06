/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyRationalization
public import AtiyahSinger.Topology.SingularHomologyEvaluation

/-!
# Coefficient change in the relative Kronecker pairing

Public module ID: M2079.

The original integral chain and cochain coefficient maps preserve their
evaluation pairing. Passing through the original homology quotients gives
the corresponding statement for integral classes and their rational images.
This provides the normalization needed for rational fiber orientations;
it asserts no general rationalization isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Rationalizing both entries preserves the original relative Kronecker pairing. -/
theorem singularCochainHomologyEvaluation_rationalization
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (a : relativeSingularCohomology ℤ A n) (z : relativeSingularHomology ℤ A n) :
    (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ A) n
      (relativeSingularCohomologyRationalization A n a)
      (relativeSingularHomologyRationalization A n z)).down =
        ((singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ A) n a z).down :
          ℚ) := by
  -- The coefficient maps agree on the same original simplex, before taking quotients.
  let coefficient : singularCoefficient.{u} ℤ →ₗ[ℤ] singularCoefficient.{u} ℚ :=
    { toFun := fun a ↦ ULift.up (a.down : ℚ)
      map_add' := by intros; apply ULift.ext; simp
      map_smul' := by intros; apply ULift.ext; simp }
  have hordinary (k : ℕ) (φ : (singularCochains ℤ X).X k)
      (c : (singularChains ℤ X).X k) :
      (show (singularChains ℚ X).X k ⟶ singularCoefficient ℚ from
          (singularCochainsRationalization X).f k φ)
        ((singularChainsRationalization X).f k c) =
          coefficient ((show (singularChains ℤ X).X k ⟶ singularCoefficient ℤ from φ) c) := by
    have heq : (singularChainsRationalization X).f k ≫
        (ModuleCat.restrictScalars (Int.castRingHom ℚ)).map
          (show (singularChains ℚ X).X k ⟶ singularCoefficient ℚ from
            (singularCochainsRationalization X).f k φ) =
          (show (singularChains ℤ X).X k ⟶ singularCoefficient ℤ from φ) ≫
            ModuleCat.ofHom coefficient := by
      apply Sigma.hom_ext
      intro σ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      have hchain : (singularChainsRationalization X).f k
          ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient ℤ) σ t) =
          (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient ℚ) σ (ULift.up (t.down : ℚ)) :=
        (existsUnique_singularChainsRationalization X).exists.choose_spec k σ t.down
      change (show (singularChains ℚ X).X k ⟶ singularCoefficient ℚ from
        (singularCochainsRationalization X).f k φ)
        ((singularChainsRationalization X).f k
          ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient ℤ) σ t)) = _
      rw [hchain]
      have hcochain := (existsUnique_singularCochainsRationalization X).exists.choose_spec
        k φ σ
      let ιZ := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient ℤ) σ
      let ιQ := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient ℚ) σ
      let φQ : (singularChains ℚ X).X k ⟶ singularCoefficient ℚ :=
        (singularCochainsRationalization X).f k φ
      let φZ : (singularChains ℤ X).X k ⟶ singularCoefficient ℤ := φ
      change φQ (ιQ (ULift.up 1)) = coefficient (φZ (ιZ (ULift.up 1))) at hcochain
      have htZ : ιZ t = t.down • ιZ (ULift.up 1) := by
        rw [← map_zsmul]
        apply congrArg ιZ
        apply ULift.ext
        simp
      have htQ : ιQ (ULift.up (t.down : ℚ)) = (t.down : ℚ) • ιQ (ULift.up 1) := by
        rw [← map_smul]
        apply congrArg ιQ
        apply ULift.ext
        simp
      change φQ (ιQ (ULift.up (t.down : ℚ))) = coefficient (φZ (ιZ t))
      rw [htQ, map_smul, hcochain, htZ, map_zsmul, map_zsmul]
      exact Int.cast_smul_eq_zsmul ℚ t.down (coefficient (φZ (ιZ (ULift.up 1))))
    exact congrArg (fun f ↦ f c) heq
  have hrelative (k : ℕ) (φ : (relativeSingularCochains ℤ A).X k)
      (c : (relativeSingularChains ℤ A).X k) :
      (show (relativeSingularChains ℚ A).X k ⟶ singularCoefficient ℚ from
          (relativeSingularCochainsRationalization A).f k φ)
        ((relativeSingularChainsRationalization A).f k c) =
          coefficient ((show (relativeSingularChains ℤ A).X k ⟶
            singularCoefficient ℤ from φ) c) := by
    obtain ⟨d, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relativeSingularChainsProjection ℤ A).f k)).mp inferInstance c
    have hchain := congrArg (fun F ↦ F.f k d)
      (existsUnique_relativeSingularChainsRationalization A).exists.choose_spec
    have hcochain := congrArg (fun F ↦ F.f k φ)
      (existsUnique_relativeSingularCochainsRationalization A).exists.choose_spec
    change (show (relativeSingularChains ℚ A).X k ⟶ singularCoefficient ℚ from
      (relativeSingularCochainsRationalization A).f k φ)
      ((relativeSingularChainsRationalization A).f k
        ((relativeSingularChainsProjection ℤ A).f k d)) = _
    change (relativeSingularChainsRationalization A).f k
      ((relativeSingularChainsProjection ℤ A).f k d) =
      (relativeSingularChainsProjection ℚ A).f k
        ((singularChainsRationalization X).f k d) at hchain
    rw [hchain]
    have hvalue := congrArg (fun f : (singularCochains ℚ X).X k ↦
      (show (singularChains ℚ X).X k ⟶ singularCoefficient ℚ from f)
        ((singularChainsRationalization X).f k d)) hcochain
    exact hvalue.trans (hordinary k
      (((singularCochainDualFunctor ℤ).map
        (relativeSingularChainsProjection ℤ A).op).f k φ) d)
  -- Use the canonical representative formula for each scalar-restriction comparison.
  have hclass (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      {shape : ComplexShape ℕ}
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
  have hrep (R : Type) [CommRing R] {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  have hcycles (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (D : HomologicalComplex (ModuleCat.{u} S) shape)
      (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
        shape).obj D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  obtain ⟨φ, rfl⟩ := hrep ℤ (relativeSingularCochains ℤ A) n a
  obtain ⟨c, rfl⟩ := hrep ℤ (relativeSingularChains ℤ A) n z
  obtain ⟨φQ, hφQ⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ)
    (relativeSingularCochains ℤ A) (relativeSingularCochains ℚ A)
    (relativeSingularCochainsRationalization A) n φ
  obtain ⟨cQ, hcQ⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ)
    (relativeSingularChains ℤ A) (relativeSingularChains ℚ A)
    (relativeSingularChainsRationalization A) n c
  have hφ := hclass ℤ ℚ (Int.castRingHom ℚ) _ _
    (relativeSingularCochainsRationalization A) n φ φQ hφQ.symm
  have hc := hclass ℤ ℚ (Int.castRingHom ℚ) _ _
    (relativeSingularChainsRationalization A) n c cQ hcQ.symm
  change relativeSingularCohomologyRationalization A n _ = _ at hφ
  change relativeSingularHomologyRationalization A n _ = _ at hc
  rw [hφ, hc, singularCochainHomologyEvaluation_cycleClass,
    singularCochainHomologyEvaluation_cycleClass]
  change ((show (relativeSingularChains ℚ A).X n ⟶
    singularCoefficient ℚ from φQ.val) cQ.val).down = _
  rw [hφQ, hcQ]
  exact congrArg ULift.down (hrelative n φ.val c.val)

end AtiyahSinger
