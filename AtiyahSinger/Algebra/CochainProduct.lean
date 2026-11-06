/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic

/-!
# Degreewise products of module cochain complexes

Public module ID: M0005.

The concrete product has tuples of the original module elements in every degree
and the pointwise differential. Its induced maps retain the specified component
cochain maps and their order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R]

/-- The degreewise product of module cochain complexes, with its pointwise differential.
This concrete product keeps the component cochains accessible in Čech descent. -/
def cochainFamilyProduct {ι : Type u}
    (C : ι → CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ where
  X q := ModuleCat.of R (∀ i, (C i).X q)
  d p q := ModuleCat.ofHom
    { toFun := fun c i ↦ (C i).d p q (c i)
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  shape p q hpq := by
    ext c i
    exact congrArg (fun f ↦ f (c i)) ((C i).shape p q hpq)
  d_comp_d' p q r _ _ := by
    ext c i
    exact congrArg (fun f ↦ f (c i)) ((C i).d_comp_d p q r)

/-- The map of degreewise products induced by specified component cochain maps. -/
def cochainFamilyProductMap {ι κ : Type u}
    {C : ι → CochainComplex (ModuleCat.{u} R) ℕ}
    {D : κ → CochainComplex (ModuleCat.{u} R) ℕ}
    (j : κ → ι) (f : ∀ k, C (j k) ⟶ D k) :
    cochainFamilyProduct R C ⟶ cochainFamilyProduct R D where
  f q := ModuleCat.ofHom
    { toFun := fun c k ↦ (f k).f q (c (j k))
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext k
    exact congrArg (fun F ↦ F (c (j k))) ((f k).comm p q)

/-- Projection to one of the original cochain complexes in the degreewise product. -/
def cochainFamilyProductProjection {ι : Type u}
    (C : ι → CochainComplex (ModuleCat.{u} R) ℕ) (i : ι) :
    cochainFamilyProduct R C ⟶ C i where
  f _ := ModuleCat.ofHom (LinearMap.proj i)
  comm' _ _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cohomology of a degreewise product of modules is the product of their cohomology.
The comparison consists of the original projection maps, including for an empty family. -/
theorem bijective_homologyMap_cochainFamilyProductProjection {ι : Type u}
    (C : ι → CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Bijective (fun z : (cochainFamilyProduct R C).homology n ↦
      fun i ↦ HomologicalComplex.homologyMap (cochainFamilyProductProjection R C i) n z) := by
  let P := cochainFamilyProduct R C
  let cc (D : CochainComplex (ModuleCat.{u} R) ℕ)
      (a : (D.sc n).moduleCatLeftHomologyData.K) : D.homology n :=
    (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ a)
  have hrep (D : CochainComplex (ModuleCat.{u} R) ℕ) (z : D.homology n) :
      ∃ a, cc D a = z := by
    obtain ⟨a, ha⟩ := (D.sc n).moduleCatToCycles.range.mkQ_surjective
      ((D.sc n).moduleCatHomologyIso.hom z)
    refine ⟨a, ?_⟩
    dsimp only [cc]
    rw [ha]
    exact congrArg (fun f ↦ f z) (D.sc n).moduleCatHomologyIso.hom_inv_id
  have hzero (D : CochainComplex (ModuleCat.{u} R) ℕ)
      (a : (D.sc n).moduleCatLeftHomologyData.K) :
      cc D a = 0 ↔ ∃ b, (D.sc n).f b = a.val := by
    constructor
    · intro h
      have hz := congrArg (D.sc n).moduleCatHomologyIso.hom h
      change (D.sc n).moduleCatHomologyIso.hom
        ((D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ a)) = _ at hz
      rw [Iso.inv_hom_id_apply, map_zero] at hz
      obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
      exact ⟨b, congrArg Subtype.val hb⟩
    · rintro ⟨b, hb⟩
      have hz : (D.sc n).moduleCatToCycles.range.mkQ a = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, Subtype.ext hb⟩
      change (D.sc n).moduleCatHomologyIso.inv _ = 0
      rw [hz, map_zero]
  -- The projection homology maps send the same tuple of cocycles to its components.
  have hmap (i : ι) (a : (P.sc n).moduleCatLeftHomologyData.K)
      (b : ((C i).sc n).moduleCatLeftHomologyData.K) (hab : a.val i = b.val) :
      HomologicalComplex.homologyMap (cochainFamilyProductProjection R C i) n
        (cc P a) = cc (C i) b := by
    let F := cochainFamilyProductProjection R C i
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map F
    let G := ShortComplex.leftHomologyMapData S
      (P.sc n).moduleCatLeftHomologyData ((C i).sc n).moduleCatLeftHomologyData
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans hab
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((P.sc n).moduleCatToCycles.range.mkQ a) =
      ((C i).sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap]
    change ((C i).sc n).moduleCatHomologyIso.inv
      (G.φH ((P.sc n).moduleCatHomologyIso.hom
        ((P.sc n).moduleCatHomologyIso.inv ((P.sc n).moduleCatToCycles.range.mkQ a)))) = _
    rw [Iso.inv_hom_id_apply, hquot]
  constructor
  · -- A tuple with zero component classes admits a tuple of boundary primitives.
    intro x y hxy
    obtain ⟨a, ha⟩ := hrep P (x - y)
    have hi (i : ι) : ∃ b : ((C i).sc n).X₁, ((C i).sc n).f b = a.val i := by
      let ai : ((C i).sc n).moduleCatLeftHomologyData.K :=
        ⟨a.val i, congrFun a.property i⟩
      apply (hzero (C i) ai).mp
      rw [← hmap i a ai rfl, ha, map_sub]
      exact sub_eq_zero.mpr (congrFun hxy i)
    choose b hb using hi
    have hz : cc P a = 0 := (hzero P a).mpr ⟨b, funext hb⟩
    exact sub_eq_zero.mp (ha.symm.trans hz)
  · -- Choose a cocycle in each prescribed class and form the actual product cocycle.
    intro z
    choose a ha using fun i ↦ hrep (C i) (z i)
    let c : (P.sc n).moduleCatLeftHomologyData.K :=
      ⟨fun i ↦ (a i).val, funext (fun i ↦ (a i).property)⟩
    refine ⟨cc P c, ?_⟩
    funext i
    exact (hmap i c (a i) rfl).trans (ha i)

end AtiyahSinger
