/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainProduct
public import AtiyahSinger.Topology.SingularCohomologyCup
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The finite cochain comparison for Leray--Hirsch

Public module ID: M2131.

A finite family of specified cocycles gives the sum of the original pullback
followed by right cup. Each source summand is extended upward by its own degree;
the full original target complex, including all incoming boundaries, is retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Right cup with the specified cocycle, on the original cochain complexes. -/
def singularCochainCupMap (r : ℕ)
    (U : singularCocycles R X r) :
    (singularCochains R X).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶
      singularCochains R X := by
  let C := singularCochains R X
  let D := singularCochains R X
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let f (n : ℕ) : (C.extend e).X n ⟶ D.X n :=
    if h : r ≤ n then
      (C.extendXIso e (Nat.sub_add_cancel h)).hom ≫
        ModuleCat.ofHom ((singularCochainCup R X (n - r) r).flip U.val) ≫
          (D.XIsoOfEq (Nat.sub_add_cancel h)).hom
    else 0
  have hf (p n : ℕ) (hn : p + r = n) : f n =
      (C.extendXIso e hn).hom ≫
        ModuleCat.ofHom ((singularCochainCup R X p r).flip U.val) ≫
          (D.XIsoOfEq hn).hom := by
    subst n
    dsimp only [f]
    rw [dite_eq_left (Nat.le_add_left r p)]
    have htransport (k : ℕ) (hk : k = p) (h : k + r = p + r) :
        (C.extendXIso e h).hom ≫
            ModuleCat.ofHom ((singularCochainCup R X k r).flip U.val) ≫
              (D.XIsoOfEq h).hom =
          (C.extendXIso e (i := p) rfl).hom ≫
            ModuleCat.ofHom ((singularCochainCup R X p r).flip U.val) ≫
              (D.XIsoOfEq (p := p + r) rfl).hom := by
      subst k
      rfl
    exact htransport _ (Nat.add_sub_cancel_right p r) _
  refine { f := f, comm' := ?_ }
  intro i j hij
  change f i ≫ D.d i j = (C.extend e).d i j ≫ f j
  have hj : j = i + 1 := hij.symm
  subst j
  by_cases hi : r ≤ i
  · obtain ⟨p, rfl⟩ : ∃ p, i = p + r := ⟨i - r, (Nat.sub_add_cancel hi).symm⟩
    have heq : p + r + 1 = (p + 1) + r := by omega
    -- In every supported degree, the differential square follows from the cup Leibniz formula.
    have hU : D.d r (r + 1) U.val = 0 := by
      have h : D.dFrom r U.val = 0 := U.property
      have h' := congrArg (D.xNextIso
        (show (ComplexShape.up ℕ).Rel r (r + 1) from rfl)).hom h
      rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
      exact h'
    rw [hf p (p + r) rfl]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    rw [C.extend_d_eq e (i := p) (i' := p + r) rfl (j := p + 1) heq.symm]
    rw [hf (p + 1) (p + r + 1) heq.symm]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply (cancel_epi (C.extendXIso e (i := p) rfl).hom).mpr
    ext a
    change D.d (p + r) (p + r + 1) (singularCochainCup R X p r a U.val) =
      (D.XIsoOfEq heq.symm).hom
        (singularCochainCup R X (p + 1) r (C.d p (p + 1) a) U.val)
    have h := singularCochainCup_leibniz R X p r a U.val
    rw [hU] at h
    simpa only [map_zero, smul_zero, add_zero] using h
  · -- Below r the source is zero, so the square commutes without discarding target terms.
    exact (C.isZero_extend_X e i (by
      intro p hp
      change p + r = i at hp
      omega)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In degree p + r the cochain morphism is the specified, ordered cup formula. -/
theorem singularCochainCupMap_f (r : ℕ)
    (U : singularCocycles R X r) (p : ℕ) :
    (singularCochainCupMap R X r U).f (p + r) =
      ((singularCochains R X).extendXIso (ComplexShape.embeddingUp'Add (1 : ℕ) r)
        (i := p) rfl).hom ≫
          ModuleCat.ofHom ((singularCochainCup R X p r).flip U.val) := by
  let C := singularCochains R X
  let D := singularCochains R X
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  change (if h : r ≤ p + r then
    (C.extendXIso e (Nat.sub_add_cancel h)).hom ≫
      ModuleCat.ofHom ((singularCochainCup R X (p + r - r) r).flip U.val) ≫
        (D.XIsoOfEq (Nat.sub_add_cancel h)).hom else 0) = _
  rw [dite_eq_left (Nat.le_add_left r p)]
  have htransport (k : ℕ) (hk : k = p) (h : k + r = p + r) :
      (C.extendXIso e h).hom ≫
          ModuleCat.ofHom ((singularCochainCup R X k r).flip U.val) ≫
            (D.XIsoOfEq h).hom =
        (C.extendXIso e (i := p) rfl).hom ≫
          ModuleCat.ofHom ((singularCochainCup R X p r).flip U.val) := by
    subst k
    simp only [ModuleCat.of_coe, Functor.op_obj, Functor.comp_obj,
      HomologicalComplex.shortComplexFunctor_obj_X₂,
      HomologicalComplex.shortComplexFunctor_obj_X₃,
      HomologicalComplex.shortComplexFunctor_obj_g,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.cancel_iso_hom_left]
    exact Category.comp_id _
  exact htransport _ (Nat.add_sub_cancel_right p r) _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced homology map is the original cohomology cup product. -/
theorem homologyMap_singularCochainCupMap (r : ℕ)
    (U : singularCocycles R X r) (p : ℕ) (a : singularCohomology R X p) :
    HomologicalComplex.homologyMap (singularCochainCupMap R X r U) (p + r)
        (((singularCochains R X).extendHomologyIso
          (ComplexShape.embeddingUp'Add (1 : ℕ) r) (j := p) rfl).inv a) =
      singularCohomologyCup R X p r a (singularCocycleClass R X r U) := by
  let C := singularCochains R X
  let D := singularCochains R X
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let F := singularCochainCupMap R X r U
  -- Choose an original cocycle, retaining its canonical cycle and quotient comparisons.
  obtain ⟨α, hα⟩ := (C.sc p).moduleCatToCycles.range.mkQ_surjective
    ((C.sc p).moduleCatHomologyIso.hom a)
  have ha : singularCocycleClass R X p α = a := by
    change (C.sc p).moduleCatHomologyIso.inv ((C.sc p).moduleCatToCycles.range.mkQ α) = a
    rw [hα]
    exact congrArg (fun g ↦ g a) (C.sc p).moduleCatHomologyIso.hom_inv_id
  let α' := (C.sc p).moduleCatCyclesIso.inv α
  let αe := (C.extendCyclesIso e (j := p) rfl).inv α'
  let β := singularCocycleCup R X p r α U
  let β' := (D.sc (p + r)).moduleCatCyclesIso.inv β
  have hαi : C.iCycles p α' = α.val :=
    congrArg (fun g ↦ g α) (C.sc p).moduleCatCyclesIso_inv_iCycles
  have hβi : D.iCycles (p + r) β' = β.val :=
    congrArg (fun g ↦ g β) (D.sc (p + r)).moduleCatCyclesIso_inv_iCycles
  have hei : (C.extend e).iCycles (p + r) αe =
      (C.extendXIso e (i := p) rfl).inv α.val := by
    have h := congrArg (fun g ↦ g α') (C.extendCyclesIso_inv_iCycles e (j := p) rfl)
    change (C.extend e).iCycles (p + r) αe =
      (C.extendXIso e (i := p) rfl).inv (C.iCycles p α') at h
    rw [hαi] at h
    exact h
  -- On these same cycles the map is exactly multiplication by U, with no extra sign.
  have hcycle : HomologicalComplex.cyclesMap F (p + r) αe = β' := by
    apply (ModuleCat.mono_iff_injective (D.iCycles (p + r))).mp inferInstance
    have h := congrArg (fun g ↦ g αe) (HomologicalComplex.cyclesMap_i F (p + r))
    change D.iCycles (p + r) (HomologicalComplex.cyclesMap F (p + r) αe) =
      F.f (p + r) ((C.extend e).iCycles (p + r) αe) at h
    rw [h, hei, hβi]
    change (F.f (p + r)) ((C.extendXIso e (i := p) rfl).inv α.val) = β.val
    rw [singularCochainCupMap_f]
    change singularCochainCup R X p r
      ((C.extendXIso e (i := p) rfl).hom
        ((C.extendXIso e (i := p) rfl).inv α.val)) U.val = β.val
    rw [Iso.inv_hom_id_apply]
    rfl
  have hαπ : C.homologyπ p α' = singularCocycleClass R X p α :=
    congrArg (fun g ↦ g α) (C.sc p).moduleCatCyclesIso_inv_π
  have hβπ : D.homologyπ (p + r) β' = singularCocycleClass R X (p + r) β :=
    congrArg (fun g ↦ g β) (D.sc (p + r)).moduleCatCyclesIso_inv_π
  have heπ : (C.extendHomologyIso e (j := p) rfl).inv (C.homologyπ p α') =
      (C.extend e).homologyπ (p + r) αe :=
    congrArg (fun g ↦ g α') (C.homologyπ_extendHomologyIso_inv e (j := p) rfl)
  have hmap := congrArg (fun g ↦ g αe) (HomologicalComplex.homologyπ_naturality F (p + r))
  change HomologicalComplex.homologyMap F (p + r)
      ((C.extend e).homologyπ (p + r) αe) =
    D.homologyπ (p + r) (HomologicalComplex.cyclesMap F (p + r) αe) at hmap
  rw [hcycle, hβπ] at hmap
  rw [← ha, singularCohomologyCup_cocycleClass]
  change HomologicalComplex.homologyMap F (p + r)
    ((C.extendHomologyIso e (j := p) rfl).inv (singularCocycleClass R X p α)) = _
  rw [← hαπ, heπ]
  exact hmap

variable {X} {Y : Type u} [TopologicalSpace Y]

private def lerayHirschMapCocycle {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) (c : (C.sc n).moduleCatLeftHomologyData.K) :
    (D.sc n).moduleCatLeftHomologyData.K :=
  ⟨F.f n c.val, by
    change D.dFrom n (F.f n c.val) = 0
    have h := congrArg (fun f ↦ f c.val) (F.comm_from n)
    change D.dFrom n (F.f n c.val) = F.next n (C.dFrom n c.val) at h
    have hc : C.dFrom n c.val = 0 := c.property
    rw [h, hc, map_zero]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem lerayHirschMapCocycle_class {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) (c : (C.sc n).moduleCatLeftHomologyData.K) :
    homologyMap F n ((C.sc n).moduleCatHomologyIso.inv
      ((C.sc n).moduleCatToCycles.range.mkQ c)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ
          (lerayHirschMapCocycle R F n c)) := by
  let a : C.cycles n := (C.sc n).moduleCatCyclesIso.inv c
  let b : D.cycles n := (D.sc n).moduleCatCyclesIso.inv (lerayHirschMapCocycle R F n c)
  have hc : cyclesMap F n a = b := by
    apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have h := congrArg (fun f ↦ f a) (cyclesMap_i F n)
    change D.iCycles n (cyclesMap F n a) = F.f n (C.iCycles n a) at h
    rw [h]
    have ha := congrArg (fun f ↦ f c) (C.sc n).moduleCatCyclesIso_inv_iCycles
    have hb := congrArg (fun f ↦ f (lerayHirschMapCocycle R F n c))
      (D.sc n).moduleCatCyclesIso_inv_iCycles
    exact (congrArg (F.f n) ha).trans hb.symm
  have h := congrArg (fun f ↦ f a) (homologyπ_naturality F n)
  change homologyMap F n (C.homologyπ n a) = D.homologyπ n (cyclesMap F n a) at h
  rw [hc] at h
  have ha := congrArg (fun f ↦ f c) (C.sc n).moduleCatCyclesIso_inv_π
  have hb := congrArg (fun f ↦ f (lerayHirschMapCocycle R F n c))
    (D.sc n).moduleCatCyclesIso_inv_π
  change C.homologyπ n a = (C.sc n).moduleCatHomologyIso.inv
    ((C.sc n).moduleCatToCycles.range.mkQ c) at ha
  change D.homologyπ n b = (D.sc n).moduleCatHomologyIso.inv
    ((D.sc n).moduleCatToCycles.range.mkQ (lerayHirschMapCocycle R F n c)) at hb
  rw [ha, hb] at h
  exact h

/-- Pullback of an original singular cocycle along the specified continuous map. -/
def singularCocyclePullback (f : C(X, Y)) (n : ℕ) (c : singularCocycles R Y n) :
    singularCocycles R X n :=
  let F := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  ⟨F.f n c.val, by
    change (singularCochains R X).dFrom n (F.f n c.val) = 0
    have h := congrArg (fun g ↦ g c.val) (F.comm_from n)
    change (singularCochains R X).dFrom n (F.f n c.val) =
      F.next n ((singularCochains R Y).dFrom n c.val) at h
    have hc : (singularCochains R Y).dFrom n c.val = 0 := c.property
    rw [h, hc, map_zero]⟩

/-- Pullback of the specified cocycle represents the actual cohomology pullback. -/
theorem singularCocycleClass_pullback (f : C(X, Y)) (n : ℕ)
    (c : singularCocycles R Y n) :
    singularCocycleClass R X n (singularCocyclePullback R f n c) =
      singularCohomologyPullback R f n (singularCocycleClass R Y n c) :=
  (lerayHirschMapCocycle_class R ((singularCochainsFunctor R).map
    (TopCat.ofHom f).op) n c).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original cochain cup product is natural for actual singular pullback maps. -/
theorem singularCochainCup_pullback (f : C(X, Y)) (p q : ℕ)
    (a : (singularCochains R Y).X p) (b : (singularCochains R Y).X q) :
    (((singularCochainsFunctor R).map (TopCat.ofHom f).op).f (p + q))
        (singularCochainCup R Y p q a b) =
      singularCochainCup R X p q
        (((singularCochainsFunctor R).map (TopCat.ofHom f).op).f p a)
        (((singularCochainsFunctor R).map (TopCat.ofHom f).op).f q b) := by
  -- The same singular map commutes with both Alexander--Whitney faces.
  let P := (singularCochainsFunctor R).map (TopCat.ofHom f).op
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
  apply (singularCochainEquiv R X (p + q)).injective
  funext σ
  rw [heval]
  change singularCochainEquiv R Y (p + q)
    ((singularCochainEquiv R Y (p + q)).symm _) _ =
      singularCochainEquiv R X (p + q) ((singularCochainEquiv R X (p + q)).symm _) _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  dsimp only
  rw [heval, heval]
  have hfront := congrArg (fun t ↦ t σ) (g.naturality (singularCupFrontFace p q).op)
  have hback := congrArg (fun t ↦ t σ) (g.naturality (singularCupBackFace p q).op)
  exact congrArg₂ (fun u v ↦ singularCochainEquiv R Y p a u *
    singularCochainEquiv R Y q b v) hfront.symm hback.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Right cup by the same pulled-back cocycle commutes with pullback of cochains. -/
theorem singularCochainCupMap_natural (f : C(X, Y)) (r : ℕ)
    (c : singularCocycles R Y r) :
    extendMap ((singularCochainsFunctor R).map (TopCat.ofHom f).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
      singularCochainCupMap R X r (singularCocyclePullback R f r c) =
      singularCochainCupMap R Y r c ≫
        (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    simp only [HomologicalComplex.comp_f, singularCochainCupMap_f]
    rw [extendMap_f _ e (i := p) (i' := p + r) rfl]
    change (((singularCochains R Y).extendXIso e (i := p) rfl).hom ≫
      ((singularCochainsFunctor R).map (TopCat.ofHom f).op).f p ≫
      ((singularCochains R X).extendXIso e (i := p) rfl).inv) ≫
        ((singularCochains R X).extendXIso e (i := p) rfl).hom ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    ext a
    exact (singularCochainCup_pullback R f p r
      (((singularCochains R Y).extendXIso e (i := p) rfl).hom a) c.val).symm
  · exact ((singularCochains R Y).isZero_extend_X e n (by
      intro p hp
      change p + r = n at hp
      omega)).eq_of_src _ _

variable {ι : Type u} [Fintype ι]

/-- The Leray--Hirsch comparison on the original cochains is the finite sum of
pullback followed by right cup with each specified cocycle. -/
def singularCohomologyLerayHirschMap (π : C(Y, X)) (d : ι → ℕ)
    (c : ∀ i, singularCocycles R Y (d i)) :
    cochainFamilyProduct R (fun i ↦ (singularCochains R X).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))) ⟶ singularCochains R Y :=
  ∑ i, cochainFamilyProductProjection R _ i ≫
    HomologicalComplex.extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫ singularCochainCupMap R Y (d i) (c i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In its supported degree, each summand acts by the original pullback and cup product. -/
theorem homologyMap_pullback_singularCochainCupMap (π : C(Y, X)) (r : ℕ)
    (c : singularCocycles R Y r) (p : ℕ) (a : singularCohomology R X p) :
    homologyMap
        (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
          (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ singularCochainCupMap R Y r c) (p + r)
      (((singularCochains R X).extendHomologyIso
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) (j := p) rfl).inv a) =
      singularCohomologyCup R Y p r (singularCohomologyPullback R π p a)
        (singularCocycleClass R Y r c) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let P := (singularCochainsFunctor R).map (TopCat.ofHom π).op
  let JX := (singularCochains R X).extendHomologyIso e (j := p) rfl
  let JY := (singularCochains R Y).extendHomologyIso e (j := p) rfl
  have h : homologyMap (extendMap P e) (p + r) (JX.inv a) =
      JY.inv (singularCohomologyPullback R π p a) := by
    apply (ConcreteCategory.bijective_of_isIso JY.hom).injective
    rw [Iso.inv_hom_id_apply]
    have h := congrArg (fun g ↦ g (JX.inv a))
      (extendHomologyIso_hom_naturality P e (j := p) rfl)
    change JY.hom (homologyMap (extendMap P e) (p + r) (JX.inv a)) =
      homologyMap P p (JX.hom (JX.inv a)) at h
    change JY.hom (homologyMap (extendMap P e) (p + r) (JX.inv a)) =
      homologyMap P p a
    simpa only [Iso.inv_hom_id_apply] using h
  rw [homologyMap_comp]
  change homologyMap (singularCochainCupMap R Y r c) (p + r)
    (homologyMap (extendMap P e) (p + r)
      (((singularCochains R X).extendHomologyIso e (j := p) rfl).inv a)) = _
  rw [h]
  exact homologyMap_singularCochainCupMap R Y r c p _

/-- On cohomology the finite comparison is the sum of its specified pullback-cup
summands, evaluated on the original product projections. Together with the
supported-degree formula this is the usual Leray--Hirsch sum. -/
theorem homologyMap_singularCohomologyLerayHirschMap (π : C(Y, X)) (d : ι → ℕ)
    (c : ∀ i, singularCocycles R Y (d i)) (n : ℕ)
    (a : (cochainFamilyProduct R (fun i ↦ (singularCochains R X).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)))).homology n) :
    homologyMap (singularCohomologyLerayHirschMap R π d c) n a =
      ∑ i, homologyMap
        (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
          (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫
            singularCochainCupMap R Y (d i) (c i)) n
        (homologyMap (cochainFamilyProductProjection R _ i) n a) := by
  classical
  let F (i : ι) := cochainFamilyProductProjection R
    (fun j ↦ (singularCochains R X).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d j))) i ≫
    extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫ singularCochainCupMap R Y (d i) (c i)
  have hsum (s : Finset ι) : homologyMap (∑ i ∈ s, F i) n a =
      ∑ i ∈ s, homologyMap (F i) n a := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
      simp only [Finset.sum_insert hi, homologyMap_add]
      change homologyMap (F i) n a + homologyMap (∑ j ∈ s, F j) n a = _
      rw [hs]
  change homologyMap (∑ i, F i) n a = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun g ↦ g a) (homologyMap_comp
    (cochainFamilyProductProjection R _ i)
    (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫ singularCochainCupMap R Y (d i) (c i)) n)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite comparison is natural for the specified commutative square and
pulls back the same family of cocycles on the total space. -/
theorem singularCohomologyLerayHirschMap_natural
    {X' Y' : Type u} [TopologicalSpace X'] [TopologicalSpace Y']
    (π : C(Y, X)) (π' : C(Y', X')) (f : C(Y', Y)) (g : C(X', X))
    (hs : π.comp f = g.comp π') (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i)) :
    cochainFamilyProductMap R id (fun i ↦
      extendMap ((singularCochainsFunctor R).map (TopCat.ofHom g).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))) ≫
      singularCohomologyLerayHirschMap R π' d
        (fun i ↦ singularCocyclePullback R f (d i) (c i)) =
    singularCohomologyLerayHirschMap R π d c ≫
      (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
  have hs' : TopCat.ofHom π' ≫ TopCat.ofHom g = TopCat.ofHom f ≫ TopCat.ofHom π :=
    congrArg TopCat.ofHom hs.symm
  have hP : (singularCochainsFunctor R).map (TopCat.ofHom g).op ≫
      (singularCochainsFunctor R).map (TopCat.ofHom π').op =
    (singularCochainsFunctor R).map (TopCat.ofHom π).op ≫
      (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hs']
  simp only [singularCohomologyLerayHirschMap, Preadditive.comp_sum,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hpr : cochainFamilyProductMap R id (fun j ↦
        extendMap ((singularCochainsFunctor R).map (TopCat.ofHom g).op)
          (ComplexShape.embeddingUp'Add (1 : ℕ) (d j))) ≫
      cochainFamilyProductProjection R (fun j ↦ (singularCochains R X').extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d j))) i =
    cochainFamilyProductProjection R (fun j ↦ (singularCochains R X).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d j))) i ≫
      extendMap ((singularCochainsFunctor R).map (TopCat.ofHom g).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) := rfl
  rw [← Category.assoc, hpr, Category.assoc, ← Category.assoc
    (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom g).op) _),
    ← extendMap_comp, hP, extendMap_comp, Category.assoc, singularCochainCupMap_natural]
  simp only [Category.assoc]

end AtiyahSinger
