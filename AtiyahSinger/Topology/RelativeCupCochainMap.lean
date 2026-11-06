/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyCup
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Right multiplication by a relative cocycle

Public module ID: M2076.

The original ordinary-relative cup product with a fixed relative cocycle is
a morphism from the degree-extended ordinary cochains to the original relative
cochains. The source is extended by zero below the cocycle degree. Its differential
has no shift sign, exactly as in the original right-cup Leibniz identity.
No truncation of the relative target or of its incoming boundaries is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Right cup with the specified relative cocycle, on the original cochain complexes. -/
def relativeSingularCochainCupMap (A : Set X) (r : ℕ)
    (U : relativeSingularCocycles R A r) :
    (singularCochains R X).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶
      relativeSingularCochains R A := by
  let C := singularCochains R X
  let D := relativeSingularCochains R A
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let f (n : ℕ) : (C.extend e).X n ⟶ D.X n :=
    if h : r ≤ n then
      (C.extendXIso e (Nat.sub_add_cancel h)).hom ≫
        ModuleCat.ofHom ((relativeSingularCochainAction R A (n - r) r).flip U.val) ≫
          (D.XIsoOfEq (Nat.sub_add_cancel h)).hom
    else 0
  have hf (p n : ℕ) (hn : p + r = n) : f n =
      (C.extendXIso e hn).hom ≫
        ModuleCat.ofHom ((relativeSingularCochainAction R A p r).flip U.val) ≫
          (D.XIsoOfEq hn).hom := by
    subst n
    dsimp only [f]
    rw [dite_eq_left (Nat.le_add_left r p)]
    have htransport (k : ℕ) (hk : k = p) (h : k + r = p + r) :
        (C.extendXIso e h).hom ≫
            ModuleCat.ofHom ((relativeSingularCochainAction R A k r).flip U.val) ≫
              (D.XIsoOfEq h).hom =
          (C.extendXIso e (i := p) rfl).hom ≫
            ModuleCat.ofHom ((relativeSingularCochainAction R A p r).flip U.val) ≫
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
    -- The sole nonzero component identity is the actual relative Leibniz formula.
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
    change D.d (p + r) (p + r + 1) (relativeSingularCochainAction R A p r a U.val) =
      (D.XIsoOfEq heq.symm).hom
        (relativeSingularCochainAction R A (p + 1) r (C.d p (p + 1) a) U.val)
    have h := relativeSingularCochainAction_leibniz R A p r a U.val
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
theorem relativeSingularCochainCupMap_f (A : Set X) (r : ℕ)
    (U : relativeSingularCocycles R A r) (p : ℕ) :
    (relativeSingularCochainCupMap R A r U).f (p + r) =
      ((singularCochains R X).extendXIso (ComplexShape.embeddingUp'Add (1 : ℕ) r)
        (i := p) rfl).hom ≫
          ModuleCat.ofHom ((relativeSingularCochainAction R A p r).flip U.val) := by
  let C := singularCochains R X
  let D := relativeSingularCochains R A
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  change (if h : r ≤ p + r then
    (C.extendXIso e (Nat.sub_add_cancel h)).hom ≫
      ModuleCat.ofHom ((relativeSingularCochainAction R A (p + r - r) r).flip U.val) ≫
        (D.XIsoOfEq (Nat.sub_add_cancel h)).hom else 0) = _
  rw [dite_eq_left (Nat.le_add_left r p)]
  have htransport (k : ℕ) (hk : k = p) (h : k + r = p + r) :
      (C.extendXIso e h).hom ≫
          ModuleCat.ofHom ((relativeSingularCochainAction R A k r).flip U.val) ≫
            (D.XIsoOfEq h).hom =
        (C.extendXIso e (i := p) rfl).hom ≫
          ModuleCat.ofHom ((relativeSingularCochainAction R A p r).flip U.val) := by
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
/-- The induced homology map is the original relative cohomology action. -/
theorem homologyMap_relativeSingularCochainCupMap (A : Set X) (r : ℕ)
    (U : relativeSingularCocycles R A r) (p : ℕ) (a : singularCohomology R X p) :
    HomologicalComplex.homologyMap (relativeSingularCochainCupMap R A r U) (p + r)
        (((singularCochains R X).extendHomologyIso
          (ComplexShape.embeddingUp'Add (1 : ℕ) r) (j := p) rfl).inv a) =
      relativeSingularCohomologyAction R A p r a (relativeSingularCocycleClass R A r U) := by
  let C := singularCochains R X
  let D := relativeSingularCochains R A
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let F := relativeSingularCochainCupMap R A r U
  -- Choose an original cocycle, retaining its canonical cycle and quotient comparisons.
  obtain ⟨α, hα⟩ := (C.sc p).moduleCatToCycles.range.mkQ_surjective
    ((C.sc p).moduleCatHomologyIso.hom a)
  have ha : singularCocycleClass R X p α = a := by
    change (C.sc p).moduleCatHomologyIso.inv ((C.sc p).moduleCatToCycles.range.mkQ α) = a
    rw [hα]
    exact congrArg (fun g ↦ g a) (C.sc p).moduleCatHomologyIso.hom_inv_id
  let α' := (C.sc p).moduleCatCyclesIso.inv α
  let αe := (C.extendCyclesIso e (j := p) rfl).inv α'
  let β := relativeSingularCocycleAction R A p r α U
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
    rw [relativeSingularCochainCupMap_f]
    change relativeSingularCochainAction R A p r
      ((C.extendXIso e (i := p) rfl).hom
        ((C.extendXIso e (i := p) rfl).inv α.val)) U.val = β.val
    rw [Iso.inv_hom_id_apply]
    rfl
  have hαπ : C.homologyπ p α' = singularCocycleClass R X p α :=
    congrArg (fun g ↦ g α) (C.sc p).moduleCatCyclesIso_inv_π
  have hβπ : D.homologyπ (p + r) β' = relativeSingularCocycleClass R A (p + r) β :=
    congrArg (fun g ↦ g β) (D.sc (p + r)).moduleCatCyclesIso_inv_π
  have heπ : (C.extendHomologyIso e (j := p) rfl).inv (C.homologyπ p α') =
      (C.extend e).homologyπ (p + r) αe :=
    congrArg (fun g ↦ g α') (C.homologyπ_extendHomologyIso_inv e (j := p) rfl)
  have hmap := congrArg (fun g ↦ g αe) (HomologicalComplex.homologyπ_naturality F (p + r))
  change HomologicalComplex.homologyMap F (p + r)
      ((C.extend e).homologyπ (p + r) αe) =
    D.homologyπ (p + r) (HomologicalComplex.cyclesMap F (p + r) αe) at hmap
  rw [hcycle, hβπ] at hmap
  rw [← ha, relativeSingularCohomologyAction_cocycleClass]
  change HomologicalComplex.homologyMap F (p + r)
    ((C.extendHomologyIso e (j := p) rfl).inv (singularCocycleClass R X p α)) = _
  rw [← hαπ, heπ]
  exact hmap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the original ordinary-relative cochain action for an actual map of pairs. -/
theorem relativeSingularCochainAction_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) (p q : ℕ)
    (a : (singularCochains R Y).X p) (b : (relativeSingularCochains R B).X q) :
    (((singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op).f
      (p + q)) (relativeSingularCochainAction R B p q a b) =
        relativeSingularCochainAction R A p q
          (((singularCochainsFunctor R).map (TopCat.ofHom f).op).f p a)
          ((((singularCochainDualFunctor R).map
            (relativeSingularChainsMap R f hf).op).f q) b) := by
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
  -- The quotient projection injects relative cochains into ordinary cochains by pullback.
  -- The same simplex map preserves front and back faces, so both evaluations coincide.
  apply (relativeSingularCochainEquiv R A (p + q)).injective
  apply Subtype.ext
  change JX.f (p + q) (F.f (p + q) (relativeSingularCochainAction R B p q a b)) =
    JX.f (p + q) (relativeSingularCochainAction R A p q (P.f p a) (F.f q b))
  have hcomp (n : ℕ) (v : C.X n) : JX.f n (F.f n v) = P.f n (JY.f n v) :=
    congrArg (fun t ↦ t.f n v) hprojection
  rw [hcomp, haction B p q a b, haction A p q (P.f p a) (F.f q b),
    hcup p q a (JY.f q b), hcomp q b]

end AtiyahSinger
