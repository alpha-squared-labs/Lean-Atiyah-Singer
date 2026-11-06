/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainComparisonDescent
public import AtiyahSinger.Algebra.CochainExtensionRows
public import AtiyahSinger.Topology.SmallRelativeCupCochainMap

/-!
# Descent of the original relative right-cup map

Public module ID: M2129.

Local right-cup isomorphisms on every nonempty tuple intersection of an open
cover descend globally when the local relative cohomology also vanishes
below the fixed cocycle degree. The source
Čech row is extended upward by the fixed cocycle degree and is zero below it;
the target is the full original relative Čech row. In particular no incoming
target boundary is discarded at the Thom degree.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

private def cupDescentMapCocycle {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) (c : (C.sc n).moduleCatLeftHomologyData.K) :
    (D.sc n).moduleCatLeftHomologyData.K :=
  ⟨F.f n c.val, by
    change D.dFrom n (F.f n c.val) = 0
    have h := congrArg (fun f ↦ f c.val) (F.comm_from n)
    change D.dFrom n (F.f n c.val) = F.next n (C.dFrom n c.val) at h
    have hc : C.dFrom n c.val = 0 := c.property
    rw [h, hc, map_zero]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem cupDescentMapCocycle_class {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) (c : (C.sc n).moduleCatLeftHomologyData.K) :
    homologyMap F n ((C.sc n).moduleCatHomologyIso.inv
      ((C.sc n).moduleCatToCycles.range.mkQ c)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ
          (cupDescentMapCocycle R F n c)) := by
  let a : C.cycles n := (C.sc n).moduleCatCyclesIso.inv c
  let b : D.cycles n := (D.sc n).moduleCatCyclesIso.inv (cupDescentMapCocycle R F n c)
  have hc : cyclesMap F n a = b := by
    apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have h := congrArg (fun f ↦ f a) (cyclesMap_i F n)
    change D.iCycles n (cyclesMap F n a) = F.f n (C.iCycles n a) at h
    rw [h]
    have ha := congrArg (fun f ↦ f c) (C.sc n).moduleCatCyclesIso_inv_iCycles
    have hb := congrArg (fun f ↦ f (cupDescentMapCocycle R F n c))
      (D.sc n).moduleCatCyclesIso_inv_iCycles
    exact (congrArg (F.f n) ha).trans hb.symm
  have h := congrArg (fun f ↦ f a) (homologyπ_naturality F n)
  change homologyMap F n (C.homologyπ n a) = D.homologyπ n (cyclesMap F n a) at h
  rw [hc] at h
  have ha := congrArg (fun f ↦ f c) (C.sc n).moduleCatCyclesIso_inv_π
  have hb := congrArg (fun f ↦ f (cupDescentMapCocycle R F n c))
    (D.sc n).moduleCatCyclesIso_inv_π
  change C.homologyπ n a = (C.sc n).moduleCatHomologyIso.inv
    ((C.sc n).moduleCatToCycles.range.mkQ c) at ha
  change D.homologyπ n b = (D.sc n).moduleCatHomologyIso.inv
    ((D.sc n).moduleCatToCycles.range.mkQ (cupDescentMapCocycle R F n c)) at hb
  rw [ha, hb] at h
  exact h

variable {X : Type u} [TopologicalSpace X]

private def cupDescentRestriction (A V : Set X) :
    relativeSingularCochains R A ⟶
      relativeSingularCochains R ((Subtype.val : V → X) ⁻¹' A) :=
  (singularCochainDualFunctor R).map (relativeSingularChainsMap R
    (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (fun _ hx ↦ hx)).op

private def cupDescentForget (A : Set X) :
    relativeSingularCochains R A ⟶ singularCochains R X :=
  (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op

set_option backward.isDefEq.respectTransparency false in
private theorem cupDescentForget_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op ≫
        cupDescentForget R A =
      cupDescentForget R B ≫ (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
  change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ =
    (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
  change (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op ≫
      (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op =
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op ≫
      (singularCochainDualFunctor R).map
        ((singularChainsFunctor R).map (TopCat.ofHom f)).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 2
  simp [relativeSingularChainsMap, relativeSingularChainsProjection, cokernel.map]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cupDescentCup_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B)
    (r : ℕ) (c : relativeSingularCocycles R B r) :
    extendMap ((singularCochainsFunctor R).map (TopCat.ofHom f).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
      relativeSingularCochainCupMap R A r
        (cupDescentMapCocycle R ((singularCochainDualFunctor R).map
          (relativeSingularChainsMap R f hf).op) r c) =
      relativeSingularCochainCupMap R B r c ≫
        (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    simp only [HomologicalComplex.comp_f, relativeSingularCochainCupMap_f]
    rw [extendMap_f _ e (i := p) (i' := p + r) rfl]
    change (((singularCochains R Y).extendXIso e (i := p) rfl).hom ≫
      ((singularCochainsFunctor R).map (TopCat.ofHom f).op).f p ≫
      ((singularCochains R X).extendXIso e (i := p) rfl).inv) ≫
        ((singularCochains R X).extendXIso e (i := p) rfl).hom ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    ext a
    exact (relativeSingularCochainAction_natural R f A B hf p r
      (((singularCochains R Y).extendXIso e (i := p) rfl).hom a) c.val).symm
  · have hz := (singularCochains R Y).isZero_extend_X e n (by
      intro p hp
      change p + r = n at hp
      omega)
    exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem cupDescentRestriction_natural (A V W : Set X) (h : W ⊆ V) :
    cupDescentRestriction R A V ≫
      (relativeSingularCochainsPresheaf R A).map (homOfLE h).op =
        cupDescentRestriction R A W := by
  change (singularCochainDualFunctor R).map _ ≫
    (singularCochainDualFunctor R).map _ = _
  rw [← Functor.map_comp, ← op_comp, ← relativeSingularChainsMap_comp]
  rfl

private def cupDescentLocalMap (A V : Set X) (r : ℕ)
    (c : relativeSingularCocycles R A r) :
    ((relativeSingularCochainsPresheaf R (∅ : Set X)).obj (op V)).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶
        (relativeSingularCochainsPresheaf R A).obj (op V) :=
  extendMap (cupDescentForget R ((Subtype.val : V → X) ⁻¹' (∅ : Set X)))
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
    relativeSingularCochainCupMap R ((Subtype.val : V → X) ⁻¹' A) r
      (cupDescentMapCocycle R (cupDescentRestriction R A V) r c)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cupDescentLocalMap_natural (A V W : Set X) (h : W ⊆ V)
    (r : ℕ) (c : relativeSingularCocycles R A r) :
    extendMap ((relativeSingularCochainsPresheaf R (∅ : Set X)).map (homOfLE h).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ cupDescentLocalMap R A W r c =
      cupDescentLocalMap R A V r c ≫
        (relativeSingularCochainsPresheaf R A).map (homOfLE h).op := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let f : C(W, V) := ⟨fun x ↦ ⟨x.val, h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let P := (relativeSingularCochainsPresheaf R A).map (homOfLE h).op
  have hc : cupDescentMapCocycle R P r
      (cupDescentMapCocycle R (cupDescentRestriction R A V) r c) =
      cupDescentMapCocycle R (cupDescentRestriction R A W) r c := by
    apply Subtype.ext
    exact congrArg (fun F ↦ F.f r c.val) (cupDescentRestriction_natural R A V W h)
  have hcup := cupDescentCup_natural R f
    ((Subtype.val : W → X) ⁻¹' A) ((Subtype.val : V → X) ⁻¹' A)
    (fun _ hx ↦ hx) r (cupDescentMapCocycle R (cupDescentRestriction R A V) r c)
  change extendMap ((singularCochainsFunctor R).map (TopCat.ofHom f).op) e ≫
    relativeSingularCochainCupMap R _ r (cupDescentMapCocycle R P r _) = _ at hcup
  rw [hc] at hcup
  have hforget := cupDescentForget_natural R f
    ((Subtype.val : W → X) ⁻¹' (∅ : Set X))
    ((Subtype.val : V → X) ⁻¹' (∅ : Set X)) (fun _ hx ↦ hx)
  change (relativeSingularCochainsPresheaf R (∅ : Set X)).map (homOfLE h).op ≫
    cupDescentForget R _ = _ at hforget
  dsimp only [cupDescentLocalMap]
  rw [← Category.assoc, ← extendMap_comp, hforget, extendMap_comp,
    Category.assoc, hcup, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cupDescentLocalMap_bijective (A V : Set X) (r : ℕ)
    (c : relativeSingularCocycles R A r)
    (hvan : ∀ q, q < r → Subsingleton
      (relativeSingularCohomology R ((Subtype.val : V → X) ⁻¹' A) q))
    (hlocal : ∀ p, Function.Bijective (fun a : singularCohomology R V p ↦
      relativeSingularCohomologyAction R ((Subtype.val : V → X) ⁻¹' A) p r a
        (relativeSingularCohomologyPullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (fun _ hx ↦ hx) r
            (relativeSingularCocycleClass R A r c)))) (n : ℕ) :
    Function.Bijective (homologyMap (cupDescentLocalMap R A V r c) n) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    let cV := cupDescentMapCocycle R (cupDescentRestriction R A V) r c
    let F := relativeSingularCochainCupMap R ((Subtype.val : V → X) ⁻¹' A) r cV
    let J := (singularCochains R V).extendHomologyIso e (j := p) rfl
    have hc : relativeSingularCocycleClass R ((Subtype.val : V → X) ⁻¹' A) r cV =
        relativeSingularCohomologyPullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (fun _ hx ↦ hx) r
            (relativeSingularCocycleClass R A r c) :=
      (cupDescentMapCocycle_class R (cupDescentRestriction R A V) r c).symm
    have hF : Function.Bijective (homologyMap F (p + r)) := by
      apply (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso J.inv)).mp
      have hformula : homologyMap F (p + r) ∘ J.inv = (fun a ↦
          relativeSingularCohomologyAction R ((Subtype.val : V → X) ⁻¹' A) p r a
            (relativeSingularCohomologyPullback R
              (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (fun _ hx ↦ hx) r
                (relativeSingularCocycleClass R A r c))) := by
        funext a
        exact (homologyMap_relativeSingularCochainCupMap R _ r cV p a).trans
          (congrArg (relativeSingularCohomologyAction R _ p r a) hc)
      rw [hformula]
      exact hlocal p
    have : IsIso (cupDescentForget R ((Subtype.val : V → X) ⁻¹' (∅ : Set X))) :=
      isIso_relativeSingularCochainsToOrdinary_empty R V
    have : IsIso (extendMap
        (cupDescentForget R ((Subtype.val : V → X) ⁻¹' (∅ : Set X))) e) :=
      inferInstanceAs (IsIso ((e.extendFunctor (ModuleCat.{u} R)).map _))
    rw [cupDescentLocalMap, homologyMap_comp]
    exact hF.comp (ConcreteCategory.bijective_of_isIso (homologyMap
      (extendMap (cupDescentForget R ((Subtype.val : V → X) ⁻¹' (∅ : Set X))) e) (p + r)))
  · have : Subsingleton
        ((((relativeSingularCochainsPresheaf R (∅ : Set X)).obj (op V)).extend e).homology n) := by
      apply ModuleCat.isZero_iff_subsingleton.mp
      apply (exactAt_iff_isZero_homology _ _).mp
      exact extend_exactAt _ e n (by
        intro p hp
        change p + r = n at hp
        omega)
    have : Subsingleton
        (((relativeSingularCochainsPresheaf R A).obj (op V)).homology n) :=
      hvan n (Nat.lt_of_not_ge hn)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

private def cupDescentProductMap {ι : Type u}
    (C D : ι → CochainComplex (ModuleCat.{u} R) ℕ) (r : ℕ)
    (F : ∀ i, (C i).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶ D i) :
    (cochainFamilyProduct R C).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶
      cochainFamilyProduct R D where
  f n := ModuleCat.ofHom
    { toFun := fun c i ↦ (extendMap (cochainFamilyProductProjection R C i)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ F i).f n c
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext i
    exact congrArg (fun f ↦ f c) ((extendMap (cochainFamilyProductProjection R C i)
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ F i).comm p q)

private theorem cupDescentProductMap_projection {ι : Type u}
    (C D : ι → CochainComplex (ModuleCat.{u} R) ℕ) (r : ℕ)
    (F : ∀ i, (C i).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶ D i) (i : ι) :
    cupDescentProductMap R C D r F ≫ cochainFamilyProductProjection R D i =
      extendMap (cochainFamilyProductProjection R C i)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ F i := by
  ext n c
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cupDescentProductMap_bijective {ι : Type u}
    (C D : ι → CochainComplex (ModuleCat.{u} R) ℕ) (r : ℕ)
    (F : ∀ i, (C i).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶ D i)
    (hF : ∀ i n, Function.Bijective (homologyMap (F i) n)) (n : ℕ) :
    Function.Bijective (homologyMap (cupDescentProductMap R C D r F) n) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let S (z : ((cochainFamilyProduct R C).extend e).homology n) :=
    fun i ↦ homologyMap (extendMap (cochainFamilyProductProjection R C i) e) n z
  have hS : Function.Bijective S := by
    by_cases hn : r ≤ n
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
      let J := (cochainFamilyProduct R C).extendHomologyIso e (j := p) rfl
      let L (z : ∀ i, ((C i).extend e).homology (p + r)) :=
        fun i ↦ ((C i).extendHomologyIso e (j := p) rfl).hom (z i)
      have hL : Function.Bijective L := Function.Bijective.piMap
        (fun i ↦ ConcreteCategory.bijective_of_isIso
          ((C i).extendHomologyIso e (j := p) rfl).hom)
      have hformula : L ∘ S = (fun z ↦ fun i ↦
          homologyMap (cochainFamilyProductProjection R C i) p z) ∘ J.hom := by
        funext z i
        exact congrArg (fun f ↦ f z) (extendHomologyIso_hom_naturality
          (cochainFamilyProductProjection R C i) e (j := p) rfl)
      apply (hL.of_comp_iff' S).mp
      rw [hformula]
      exact (bijective_homologyMap_cochainFamilyProductProjection R C p).comp
        (ConcreteCategory.bijective_of_isIso J.hom)
    · have hzero (K : CochainComplex (ModuleCat.{u} R) ℕ) :
          Subsingleton ((K.extend e).homology n) := by
        apply ModuleCat.isZero_iff_subsingleton.mp
        apply (exactAt_iff_isZero_homology _ _).mp
        exact K.extend_exactAt e n (by
          intro p hp
          change p + r = n at hp
          omega)
      have := hzero (cochainFamilyProduct R C)
      have (i : ι) := hzero (C i)
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  let T (z : (cochainFamilyProduct R D).homology n) :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R D i) n z
  have hT : Function.Bijective T :=
    bijective_homologyMap_cochainFamilyProductProjection R D n
  have hformula : T ∘ homologyMap (cupDescentProductMap R C D r F) n =
      (Pi.map (fun i ↦ homologyMap (F i) n)) ∘ S := by
    funext z i
    have h := congrArg (fun f : (cochainFamilyProduct R C).extend e ⟶ D i ↦
      homologyMap f n z)
      (cupDescentProductMap_projection R C D r F i)
    dsimp only [T, S, Function.comp_def, Pi.map]
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using h
  apply (hT.of_comp_iff' _).mp
  rw [hformula]
  exact (Function.Bijective.piMap (fun i ↦ hF i n)).comp hS

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def cupDescentCosimplicialMap {ι : Type u} (U : ι → Set X) (A : Set X)
    (r : ℕ) (c : relativeSingularCocycles R A r) :
    singularCechCosimplicialCochains R U (∅ : Set X) ⋙
        (ComplexShape.embeddingUp'Add (1 : ℕ) r).extendFunctor (ModuleCat.{u} R) ⟶
      singularCechCosimplicialCochains R U A where
  app n := cupDescentProductMap R
    (fun a : Fin (n.len + 1) → ι ↦
      (relativeSingularCochainsPresheaf R (∅ : Set X)).obj (op (singularCechIntersection U a)))
    (fun a : Fin (n.len + 1) → ι ↦
      (relativeSingularCochainsPresheaf R A).obj (op (singularCechIntersection U a))) r
    (fun a ↦ cupDescentLocalMap R A (singularCechIntersection U a) r c)
  naturality {n m} f := by
    let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
      ComplexShape.embeddingUp'Add (1 : ℕ) r
    let S := singularCechCosimplicialCochains R U (∅ : Set X)
    let T := singularCechCosimplicialCochains R U A
    let C (k : ℕ) (B : Set X) := fun a : Fin (k + 1) → ι ↦
      (relativeSingularCochainsPresheaf R B).obj (op (singularCechIntersection U a))
    let F (k : ℕ) := cupDescentProductMap R (C k ∅) (C k A) r
      (fun a ↦ cupDescentLocalMap R A (singularCechIntersection U a) r c)
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    let b := a ∘ f.toOrderHom
    let V := singularCechIntersection U b
    let W := singularCechIntersection U a
    let h : W ⊆ V := fun _ hx _i ↦ hx _
    have hproj (B : Set X) : (singularCechCosimplicialCochains R U B).map f ≫
        cochainFamilyProductProjection R (C m.len B) a =
      cochainFamilyProductProjection R (C n.len B) b ≫
        (relativeSingularCochainsPresheaf R B).map (homOfLE h).op := by
      ext q x
      rfl
    have heq : extendMap (S.map f) e ≫ F m.len ≫
        cochainFamilyProductProjection R (C m.len A) a =
      F n.len ≫ T.map f ≫ cochainFamilyProductProjection R (C m.len A) a := by
      rw [show F m.len ≫ cochainFamilyProductProjection R (C m.len A) a =
          extendMap (cochainFamilyProductProjection R (C m.len ∅) a) e ≫
            cupDescentLocalMap R A W r c from
              cupDescentProductMap_projection R _ _ r _ a]
      rw [← Category.assoc, ← extendMap_comp, hproj ∅, extendMap_comp, Category.assoc,
        cupDescentLocalMap_natural R A V W h r c]
      have hFn : F n.len ≫ cochainFamilyProductProjection R (C n.len A) b =
          extendMap (cochainFamilyProductProjection R (C n.len ∅) b) e ≫
            cupDescentLocalMap R A V r c :=
        cupDescentProductMap_projection R _ _ r _ b
      rw [← Category.assoc, ← hFn, Category.assoc, hproj A]
    exact congrArg (fun g ↦ g.f q x) heq

private def cupDescentRowMap {ι : Type u} (U : ι → Set X) (A : Set X)
    (r : ℕ) (c : relativeSingularCocycles R A r) (i : ℕ) :
    (singularCechCochains R U (∅ : Set X) i).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶ singularCechCochains R U A i :=
  match i with
  | 0 => smallRelativeSingularCochainCupMap R (Set.range U) A r c
  | n + 1 => (cupDescentCosimplicialMap R U A r c).app ⦋n⦌

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cupDescentLocalMap_restriction (A V : Set X) (r : ℕ)
    (c : relativeSingularCocycles R A r) :
    extendMap (cupDescentRestriction R (∅ : Set X) V)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ cupDescentLocalMap R A V r c =
      extendMap (cupDescentForget R (∅ : Set X))
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ relativeSingularCochainCupMap R A r c ≫
          cupDescentRestriction R A V := by
  let f : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf := cupDescentForget_natural R f
    ((Subtype.val : V → X) ⁻¹' (∅ : Set X)) (∅ : Set X) (fun _ hx ↦ hx)
  change cupDescentRestriction R (∅ : Set X) V ≫ cupDescentForget R _ = _ at hf
  rw [cupDescentLocalMap, ← Category.assoc, ← extendMap_comp, hf,
    extendMap_comp, Category.assoc]
  exact congrArg (fun g ↦ extendMap (cupDescentForget R (∅ : Set X))
    (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ g)
      (cupDescentCup_natural R f ((Subtype.val : V → X) ⁻¹' A) A
        (fun _ hx ↦ hx) r c)

set_option backward.isDefEq.respectTransparency false in
private theorem cupDescentRowMap_comm {ι : Type u} (U : ι → Set X) (A : Set X)
    (r : ℕ) (c : relativeSingularCocycles R A r) (i : ℕ) :
    cupDescentRowMap R U A r c i ≫ singularCechDifferential R U A i =
      extendMap (singularCechDifferential R U (∅ : Set X) i)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ cupDescentRowMap R U A r c (i + 1) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  cases i with
  | succ n =>
    let F := cupDescentCosimplicialMap R U A r c
    change F.app ⦋n⦌ ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (singularCechCosimplicialCochains R U A) n =
      (e.extendFunctor (ModuleCat.{u} R)).map
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD
          (singularCechCosimplicialCochains R U (∅ : Set X)) n) ≫ F.app ⦋n + 1⦌
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum,
      Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (F.naturality (SimplexCategory.δ j)).symm
  | zero =>
    let s := extendMap (smallRelativeSingularCochainsRestriction R (Set.range U)
      (∅ : Set X)) e
    have : Epi (smallRelativeSingularCochainsRestriction R (Set.range U) (∅ : Set X)) :=
      epi_smallRelativeSingularCochainsRestriction_empty R (Set.range U)
    have : Epi s := by
      apply HomologicalComplex.epi_of_epi_f
      intro n
      by_cases hn : r ≤ n
      · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
        dsimp only [s]
        rw [extendMap_f _ e (i := p) (i' := p + r) rfl]
        infer_instance
      · exact ((smallRelativeSingularCochains R (Set.range U) (∅ : Set X)).isZero_extend_X
          e n (by intro p hp; change p + r = n at hp; omega)).epi _
    let C (B : Set X) := fun t : Fin 1 → ι ↦
      (relativeSingularCochainsPresheaf R B).obj (op (singularCechIntersection U t))
    let pr (B : Set X) (a : Fin 1 → ι) :
        singularCechCochains R U B 1 ⟶ C B a :=
      cochainFamilyProductProjection R (C B) a
    have hcomponent (a : Fin 1 → ι) :
        s ≫ smallRelativeSingularCochainCupMap R (Set.range U) A r c ≫
          singularCechAugmentation R U A ≫ pr A a =
        s ≫ extendMap (singularCechAugmentation R U (∅ : Set X)) e ≫
          cupDescentRowMap R U A r c 1 ≫ pr A a := by
      let V := singularCechIntersection U a
      have hproj (B : Set X) : smallRelativeSingularCochainsRestriction R (Set.range U) B ≫
          singularCechAugmentation R U B ≫ pr B a =
            cupDescentRestriction R B V :=
        smallRelativeSingularCochainsRestriction_cechAugmentation_projection R U B a
      have hcup : s ≫ smallRelativeSingularCochainCupMap R (Set.range U) A r c =
          extendMap (cupDescentForget R (∅ : Set X)) e ≫
            relativeSingularCochainCupMap R A r c ≫
              smallRelativeSingularCochainsRestriction R (Set.range U) A :=
        smallRelativeSingularCochainsRestriction_cupMap R (Set.range U) A r c
      have hF : cupDescentRowMap R U A r c 1 ≫
          pr A a =
        extendMap (pr ∅ a) e ≫
          cupDescentLocalMap R A V r c :=
        cupDescentProductMap_projection R _ _ r _ a
      have hleft : s ≫ smallRelativeSingularCochainCupMap R (Set.range U) A r c ≫
          singularCechAugmentation R U A ≫ pr A a =
        extendMap (cupDescentForget R (∅ : Set X)) e ≫
          relativeSingularCochainCupMap R A r c ≫ cupDescentRestriction R A V := by
        have h₁ : CommSq
            (extendMap (cupDescentForget R (∅ : Set X)) e ≫
              relativeSingularCochainCupMap R A r c) s
            (smallRelativeSingularCochainsRestriction R (Set.range U) A)
            (smallRelativeSingularCochainCupMap R (Set.range U) A r c) :=
          ⟨by simpa only [Category.assoc] using hcup.symm⟩
        have h₂ : CommSq (cupDescentRestriction R A V)
            (smallRelativeSingularCochainsRestriction R (Set.range U) A)
            (𝟙 (C A a))
            (singularCechAugmentation R U A ≫ pr A a) :=
          ⟨(Category.comp_id (cupDescentRestriction R A V)).trans (hproj A).symm⟩
        exact (h₁.horiz_comp h₂).w.symm.trans ((Category.comp_id _).trans
          (Category.assoc _ _ _))
      have hres : s ≫ extendMap (singularCechAugmentation R U (∅ : Set X)) e ≫
          extendMap (pr ∅ a) e =
        extendMap (cupDescentRestriction R (∅ : Set X) V) e := by
        have h := congrArg (fun f ↦ extendMap f e) (hproj ∅)
        simpa only [extendMap_comp] using h
      have hright : s ≫ extendMap (singularCechAugmentation R U (∅ : Set X)) e ≫
          cupDescentRowMap R U A r c 1 ≫ pr A a =
        extendMap (cupDescentForget R (∅ : Set X)) e ≫
          relativeSingularCochainCupMap R A r c ≫ cupDescentRestriction R A V := by
        calc
          _ = (s ≫ extendMap (singularCechAugmentation R U (∅ : Set X)) e ≫
                extendMap (pr ∅ a) e) ≫
                  cupDescentLocalMap R A V r c := by
            have h := congrArg (fun f ↦ s ≫
              extendMap (singularCechAugmentation R U (∅ : Set X)) e ≫ f) hF
            simpa only [Category.assoc] using h
          _ = extendMap (cupDescentRestriction R (∅ : Set X) V) e ≫
                cupDescentLocalMap R A V r c := congrArg (fun f ↦ f ≫ _) hres
          _ = _ := cupDescentLocalMap_restriction R A V r c
      exact hleft.trans hright.symm
    apply (cancel_epi s).mp
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    exact congrArg (fun f ↦ f.f q x) (hcomponent a)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Right cup with the specified global relative class is bijective if it is bijective
on every nonempty finite tuple intersection of an open cover and the local relative
cohomology vanishes below its degree. Every restriction is the original pair pullback. -/
theorem relativeSingularCohomologyAction_bijective_of_openCover
    {ι : Type u} (U : ι → Set X) (A : Set X)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ⋃ i, U i = Set.univ)
    (r : ℕ) (c : relativeSingularCocycles R A r)
    (hvan : ∀ m (t : Fin (m + 1) → ι) q, q < r →
      Subsingleton (relativeSingularCohomology R
        ((Subtype.val : singularCechIntersection U t → X) ⁻¹' A) q))
    (hlocal : ∀ m (t : Fin (m + 1) → ι) p,
      Function.Bijective (fun a : singularCohomology R (singularCechIntersection U t) p ↦
        relativeSingularCohomologyAction R
          ((Subtype.val : singularCechIntersection U t → X) ⁻¹' A) p r a
          (relativeSingularCohomologyPullback R
            (⟨Subtype.val, continuous_subtype_val⟩ : C(singularCechIntersection U t, X))
            (fun _ hx ↦ hx) r (relativeSingularCocycleClass R A r c)))) (p : ℕ) :
    Function.Bijective (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R A p r a (relativeSingularCocycleClass R A r c)) := by
  /- Use the original augmented Čech rows. Extending the source upward retains the
  right-cup Leibniz sign convention; the entire relative target remains present.
  The small-chain comparison then identifies the resulting augmentation map with
  the original global cup map, through a square of actual restriction morphisms. -/
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let C := fun i ↦ (singularCechCochains R U (∅ : Set X) i).extend e
  let D := singularCechCochains R U A
  let δC := fun i ↦ extendMap (singularCechDifferential R U (∅ : Set X) i) e
  let δD := singularCechDifferential R U A
  let F := cupDescentRowMap R U A r c
  -- The local assumptions make every positive column a quasi-isomorphism, including
  -- the unsupported low degrees, where both source and target cohomology vanish.
  have hF (i : ℕ) (hi : 1 ≤ i) (n : ℕ) : Function.Bijective (homologyMap (F i) n) := by
    cases i with
    | zero => omega
    | succ m =>
      exact cupDescentProductMap_bijective R
        (fun t : Fin (m + 1) → ι ↦ (relativeSingularCochainsPresheaf R (∅ : Set X)).obj
          (op (singularCechIntersection U t)))
        (fun t : Fin (m + 1) → ι ↦ (relativeSingularCochainsPresheaf R A).obj
          (op (singularCechIntersection U t))) r
        (fun t ↦ cupDescentLocalMap R A (singularCechIntersection U t) r c)
        (fun t q ↦ cupDescentLocalMap_bijective R A (singularCechIntersection U t) r c
          (hvan m t) (hlocal m t) q) n
  have hsmall : Function.Bijective (homologyMap (F 0) (p + r)) := by
    apply homologyMap_bijective_of_exact_rows R C D δC δD (F := F)
    · intro i
      dsimp only [δC]
      rw [← extendMap_comp, singularCechDifferential_comp, extendMap_zero]
    · exact singularCechDifferential_comp R U A
    · intro i q
      exact exact_extendMap_f R _ _ r
        (singularCechDifferential_exact R U (∅ : Set X) i) q
    · exact singularCechDifferential_exact R U A
    · exact injective_extendMap_f R _ r
        (singularCechAugmentation_injective R U (∅ : Set X))
    · exact singularCechAugmentation_injective R U A
    · exact cupDescentRowMap_comm R U A r c
    · exact hF
  -- Small cochains compute the same original relative cohomology for this open cover.
  have hopen : ∀ V ∈ Set.range U, IsOpen V := by
    rintro V ⟨i, rfl⟩
    exact hOpen i
  have hcover : ⋃₀ Set.range U = Set.univ := by simpa using hCover
  let s := smallRelativeSingularCochainsRestriction R (Set.range U) (∅ : Set X)
  let t := smallRelativeSingularCochainsRestriction R (Set.range U) A
  let J := extendMap (cupDescentForget R (∅ : Set X)) e
  let G := relativeSingularCochainCupMap R A r c
  have : IsIso (homologyMap s p) :=
    isIso_homologyMap_smallRelativeSingularCochainsRestriction R (Set.range U)
      (∅ : Set X) hopen hcover p
  have hs : IsIso (homologyMap (extendMap s e) (p + r)) := by
    apply (quasiIsoAt_iff_isIso_homologyMap _ _).mp
    apply (quasiIsoAt_extendMap_iff s e (j := p) (hj' := rfl)).mpr
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr inferInstance
  have : IsIso (homologyMap t (p + r)) :=
    isIso_homologyMap_smallRelativeSingularCochainsRestriction R (Set.range U)
      A hopen hcover (p + r)
  have : IsIso (cupDescentForget R (∅ : Set X)) :=
    isIso_relativeSingularCochainsToOrdinary_empty R X
  have : IsIso J := inferInstanceAs (IsIso ((e.extendFunctor (ModuleCat.{u} R)).map _))
  have hsquare : extendMap s e ≫ F 0 = J ≫ G ≫ t :=
    smallRelativeSingularCochainsRestriction_cupMap R (Set.range U) A r c
  have hcomp : Function.Bijective (homologyMap (J ≫ G ≫ t) (p + r)) := by
    have hleft : Function.Bijective (homologyMap (extendMap s e ≫ F 0) (p + r)) := by
      rw [homologyMap_comp]
      exact hsmall.comp (ConcreteCategory.bijective_of_isIso (homologyMap (extendMap s e) _))
    exact (congrArg (fun f ↦ Function.Bijective (homologyMap f (p + r))) hsquare).mp hleft
  rw [homologyMap_comp, homologyMap_comp] at hcomp
  change Function.Bijective (homologyMap t (p + r) ∘
    (homologyMap G (p + r) ∘ homologyMap J (p + r))) at hcomp
  have hG : Function.Bijective (homologyMap G (p + r)) :=
    (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso (homologyMap J (p + r)))).mp
        (((ConcreteCategory.bijective_of_isIso (homologyMap t (p + r))).of_comp_iff' _).mp
          hcomp)
  -- The cochain map acts on the same original cocycle classes as the ordered cup product.
  let K := (singularCochains R X).extendHomologyIso e (j := p) rfl
  have hformula : homologyMap G (p + r) ∘ K.inv = (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R A p r a (relativeSingularCocycleClass R A r c)) := by
    funext a
    exact homologyMap_relativeSingularCochainCupMap R A r c p a
  exact (congrArg (fun f ↦ Function.Bijective f) hformula).mp
    (hG.comp (ConcreteCategory.bijective_of_isIso K.inv))

end AtiyahSinger
