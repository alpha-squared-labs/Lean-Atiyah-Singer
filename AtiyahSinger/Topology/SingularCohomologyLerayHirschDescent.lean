/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainComparisonDescent
public import AtiyahSinger.Algebra.CochainExtensionRows
public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch
public import AtiyahSinger.Topology.SmallRelativeCupCochainMap

/-!
# Open-cover descent for the finite Leray--Hirsch comparison

Public module ID: M2132.

The comparison on finite intersections extends uniquely through the exact
Čech augmentation. Native extension by zero is applied separately to each
specified generator degree, while the entire target cochain complex remains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

private theorem exists_lerayHirschAugmentationMap
    {C₀ C₁ C₂ D₀ D₁ D₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    (a₀ : C₀ ⟶ C₁) (a₁ : C₁ ⟶ C₂) (b₀ : D₀ ⟶ D₁) (b₁ : D₁ ⟶ D₂)
    (ha : a₀ ≫ a₁ = 0)
    (hb : ∀ q, Function.Exact (b₀.f q) (b₁.f q))
    (hm : ∀ q, Function.Injective (b₀.f q))
    (F₁ : C₁ ⟶ D₁) (F₂ : C₂ ⟶ D₂) (hF : F₁ ≫ b₁ = a₁ ≫ F₂) :
    ∃ F₀ : C₀ ⟶ D₀, F₀ ≫ b₀ = a₀ ≫ F₁ := by
  -- Exactness chooses the image of each augmented cochain; injectivity makes
  -- that image unique, and hence linear and compatible with the differential.
  have hpre (q : ℕ) (x : C₀.X q) : ∃ y : D₀.X q, b₀.f q y = F₁.f q (a₀.f q x) := by
    apply (hb q _).mp
    have heq : a₀ ≫ F₁ ≫ b₁ = 0 := by
      rw [hF, ← Category.assoc, ha, zero_comp]
    exact congrArg (fun g ↦ g.f q x) heq
  let g (q : ℕ) : C₀.X q →ₗ[R] D₀.X q :=
    { toFun := fun x ↦ (hpre q x).choose
      map_add' := by
        intro x y
        apply hm q
        rw [(hpre q (x + y)).choose_spec]
        simp only [map_add, (hpre q x).choose_spec, (hpre q y).choose_spec]
      map_smul' := by
        intro t x
        apply hm q
        rw [(hpre q (t • x)).choose_spec]
        simp only [map_smul, RingHom.id_apply, (hpre q x).choose_spec] }
  have hg (q : ℕ) (x : C₀.X q) : b₀.f q (g q x) = F₁.f q (a₀.f q x) :=
    (hpre q x).choose_spec
  let F₀ : C₀ ⟶ D₀ :=
    { f q := ModuleCat.ofHom (g q)
      comm' i j _ := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply hm j
        change b₀.f j (D₀.d i j (g i x)) = b₀.f j (g j (C₀.d i j x))
        rw [hg]
        calc
          _ = D₁.d i j (b₀.f i (g i x)) :=
            (congrArg (fun f ↦ f (g i x)) (b₀.comm i j)).symm
          _ = D₁.d i j (F₁.f i (a₀.f i x)) := congrArg (D₁.d i j) (hg i x)
          _ = F₁.f j (C₁.d i j (a₀.f i x)) :=
            congrArg (fun f ↦ f (a₀.f i x)) (F₁.comm i j)
          _ = F₁.f j (a₀.f j (C₀.d i j x)) :=
            congrArg (F₁.f j) (congrArg (fun f ↦ f x) (a₀.comm i j)) }
  refine ⟨F₀, ?_⟩
  ext q x
  exact hg q x

private abbrev lerayHirschSource {ι : Type u} (d : ι → ℕ)
    (C : CochainComplex (ModuleCat.{u} R) ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  cochainFamilyProduct R (fun i ↦ C.extend (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)))

private def lerayHirschSourceMap {ι : Type u} (d : ι → ℕ)
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) :
    lerayHirschSource R d C ⟶ lerayHirschSource R d D :=
  cochainFamilyProductMap R id (fun i ↦
    extendMap f (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)))

private theorem lerayHirschSourceMap_comp {ι : Type u} (d : ι → ℕ)
    {C D E : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) (g : D ⟶ E) :
    lerayHirschSourceMap R d f ≫ lerayHirschSourceMap R d g =
      lerayHirschSourceMap R d (f ≫ g) := by
  ext q x
  funext i
  exact congrArg (fun F ↦ F.f q (x i))
    (extendMap_comp f g (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))).symm

private theorem exact_lerayHirschSourceMap {ι : Type u} (d : ι → ℕ)
    {C D E : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) (g : D ⟶ E)
    (h : ∀ q, Function.Exact (f.f q) (g.f q)) (n : ℕ) :
    Function.Exact ((lerayHirschSourceMap R d f).f n)
      ((lerayHirschSourceMap R d g).f n) := by
  intro x
  constructor
  · intro hx
    have hi (i : ι) : ∃ y,
        (extendMap f (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))).f n y = x i :=
      (exact_extendMap_f R f g (d i) h n (x i)).mp (congrFun hx i)
    choose y hy using hi
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩
    funext i
    exact (exact_extendMap_f R f g (d i) h n _).mpr ⟨y i, rfl⟩

private theorem injective_lerayHirschSourceMap {ι : Type u} (d : ι → ℕ)
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D)
    (h : ∀ q, Function.Injective (f.f q)) (n : ℕ) :
    Function.Injective ((lerayHirschSourceMap R d f).f n) := by
  intro x y hxy
  funext i
  exact injective_extendMap_f R f (d i) h n (congrFun hxy i)

private theorem bijective_homologyMap_productMap {ι : Type u}
    {C D : ι → CochainComplex (ModuleCat.{u} R) ℕ} (f : ∀ i, C i ⟶ D i)
    (hf : ∀ i n, Function.Bijective (homologyMap (f i) n)) (n : ℕ) :
    Function.Bijective (homologyMap (cochainFamilyProductMap R id f) n) := by
  let S (x : (cochainFamilyProduct R C).homology n) :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R C i) n x
  let T (x : (cochainFamilyProduct R D).homology n) :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R D i) n x
  have hS : Function.Bijective S :=
    bijective_homologyMap_cochainFamilyProductProjection R C n
  have hT : Function.Bijective T :=
    bijective_homologyMap_cochainFamilyProductProjection R D n
  have hmap : T ∘ homologyMap (cochainFamilyProductMap R id f) n =
      (Pi.map (fun i ↦ homologyMap (f i) n)) ∘ S := by
    funext x i
    have h : cochainFamilyProductMap R id f ≫ cochainFamilyProductProjection R D i =
        cochainFamilyProductProjection R C i ≫ f i := rfl
    have hh := congrArg (fun g : cochainFamilyProduct R C ⟶ D i ↦
      homologyMap g n x) h
    dsimp only [S, T, Function.comp_def, Pi.map]
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using hh
  apply (hT.of_comp_iff' _).mp
  rw [hmap]
  exact (Function.Bijective.piMap (fun i ↦ hf i n)).comp hS

private theorem bijective_homologyMap_extendMap
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D)
    (hf : ∀ n, Function.Bijective (homologyMap f n)) (r n : ℕ) :
    Function.Bijective (homologyMap
      (extendMap f (ComplexShape.embeddingUp'Add (1 : ℕ) r)) n) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    have : IsIso (homologyMap f p) := (ConcreteCategory.isIso_iff_bijective _).mpr (hf p)
    have : QuasiIsoAt f p := (quasiIsoAt_iff_isIso_homologyMap f p).mpr inferInstance
    have : QuasiIsoAt (extendMap f e) (p + r) :=
      (quasiIsoAt_extendMap_iff f e (j := p) (hj' := rfl)).mpr inferInstance
    exact ConcreteCategory.bijective_of_isIso (homologyMap (extendMap f e) (p + r))
  · have hz (K : CochainComplex (ModuleCat.{u} R) ℕ) :
        Subsingleton ((K.extend e).homology n) := by
      apply ModuleCat.isZero_iff_subsingleton.mp
      apply (exactAt_iff_isZero_homology _ _).mp
      exact K.extend_exactAt e n (by
        intro p hp
        change p + r = n at hp
        omega)
    let := hz C
    let := hz D
    change Function.Bijective (homologyMap (extendMap f e) n)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem bijective_homologyMap_extendProductProjections {κ : Type u}
    (C : κ → CochainComplex (ModuleCat.{u} R) ℕ) (r n : ℕ) :
    Function.Bijective (fun z : ((cochainFamilyProduct R C).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) r)).homology n ↦ fun a ↦
      homologyMap (extendMap (cochainFamilyProductProjection R C a)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r)) n z) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let S (z : ((cochainFamilyProduct R C).extend e).homology n) :=
    fun i ↦ homologyMap (extendMap (cochainFamilyProductProjection R C i) e) n z
  change Function.Bijective S
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
    have (i : κ) := hzero (C i)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem bijective_homologyMap_lerayHirschProjections {ι κ : Type u}
    (d : ι → ℕ) (C : κ → CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Bijective (fun z : (lerayHirschSource R d (cochainFamilyProduct R C)).homology n ↦
      fun a ↦ homologyMap (lerayHirschSourceMap R d
        (cochainFamilyProductProjection R C a)) n z) := by
  let S (z : (lerayHirschSource R d (cochainFamilyProduct R C)).homology n) :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R _ i) n z
  let T (z : ∀ a, (lerayHirschSource R d (C a)).homology n) :=
    fun a i ↦ homologyMap (cochainFamilyProductProjection R _ i) n (z a)
  let K (z : ∀ i, ((cochainFamilyProduct R C).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))).homology n) :=
    fun a i ↦ homologyMap (extendMap (cochainFamilyProductProjection R C a)
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))) n (z i)
  have hS : Function.Bijective S :=
    bijective_homologyMap_cochainFamilyProductProjection R _ n
  have hT : Function.Bijective T := Function.Bijective.piMap (fun a ↦
    bijective_homologyMap_cochainFamilyProductProjection R _ n)
  have hK : Function.Bijective K := by
    constructor
    · intro x y hxy
      funext i
      apply (bijective_homologyMap_extendProductProjections R C (d i) n).injective
      exact funext (fun a ↦ congrFun (congrFun hxy a) i)
    · intro y
      have hi (i : ι) :=
        (bijective_homologyMap_extendProductProjections R C (d i) n).surjective
          (fun a ↦ y a i)
      choose x hx using hi
      exact ⟨x, funext (fun a ↦ funext (fun i ↦ congrFun (hx i) a))⟩
  let F (z : (lerayHirschSource R d (cochainFamilyProduct R C)).homology n) :=
    fun a ↦ homologyMap (lerayHirschSourceMap R d
      (cochainFamilyProductProjection R C a)) n z
  have heq : T ∘ F = K ∘ S := by
    funext z a i
    have h : lerayHirschSourceMap R d (cochainFamilyProductProjection R C a) ≫
        cochainFamilyProductProjection R (fun j ↦ (C a).extend
          (ComplexShape.embeddingUp'Add (1 : ℕ) (d j))) i =
      cochainFamilyProductProjection R (fun j ↦ (cochainFamilyProduct R C).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d j))) i ≫
          extendMap (cochainFamilyProductProjection R C a)
            (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) := rfl
    have hh := congrArg (fun g : lerayHirschSource R d (cochainFamilyProduct R C) ⟶
      (C a).extend (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ↦ homologyMap g n z) h
    dsimp only [T, F, K, S, Function.comp_def]
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using hh
  apply (hT.of_comp_iff' F).mp
  rw [heq]
  exact hK.comp hS

private def lerayHirschProductMap {ι κ : Type u} (d : ι → ℕ)
    (C D : κ → CochainComplex (ModuleCat.{u} R) ℕ)
    (F : ∀ a, lerayHirschSource R d (C a) ⟶ D a) :
    lerayHirschSource R d (cochainFamilyProduct R C) ⟶ cochainFamilyProduct R D where
  f q := ModuleCat.ofHom
    { toFun := fun x a ↦ ((lerayHirschSourceMap R d
        (cochainFamilyProductProjection R C a)) ≫ F a).f q x
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    exact congrArg (fun f ↦ f x) ((lerayHirschSourceMap R d
      (cochainFamilyProductProjection R C a) ≫ F a).comm p q)

private theorem lerayHirschProductMap_projection {ι κ : Type u} (d : ι → ℕ)
    (C D : κ → CochainComplex (ModuleCat.{u} R) ℕ)
    (F : ∀ a, lerayHirschSource R d (C a) ⟶ D a) (a : κ) :
    lerayHirschProductMap R d C D F ≫ cochainFamilyProductProjection R D a =
      lerayHirschSourceMap R d (cochainFamilyProductProjection R C a) ≫ F a := by
  ext q x
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem bijective_homologyMap_lerayHirschProductMap {ι κ : Type u} (d : ι → ℕ)
    (C D : κ → CochainComplex (ModuleCat.{u} R) ℕ)
    (F : ∀ a, lerayHirschSource R d (C a) ⟶ D a)
    (hF : ∀ a n, Function.Bijective (homologyMap (F a) n)) (n : ℕ) :
    Function.Bijective (homologyMap (lerayHirschProductMap R d C D F) n) := by
  let S (x : (lerayHirschSource R d (cochainFamilyProduct R C)).homology n) :=
    fun a ↦ homologyMap (lerayHirschSourceMap R d
      (cochainFamilyProductProjection R C a)) n x
  let T (x : (cochainFamilyProduct R D).homology n) :=
    fun a ↦ homologyMap (cochainFamilyProductProjection R D a) n x
  have hS : Function.Bijective S := bijective_homologyMap_lerayHirschProjections R d C n
  have hT : Function.Bijective T :=
    bijective_homologyMap_cochainFamilyProductProjection R D n
  have heq : T ∘ homologyMap (lerayHirschProductMap R d C D F) n =
      (Pi.map (fun a ↦ homologyMap (F a) n)) ∘ S := by
    funext x a
    have h := congrArg (fun g : lerayHirschSource R d (cochainFamilyProduct R C) ⟶ D a ↦
      homologyMap g n x) (lerayHirschProductMap_projection R d C D F a)
    dsimp only [S, T, Function.comp_def, Pi.map]
    simpa only [homologyMap_comp, ModuleCat.comp_apply] using h
  apply (hT.of_comp_iff' _).mp
  rw [heq]
  exact (Function.Bijective.piMap (fun a ↦ hF a n)).comp hS

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def lerayHirschSourceFunctor {ι : Type u} (d : ι → ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj C := lerayHirschSource R d C
  map f := lerayHirschSourceMap R d f
  map_id C := by
    ext q x
    funext i
    change (extendMap (𝟙 C) (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))).f q (x i) = x i
    rw [extendMap_id]
    rfl
  map_comp f g := (lerayHirschSourceMap_comp R d f g).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private instance instAdditiveLerayHirschSourceFunctor {ι : Type u} (d : ι → ℕ) :
    (lerayHirschSourceFunctor R d).Additive where
  map_add {C D} f g := by
    ext q x
    funext i
    change (extendMap (f + g) (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))).f q (x i) = _
    rw [extendMap_add]
    rfl

private def lerayHirschForget (X : Type u) [TopologicalSpace X] :
    relativeSingularCochains R (∅ : Set X) ⟶ singularCochains R X :=
  (singularCochainDualFunctor R).map (relativeSingularChainsProjection R (∅ : Set X)).op

private instance instIsIsoLerayHirschForget (X : Type u) [TopologicalSpace X] :
    IsIso (lerayHirschForget R X) :=
  isIso_relativeSingularCochainsToOrdinary_empty R X

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private def lerayHirschRelativePullback (f : C(X, Y)) :
    relativeSingularCochains R (∅ : Set Y) ⟶ relativeSingularCochains R (∅ : Set X) :=
  (singularCochainDualFunctor R).map (relativeSingularChainsMap R f
    (show Set.MapsTo f (∅ : Set X) (∅ : Set Y) from fun _ hx ↦ hx.elim)).op

set_option backward.isDefEq.respectTransparency false in
private theorem lerayHirschForget_natural (f : C(X, Y)) :
    lerayHirschRelativePullback R f ≫ lerayHirschForget R X =
      lerayHirschForget R Y ≫ (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
  change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ =
    (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _
  change (singularCochainDualFunctor R).map (relativeSingularChainsMap R f _).op ≫
      (singularCochainDualFunctor R).map (relativeSingularChainsProjection R (∅ : Set X)).op =
    (singularCochainDualFunctor R).map (relativeSingularChainsProjection R (∅ : Set Y)).op ≫
      (singularCochainDualFunctor R).map ((singularChainsFunctor R).map (TopCat.ofHom f)).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 2
  simp [relativeSingularChainsMap, relativeSingularChainsProjection, cokernel.map]

private def lerayHirschRelativeMap {ι : Type u} [Fintype ι] (π : C(Y, X)) (d : ι → ℕ)
    (c : ∀ i, singularCocycles R Y (d i)) :
    lerayHirschSource R d (relativeSingularCochains R (∅ : Set X)) ⟶
      relativeSingularCochains R (∅ : Set Y) :=
  lerayHirschSourceMap R d (lerayHirschForget R X) ≫
    singularCohomologyLerayHirschMap R π d c ≫ inv (lerayHirschForget R Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem lerayHirschRelativeMap_natural {ι : Type u} [Fintype ι]
    {X' Y' : Type u} [TopologicalSpace X'] [TopologicalSpace Y']
    (π : C(Y, X)) (π' : C(Y', X')) (f : C(Y', Y)) (g : C(X', X))
    (hs : π.comp f = g.comp π') (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i)) :
    lerayHirschSourceMap R d (lerayHirschRelativePullback R g) ≫
      lerayHirschRelativeMap R π' d (fun i ↦ singularCocyclePullback R f (d i) (c i)) =
      lerayHirschRelativeMap R π d c ≫ lerayHirschRelativePullback R f := by
  apply (cancel_mono (lerayHirschForget R Y')).mp
  dsimp only [lerayHirschRelativeMap]
  have hf : inv (lerayHirschForget R Y) ≫ lerayHirschRelativePullback R f ≫
      lerayHirschForget R Y' = (singularCochainsFunctor R).map (TopCat.ofHom f).op := by
    rw [lerayHirschForget_natural, IsIso.inv_hom_id_assoc]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hf]
  rw [← Category.assoc, lerayHirschSourceMap_comp, lerayHirschForget_natural,
    ← lerayHirschSourceMap_comp, Category.assoc]
  exact congrArg (fun F ↦ lerayHirschSourceMap R d (lerayHirschForget R X) ≫ F)
    (singularCohomologyLerayHirschMap_natural R π π' f g hs d c)

private theorem lerayHirschRelativeMap_bijective {ι : Type u} [Fintype ι]
    (π : C(Y, X)) (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (h : ∀ n, Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R π d c) n))
    (n : ℕ) : Function.Bijective (homologyMap (lerayHirschRelativeMap R π d c) n) := by
  have hJ : Function.Bijective (homologyMap
      (lerayHirschSourceMap R d (lerayHirschForget R X)) n) :=
    bijective_homologyMap_productMap R _ (fun i q ↦
      bijective_homologyMap_extendMap R (lerayHirschForget R X)
        (fun q ↦ ConcreteCategory.bijective_of_isIso (homologyMap (lerayHirschForget R X) q))
        (d i) q) n
  rw [lerayHirschRelativeMap, homologyMap_comp, homologyMap_comp]
  exact (ConcreteCategory.bijective_of_isIso
    (homologyMap (inv (lerayHirschForget R Y)) n)).comp ((h n).comp hJ)

private theorem lerayHirschCocyclePullback_comp {Z : Type u} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Z, X)) (n : ℕ) (c : singularCocycles R Y n) :
    singularCocyclePullback R g n (singularCocyclePullback R f n c) =
      singularCocyclePullback R (f.comp g) n c := by
  apply Subtype.ext
  have h := (singularCochainsFunctor R).map_comp (TopCat.ofHom f).op (TopCat.ofHom g).op
  exact (congrArg (fun F ↦ F.f n c.val) h).symm

private def lerayHirschLocalMap {ι : Type u} [Fintype ι] (π : C(Y, X))
    (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i)) (V : Set X) :
    lerayHirschSource R d ((relativeSingularCochainsPresheaf R (∅ : Set X)).obj (op V)) ⟶
      (relativeSingularCochainsPresheaf R (∅ : Set Y)).obj (op (π ⁻¹' V)) :=
  lerayHirschRelativeMap R (π.restrictPreimage V) d (fun i ↦
    singularCocyclePullback R (⟨Subtype.val, continuous_subtype_val⟩ : C(π ⁻¹' V, Y))
      (d i) (c i))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem lerayHirschLocalMap_natural {ι : Type u} [Fintype ι] (π : C(Y, X))
    (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i)) (V W : Set X) (h : W ⊆ V) :
    lerayHirschSourceMap R d
      ((relativeSingularCochainsPresheaf R (∅ : Set X)).map (homOfLE h).op) ≫
        lerayHirschLocalMap R π d c W =
      lerayHirschLocalMap R π d c V ≫
        (relativeSingularCochainsPresheaf R (∅ : Set Y)).map
          (homOfLE (show π ⁻¹' W ⊆ π ⁻¹' V from fun _ hy ↦ h hy)).op := by
  let g : C(W, V) := ⟨fun x ↦ ⟨x.val, h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let f : C(π ⁻¹' W, π ⁻¹' V) := ⟨fun y ↦ ⟨y.val, h y.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let j : C(π ⁻¹' V, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hs : (π.restrictPreimage V).comp f = g.comp (π.restrictPreimage W) := rfl
  have hc : (fun i ↦ singularCocyclePullback R f (d i)
      (singularCocyclePullback R j (d i) (c i))) =
    (fun i ↦ singularCocyclePullback R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(π ⁻¹' W, Y)) (d i) (c i)) := by
    funext i
    exact lerayHirschCocyclePullback_comp R j f (d i) (c i)
  have H := lerayHirschRelativeMap_natural R (π.restrictPreimage V)
    (π.restrictPreimage W) f g hs d (fun i ↦ singularCocyclePullback R j (d i) (c i))
  rw [hc] at H
  exact H

private theorem lerayHirschLocalMap_restriction {ι : Type u} [Fintype ι] (π : C(Y, X))
    (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i)) (V : Set X) :
    lerayHirschSourceMap R d (lerayHirschRelativePullback R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))) ≫
        lerayHirschLocalMap R π d c V =
      lerayHirschRelativeMap R π d c ≫ lerayHirschRelativePullback R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(π ⁻¹' V, Y)) := by
  exact lerayHirschRelativeMap_natural R π (π.restrictPreimage V)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(π ⁻¹' V, Y))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) rfl d c

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Apply the same finite pullback-cup comparison on each Čech intersection.
private def lerayHirschCosimplicialMap {ι κ : Type u} [Fintype ι] (π : C(Y, X))
    (U : κ → Set X) (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i)) :
    singularCechCosimplicialCochains R U (∅ : Set X) ⋙ lerayHirschSourceFunctor R d ⟶
      singularCechCosimplicialCochains R (fun a ↦ π ⁻¹' U a) (∅ : Set Y) where
  app n := lerayHirschProductMap R d
    (fun a : Fin (n.len + 1) → κ ↦
      (relativeSingularCochainsPresheaf R (∅ : Set X)).obj (op (singularCechIntersection U a)))
    (fun a : Fin (n.len + 1) → κ ↦
      (relativeSingularCochainsPresheaf R (∅ : Set Y)).obj
        (op (π ⁻¹' singularCechIntersection U a)))
    (fun a ↦ lerayHirschLocalMap R π d c (singularCechIntersection U a))
  naturality {n m} f := by
    let S := singularCechCosimplicialCochains R U (∅ : Set X)
    let T := singularCechCosimplicialCochains R (fun a ↦ π ⁻¹' U a) (∅ : Set Y)
    let C (k : ℕ) := fun a : Fin (k + 1) → κ ↦
      (relativeSingularCochainsPresheaf R (∅ : Set X)).obj (op (singularCechIntersection U a))
    let D (k : ℕ) := fun a : Fin (k + 1) → κ ↦
      (relativeSingularCochainsPresheaf R (∅ : Set Y)).obj
        (op (π ⁻¹' singularCechIntersection U a))
    let F (k : ℕ) := lerayHirschProductMap R d (C k) (D k)
      (fun a ↦ lerayHirschLocalMap R π d c (singularCechIntersection U a))
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
    let gX := (relativeSingularCochainsPresheaf R (∅ : Set X)).map (homOfLE h).op
    let gY := (relativeSingularCochainsPresheaf R (∅ : Set Y)).map
      (homOfLE (show π ⁻¹' W ⊆ π ⁻¹' V from fun _ hy ↦ h hy)).op
    have hX : S.map f ≫ cochainFamilyProductProjection R (C m.len) a =
        cochainFamilyProductProjection R (C n.len) b ≫ gX := rfl
    have hY : T.map f ≫ cochainFamilyProductProjection R (D m.len) a =
        cochainFamilyProductProjection R (D n.len) b ≫ gY := rfl
    have heq : lerayHirschSourceMap R d (S.map f) ≫ F m.len ≫
        cochainFamilyProductProjection R (D m.len) a =
      F n.len ≫ T.map f ≫ cochainFamilyProductProjection R (D m.len) a := by
      rw [show F m.len ≫ cochainFamilyProductProjection R (D m.len) a =
          lerayHirschSourceMap R d (cochainFamilyProductProjection R (C m.len) a) ≫
            lerayHirschLocalMap R π d c W from
              lerayHirschProductMap_projection R d _ _ _ a]
      rw [← Category.assoc, lerayHirschSourceMap_comp, hX,
        ← lerayHirschSourceMap_comp, Category.assoc, lerayHirschLocalMap_natural]
      have hn : F n.len ≫ cochainFamilyProductProjection R (D n.len) b =
          lerayHirschSourceMap R d (cochainFamilyProductProjection R (C n.len) b) ≫
            lerayHirschLocalMap R π d c V :=
        lerayHirschProductMap_projection R d _ _ _ b
      rw [← Category.assoc, ← hn, Category.assoc, hY]
    exact congrArg (fun g ↦ g.f q x) heq

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem lerayHirschCosimplicialMap_comm {ι κ : Type u} [Fintype ι]
    (π : C(Y, X)) (U : κ → Set X) (d : ι → ℕ)
    (c : ∀ i, singularCocycles R Y (d i)) (n : ℕ) :
    (lerayHirschCosimplicialMap R π U d c).app ⦋n⦌ ≫
        singularCechDifferential R (fun a ↦ π ⁻¹' U a) (∅ : Set Y) (n + 1) =
      lerayHirschSourceMap R d (singularCechDifferential R U (∅ : Set X) (n + 1)) ≫
        (lerayHirschCosimplicialMap R π U d c).app ⦋n + 1⦌ := by
  let F := lerayHirschCosimplicialMap R π U d c
  change F.app ⦋n⦌ ≫ AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (singularCechCosimplicialCochains R (fun a ↦ π ⁻¹' U a) (∅ : Set Y)) n =
    (lerayHirschSourceFunctor R d).map
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (singularCechCosimplicialCochains R U (∅ : Set X)) n) ≫ F.app ⦋n + 1⦌
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (F.naturality (SimplexCategory.δ j)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Comparing the full Čech augmentation retains both nested product families.
/-- A finite family of the specified global cocycles gives a Leray--Hirsch
isomorphism whenever the same comparison is an isomorphism on every nonempty
finite tuple intersection of an arbitrary open cover. All cohomological degrees
are tested locally, including degrees below individual generator degrees. -/
theorem homologyMap_singularCohomologyLerayHirschMap_bijective_of_openCover
    {ι κ : Type u} [Fintype ι] (π : C(Y, X)) (U : κ → Set X)
    (hOpen : ∀ a, IsOpen (U a)) (hCover : ⋃ a, U a = Set.univ)
    (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (hlocal : ∀ m (a : Fin (m + 1) → κ) n,
      Function.Bijective (homologyMap
        (singularCohomologyLerayHirschMap R (π.restrictPreimage (singularCechIntersection U a)) d
          (fun i ↦ singularCocyclePullback R
            (⟨Subtype.val, continuous_subtype_val⟩ : C(π ⁻¹' singularCechIntersection U a, Y))
            (d i) (c i))) n)) (n : ℕ) :
    Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R π d c) n) := by
  /- The exact Čech rows first descend the finite comparison to small cochains.
  Their original restriction maps then identify it with the prescribed global
  comparison. The relative-empty rows below are canonically isomorphic to
  ordinary cochains and are used only to reuse the established exact rows. -/
  let V : κ → Set Y := fun a ↦ π ⁻¹' U a
  let S := lerayHirschSourceFunctor R d
  let C := fun i ↦ S.obj (singularCechCochains R U (∅ : Set X) i)
  let D := singularCechCochains R V (∅ : Set Y)
  let δC := fun i ↦ S.map (singularCechDifferential R U (∅ : Set X) i)
  let δD := singularCechDifferential R V (∅ : Set Y)
  let P := lerayHirschCosimplicialMap R π U d c
  have hsqC (i : ℕ) : δC i ≫ δC (i + 1) = 0 := by
    change S.map _ ≫ S.map _ = 0
    rw [← Functor.map_comp, singularCechDifferential_comp, Functor.map_zero]
  have hrowC (i q : ℕ) : Function.Exact ((δC i).f q) ((δC (i + 1)).f q) :=
    exact_lerayHirschSourceMap R d _ _
      (singularCechDifferential_exact R U (∅ : Set X) i) q
  have hmonoC (q : ℕ) : Function.Injective ((δC 0).f q) :=
    injective_lerayHirschSourceMap R d _
      (singularCechAugmentation_injective R U (∅ : Set X)) q
  have hmonoD (q : ℕ) : Function.Injective ((δD 0).f q) :=
    singularCechAugmentation_injective R V (∅ : Set Y) q
  -- Exactness at the first Čech column supplies the unique augmentation map.
  obtain ⟨F₀, hF₀⟩ := exists_lerayHirschAugmentationMap R (δC 0) (δC 1) (δD 0) (δD 1)
    (hsqC 0) (singularCechDifferential_exact R V (∅ : Set Y) 0) hmonoD
    (P.app ⦋0⦌) (P.app ⦋1⦌) (lerayHirschCosimplicialMap_comm R π U d c 0)
  let F (i : ℕ) : C i ⟶ D i :=
    match i with
    | 0 => F₀
    | m + 1 => P.app ⦋m⦌
  have hcomm (i : ℕ) : F i ≫ δD i = δC i ≫ F (i + 1) := by
    cases i with
    | zero => exact hF₀
    | succ m => exact lerayHirschCosimplicialMap_comm R π U d c m
  have hF (i : ℕ) (hi : 1 ≤ i) (q : ℕ) : Function.Bijective (homologyMap (F i) q) := by
    cases i with
    | zero => omega
    | succ m =>
      exact bijective_homologyMap_lerayHirschProductMap R d _ _ _
        (fun a q ↦ lerayHirschRelativeMap_bijective R
          (π.restrictPreimage (singularCechIntersection U a)) d _ (hlocal m a) q) q
  have hsmall : Function.Bijective (homologyMap F₀ n) :=
    homologyMap_bijective_of_exact_rows R C D δC δD hsqC
      (singularCechDifferential_comp R V (∅ : Set Y)) hrowC
      (singularCechDifferential_exact R V (∅ : Set Y)) hmonoC hmonoD F hcomm hF n
  -- Compare the resulting augmentation with the original global map using
  -- its actual restrictions to the same one-member tuple intersections.
  let s₀ := smallRelativeSingularCochainsRestriction R (Set.range U) (∅ : Set X)
  let t := smallRelativeSingularCochainsRestriction R (Set.range V) (∅ : Set Y)
  let s := S.map s₀
  let G := lerayHirschRelativeMap R π d c
  have hsquare : s ≫ F₀ = G ≫ t := by
    have : Mono (δD 0) := HomologicalComplex.mono_of_mono_f _ (fun q ↦
      (ModuleCat.mono_iff_injective _).mpr (hmonoD q))
    apply (cancel_mono (δD 0)).mp
    rw [Category.assoc, hF₀]
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    let W := singularCechIntersection U a
    let prX := cochainFamilyProductProjection R
      (fun b : Fin 1 → κ ↦ (relativeSingularCochainsPresheaf R (∅ : Set X)).obj
        (op (singularCechIntersection U b))) a
    let prY := cochainFamilyProductProjection R
      (fun b : Fin 1 → κ ↦ (relativeSingularCochainsPresheaf R (∅ : Set Y)).obj
        (op (π ⁻¹' singularCechIntersection U b))) a
    have hX : s₀ ≫ singularCechAugmentation R U (∅ : Set X) ≫ prX =
        lerayHirschRelativePullback R (⟨Subtype.val, continuous_subtype_val⟩ : C(W, X)) :=
      smallRelativeSingularCochainsRestriction_cechAugmentation_projection R U (∅ : Set X) a
    have hY : t ≫ singularCechAugmentation R V (∅ : Set Y) ≫ prY =
        lerayHirschRelativePullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(π ⁻¹' W, Y)) :=
      smallRelativeSingularCochainsRestriction_cechAugmentation_projection R V (∅ : Set Y) a
    have hp : P.app ⦋0⦌ ≫ prY = S.map prX ≫ lerayHirschLocalMap R π d c W :=
      lerayHirschProductMap_projection R d _ _ _ a
    have hcomponent : s ≫ δC 0 ≫ P.app ⦋0⦌ ≫ prY = G ≫ t ≫ δD 0 ≫ prY := by
      rw [hp, ← Category.assoc, ← Category.assoc]
      change (S.map s₀ ≫ S.map (singularCechAugmentation R U (∅ : Set X)) ≫ S.map prX) ≫
          lerayHirschLocalMap R π d c W = _
      rw [← Functor.map_comp, ← Functor.map_comp, hX]
      change lerayHirschSourceMap R d _ ≫ lerayHirschLocalMap R π d c W = _
      rw [lerayHirschLocalMap_restriction]
      exact congrArg (fun f ↦ G ≫ f) hY.symm
    exact congrArg (fun f ↦ f.f q x) hcomponent
  -- The two open-cover restrictions compute the original cohomology in every
  -- degree; source extension and products preserve these same isomorphisms.
  have hOpenV (a : κ) : IsOpen (V a) := (hOpen a).preimage π.continuous
  have hCoverV : ⋃ a, V a = Set.univ := by
    change ⋃ a, π ⁻¹' U a = Set.univ
    rw [← Set.preimage_iUnion, hCover, Set.preimage_univ]
  have hsmallX (q : ℕ) : Function.Bijective (homologyMap s₀ q) := by
    have := isIso_homologyMap_smallRelativeSingularCochainsRestriction R (Set.range U)
      (∅ : Set X) (by rintro W ⟨a, rfl⟩; exact hOpen a) (by simpa using hCover) q
    exact ConcreteCategory.bijective_of_isIso (homologyMap s₀ q)
  have hsmallY : Function.Bijective (homologyMap t n) := by
    have := isIso_homologyMap_smallRelativeSingularCochainsRestriction R (Set.range V)
      (∅ : Set Y) (by rintro W ⟨a, rfl⟩; exact hOpenV a) (by simpa using hCoverV) n
    exact ConcreteCategory.bijective_of_isIso (homologyMap t n)
  have hs : Function.Bijective (homologyMap s n) :=
    bijective_homologyMap_productMap R _ (fun i q ↦
      bijective_homologyMap_extendMap R s₀ hsmallX (d i) q) n
  have hG : Function.Bijective (homologyMap G n) := by
    have hh : Function.Bijective (homologyMap (s ≫ F₀) n) := by
      rw [homologyMap_comp]
      exact hsmall.comp hs
    rw [hsquare, homologyMap_comp] at hh
    exact (hsmallY.of_comp_iff' _).mp hh
  have hJ : Function.Bijective (homologyMap
      (lerayHirschSourceMap R d (lerayHirschForget R X)) n) :=
    bijective_homologyMap_productMap R _ (fun i q ↦
      bijective_homologyMap_extendMap R (lerayHirschForget R X)
        (fun q ↦ ConcreteCategory.bijective_of_isIso (homologyMap (lerayHirschForget R X) q))
        (d i) q) n
  change Function.Bijective (homologyMap (lerayHirschRelativeMap R π d c) n) at hG
  rw [lerayHirschRelativeMap, homologyMap_comp, homologyMap_comp] at hG
  exact (Function.Bijective.of_comp_iff _ hJ).mp
    (((ConcreteCategory.bijective_of_isIso
      (homologyMap (inv (lerayHirschForget R Y)) n)).of_comp_iff' _).mp hG)

end AtiyahSinger
