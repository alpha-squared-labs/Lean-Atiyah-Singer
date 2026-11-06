/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteBundleCategory
public import AtiyahSinger.Topology.FiniteProjectiveModuleCategory
public import AtiyahSinger.Topology.SerreSwanMaps
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# The additive Serre--Swan equivalence on the original bundle and module categories

Public module ID: M2115.

KB01: the actual section functor sends the existing locally finite-rank
bundles to their original modules of continuous sections, and bundle maps
to their already defined action on those sections. The target is the
standard full subcategory of finitely generated projective modules.

The existing homOfSectionMap supplies the inverse on morphisms. Its two
recovery laws give fully faithful data without introducing another Hom
correspondence. The preadditive structure is transported along that same
correspondence; its sum is the unique bundle map acting on sections as
the sum of the original two section maps, hence has their pointwise sum
as its fiber action. The resulting section functor and its quasi-inverse
are additive. The equivalence keeps the original section functor as its
forward functor, including its actual objects and maps.

For X in Type u the original small bundle fibers give section modules in
Type u, so the displayed target is ModuleCat at that same universe. The
existing smallBundleIso handles larger fiber presentations up to actual
bundle isomorphism. No global constant rank, connectedness, smoothness,
CW structure or additional fiber norm is imposed.

Sources: Karoubi, K-Theory, I.6.17--6.18, and the
Serre--Swan object and morphism statements in SerreSwan and SerreSwanMaps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open CategoryTheory

universe u

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]

attribute [local instance] sectionModule

/-- The actual section functor, with the original section modules and fiberwise action on maps. -/
def sectionFunctor : FiniteBundle X ⥤ FiniteProjectiveModuleCat.{u} C(X, ℂ) where
  obj E :=
    { obj := ModuleCat.of C(X, ℂ) (continuousSections E.Fiber)
      property := ⟨finite_continuousSections E.Fiber, projective_continuousSections E.Fiber⟩ }
  map f := ObjectProperty.homMk (ModuleCat.ofHom f.sectionMap)
  map_id E := by
    -- The original section action takes the original identity bundle map to identity.
    apply ObjectProperty.hom_ext
    change ModuleCat.ofHom ((Hom.id E.Fiber).sectionMap) = ModuleCat.ofHom LinearMap.id
    exact congrArg ModuleCat.ofHom (Hom.sectionMap_id (E := E.Fiber))
  map_comp f g := by
    -- The order remains first f on the fiber, then g on that same fiber.
    apply ObjectProperty.hom_ext
    change ModuleCat.ofHom ((g.comp f).sectionMap) =
      ModuleCat.ofHom (g.sectionMap.comp f.sectionMap)
    exact congrArg ModuleCat.ofHom (Hom.sectionMap_comp g f)

/-- Fully faithful data use the already specified recovery of a bundle map from its section map. -/
def sectionFunctorFullyFaithful : (sectionFunctor X).FullyFaithful where
  preimage f := homOfSectionMap f.hom.hom
  map_preimage f := by
    -- Recovering a bundle map preserves the originally supplied module map exactly.
    apply ObjectProperty.hom_ext
    change ModuleCat.ofHom ((homOfSectionMap f.hom.hom).sectionMap) =
      ModuleCat.ofHom f.hom.hom
    exact congrArg ModuleCat.ofHom (homOfSectionMap_sectionMap f.hom.hom)
  preimage_map f := homOfSectionMap_eq f

/-- The additive structure on bundle maps, transported through their actual section maps. -/
instance FiniteBundle.preadditive : Preadditive (FiniteBundle X) :=
  Preadditive.ofFullyFaithful (sectionFunctorFullyFaithful X)

/-- The original section functor preserves the transported addition of actual bundle maps. -/
instance sectionFunctor_additive : (sectionFunctor X).Additive :=
  (sectionFunctorFullyFaithful X).additive_ofFullyFaithful

/-- KA I.6.18: the actual section functor is an equivalence of the stated categories. -/
theorem sectionFunctor_isEquivalence : (sectionFunctor X).IsEquivalence := by
  /- Stage 1: use sectionFunctorFullyFaithful. Its inverse on Hom sets
  is the existing homOfSectionMap of the original linear map, with the
  existing two recovery identities. Thus it preserves every prescribed
  fiber action and does not replace the Hom correspondence by a choice.
  Stage 2: for a target finite projective module P, use its two recorded
  certificates in exists_imageBundle_of_finite_projective. It gives one
  idempotent p and a section-module equivalence for the actual image
  bundle p.fiber, with its induced total-space topology and finite local
  ranks. Package that same family by FiniteBundle.ofFamily. The chosen
  linear equivalence gives a ModuleCat isomorphism and hence an isomorphism
  in the full finite-projective subcategory. This proves essential
  surjectivity with an actual image-bundle witness.
  Stage 3: full faithfulness and essential surjectivity give IsEquivalence.
  The standard asEquivalence construction below selects these essential
  image witnesses and uses the unique recovered morphisms to form its
  inverse, unit and counit. Their naturality and triangle laws follow from
  the same Hom recovery identities. No preferred idempotent presentation
  is asserted; the forward functor is exactly the original section functor.
  Compact Hausdorffness enters through the existing section and image
  theorems, allowing locally varying ranks and empty or disconnected bases. -/
  -- Full faithfulness uses the original section action and its established recovery laws.
  let : (sectionFunctor X).Full := (sectionFunctorFullyFaithful X).full
  let : (sectionFunctor X).Faithful := (sectionFunctorFullyFaithful X).faithful
  let : (sectionFunctor X).EssSurj := by
    constructor
    intro P
    -- Realize this particular target module with one actual idempotent image bundle.
    obtain ⟨p, hp⟩ := exists_imageBundle_of_finite_projective (X := X) P.obj
    let := p.fiberTotalSpaceTopology
    let := p.isFiniteRank_fiber
    obtain ⟨e⟩ := hp
    refine ⟨FiniteBundle.ofFamily (fun x ↦ p.fiber x), ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ e.toModuleIso
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The Serre--Swan equivalence whose forward functor is exactly the original section functor. -/
def serreSwanEquivalence : FiniteBundle X ≌ FiniteProjectiveModuleCat.{u} C(X, ℂ) := by
  letI := sectionFunctor_isEquivalence X
  exact (sectionFunctor X).asEquivalence

/-- The same quasi-inverse is additive for the actual transported bundle-map addition. -/
instance serreSwanEquivalence_inverse_additive : (serreSwanEquivalence X).inverse.Additive := by
  let : (serreSwanEquivalence X).functor.Additive := sectionFunctor_additive X
  exact (serreSwanEquivalence X).inverse_additive

end AtiyahSinger.ComplexBundle
