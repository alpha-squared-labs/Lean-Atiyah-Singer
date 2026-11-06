/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import AtiyahSinger.Topology.RelativeCohomologyMayerVietorisBoundary
public import AtiyahSinger.Topology.RelativeCohomologyMayerVietorisBiprod
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Topology.Separation.Regular

/-!
# Mayer–Vietoris for the original compact-support cohomology

Public module ID: M1662.

The maps on an open cover are the existing extension maps at the actual
compact image supports. Their order is difference from the intersection,
then sum into the ambient space. Compact Hausdorff controls admit finite
closed shrinkings inside themselves; the ambient space need not be locally
compact or admit a continuous partition of unity.

Sources: Hatcher, Algebraic Topology, Section 3.3, together with relative
excision and the original diagonal-and-difference cochain sequence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

private def compactSupportMvInclusion (U : Set X) : C(U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def compactSupportMvInterLeft (U V : Set X) : C((U ∩ V : Set X), U) :=
  ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def compactSupportMvInterRight (U V : Set X) : C((U ∩ V : Set X), V) :=
  ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

private theorem compactSupportMvInterLeft_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpenEmbedding (compactSupportMvInterLeft U V) := by
  apply IsOpenEmbedding.of_comp (compactSupportMvInterLeft U V)
    hU.isOpenEmbedding_subtypeVal
  exact (hU.inter hV).isOpenEmbedding_subtypeVal

private theorem compactSupportMvInterRight_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpenEmbedding (compactSupportMvInterRight U V) := by
  apply IsOpenEmbedding.of_comp (compactSupportMvInterRight U V)
    hV.isOpenEmbedding_subtypeVal
  exact (hU.inter hV).isOpenEmbedding_subtypeVal

variable [T2Space X]

/-- The original extensions from the intersection, with the standard difference sign. -/
@[no_expose]
def compactSupportCohomologyMayerVietorisDifference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportCohomology R (U ∩ V : Set X) p ⟶
      ModuleCat.of R (compactSupportCohomology R U p × compactSupportCohomology R V p) :=
  ModuleCat.ofHom
    ((compactSupportCohomologyOpenExtension R (compactSupportMvInterLeft U V)
      (compactSupportMvInterLeft_isOpenEmbedding U V hU hV) p).hom.prod
      (-(compactSupportCohomologyOpenExtension R (compactSupportMvInterRight U V)
        (compactSupportMvInterRight_isOpenEmbedding U V hU hV) p).hom))

/-- Sum of the two original open extensions into the ambient space. -/
@[no_expose]
def compactSupportCohomologyMayerVietorisSum
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    ModuleCat.of R (compactSupportCohomology R U p × compactSupportCohomology R V p) ⟶
      compactSupportCohomology R X p :=
  ModuleCat.ofHom
    ((compactSupportCohomologyOpenExtension R (compactSupportMvInclusion U)
      hU.isOpenEmbedding_subtypeVal p).hom.coprod
      (compactSupportCohomologyOpenExtension R (compactSupportMvInclusion V)
        hV.isOpenEmbedding_subtypeVal p).hom)

/-- The intersection map has the two original inclusion extensions, with a minus on the second. -/
theorem compactSupportCohomologyMayerVietorisDifference_apply
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a : compactSupportCohomology R (U ∩ V : Set X) p) :
    compactSupportCohomologyMayerVietorisDifference R U V hU hV p a =
      (compactSupportCohomologyOpenExtension R
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))
        (IsOpenEmbedding.inclusion Set.inter_subset_left
          ((hU.inter hV).preimage continuous_subtype_val)) p a,
      -(compactSupportCohomologyOpenExtension R
        (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
        (IsOpenEmbedding.inclusion Set.inter_subset_right
          ((hU.inter hV).preimage continuous_subtype_val)) p a)) := by
  rfl

/-- The sum map adds the two specified ambient open extensions. -/
theorem compactSupportCohomologyMayerVietorisSum_apply
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a : compactSupportCohomology R U p) (b : compactSupportCohomology R V p) :
    compactSupportCohomologyMayerVietorisSum R U V hU hV p (a, b) =
      compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal U)
        hU.isOpenEmbedding_subtypeVal p a +
      compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal V)
        hV.isOpenEmbedding_subtypeVal p b := by
  rfl

/-- Every compact control in a two-set open cover is covered by compact controls in its members. -/
theorem exists_compacts_cover_of_isOpen_union_eq_univ
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (K : Compacts X) :
    ∃ (L : Compacts U) (M : Compacts V),
      K ≤ L.map Subtype.val continuous_subtype_val ⊔
        M.map Subtype.val continuous_subtype_val := by
  /- Shrink the finite cover only inside the compact Hausdorff control K.
  Its closed pieces remain compact in the original open subspaces. -/
  let A : Set K := Subtype.val ⁻¹' U
  let B : Set K := Subtype.val ⁻¹' V
  have hA : IsOpen A := hU.preimage continuous_subtype_val
  have hB : IsOpen B := hV.preimage continuous_subtype_val
  have hAB : Aᶜ ⊆ B := by
    intro x hx
    have hmem : x.val ∈ U ∪ V := hcover ▸ Set.mem_univ x.val
    exact hmem.resolve_left hx
  obtain ⟨W, hW, hAW, hWB⟩ := normal_exists_closure_subset hA.isClosed_compl hB hAB
  have hWA : Wᶜ ⊆ A := by
    intro x hx
    by_contra h
    exact hx (hAW h)
  let : CompactSpace (Wᶜ : Set K) := isCompact_iff_compactSpace.mp hW.isClosed_compl.isCompact
  let : CompactSpace (closure W) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let f : C((Wᶜ : Set K), U) := ⟨fun x ↦ ⟨x.val.val, hWA x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let g : C(closure W, V) := ⟨fun x ↦ ⟨x.val.val, hWB x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let L : Compacts U := ⟨Set.range f, isCompact_range f.continuous⟩
  let M : Compacts V := ⟨Set.range g, isCompact_range g.continuous⟩
  refine ⟨L, M, ?_⟩
  intro x hx
  let y : K := ⟨x, hx⟩
  by_cases hy : y ∈ W
  · right
    exact ⟨g ⟨y, subset_closure hy⟩, ⟨⟨y, subset_closure hy⟩, rfl⟩, rfl⟩
  · left
    exact ⟨f ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

private def compactSupportMvUnionFunctor (U V : Set X) :
    Compacts U × Compacts V ⥤ Compacts X where
  obj K := K.1.map Subtype.val continuous_subtype_val ⊔
    K.2.map Subtype.val continuous_subtype_val
  map f := homOfLE (sup_le_sup (Set.image_mono (leOfHom f.1))
    (Set.image_mono (leOfHom f.2)))

private theorem compactSupportMvUnionFunctor_final
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    (compactSupportMvUnionFunctor U V).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro K
    obtain ⟨L, M, hK⟩ := exists_compacts_cover_of_isOpen_union_eq_univ U V hU hV hcover K
    exact ⟨(L, M), ⟨homOfLE hK⟩⟩
  · intro K P f g
    exact ⟨P, 𝟙 _, Subsingleton.elim _ _⟩

private def compactSupportMvIntersection (U V : Set X) (K : Compacts U × Compacts V) :
    Compacts (U ∩ V : Set X) := by
  let P := K.1.map Subtype.val continuous_subtype_val ⊓
    K.2.map Subtype.val continuous_subtype_val
  have hP : (P : Set X) ⊆ Set.range (Subtype.val : (U ∩ V : Set X) → X) := by
    rintro x ⟨⟨u, _, rfl⟩, ⟨v, _, hvu⟩⟩
    exact ⟨⟨u.val, u.property, hvu ▸ v.property⟩, rfl⟩
  exact ⟨Subtype.val ⁻¹' (P : Set X),
    IsInducing.subtypeVal.isCompact_preimage' P.isCompact hP⟩

private def compactSupportMvIntersectionFunctor (U V : Set X) :
    Compacts U × Compacts V ⥤ Compacts (U ∩ V : Set X) where
  obj K := compactSupportMvIntersection U V K
  map {K L} f := homOfLE (by
    intro x hx
    change x.val ∈
      (Subtype.val '' (K.1 : Set U)) ∩ (Subtype.val '' (K.2 : Set V)) at hx
    change x.val ∈ (Subtype.val '' (L.1 : Set U)) ∩ (Subtype.val '' (L.2 : Set V))
    exact ⟨Set.image_mono (leOfHom f.1) hx.1, Set.image_mono (leOfHom f.2) hx.2⟩)

private theorem compactSupportMvIntersectionFunctor_final (U V : Set X) :
    (compactSupportMvIntersectionFunctor U V).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro K
    let L := K.map (compactSupportMvInterLeft U V) (compactSupportMvInterLeft U V).continuous
    let M := K.map (compactSupportMvInterRight U V) (compactSupportMvInterRight U V).continuous
    refine ⟨(L, M), ⟨homOfLE ?_⟩⟩
    intro x hx
    change x.val ∈ (Subtype.val '' (L : Set U)) ∩ (Subtype.val '' (M : Set V))
    exact ⟨⟨compactSupportMvInterLeft U V x, ⟨x, hx, rfl⟩, rfl⟩,
      ⟨compactSupportMvInterRight U V x, ⟨x, hx, rfl⟩, rfl⟩⟩
  · intro K P f g
    exact ⟨P, 𝟙 _, Subsingleton.elim _ _⟩

private def compactSupportMvImageFunctor (U : Set X) : Compacts U ⥤ Compacts X where
  obj K := openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K
  map f := homOfLE (Set.image_mono (leOfHom f))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def compactSupportMvImageCohomologyIso (U : Set X) (hU : IsOpen U) (p : ℕ) :
    compactSupportMvImageFunctor U ⋙ compactSupportCohomologyFunctor R X p ≅
      compactSupportCohomologyFunctor R U p := by
  let q (K : Compacts U) := openEmbeddingCohomologySupportPullback R
    (ContinuousMap.subtypeVal U) hU.isOpenEmbedding_subtypeVal K p
  have (K : Compacts U) : IsIso (q K) :=
    isIso_openEmbeddingCohomologySupportPullback R
      (ContinuousMap.subtypeVal U) hU.isOpenEmbedding_subtypeVal K p
  refine NatIso.ofComponents (fun K ↦ asIso (q K)) ?_
  intro K L f
  change (compactSupportCohomologyFunctor R X p).map
      (homOfLE (Set.image_mono (leOfHom f))) ≫ q L =
    q K ≫ (compactSupportCohomologyFunctor R U p).map f
  exact relativeSingularCohomologyPullback_restriction R (ContinuousMap.subtypeVal U)
    (Set.compl_subset_compl.mpr (leOfHom f))
    (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f))) _ _ p

private def compactSupportMvImageCocone (U : Set X) (hU : IsOpen U) (p : ℕ) :
    Cocone (compactSupportMvImageFunctor U ⋙ compactSupportCohomologyFunctor R X p) :=
  (Cocone.precompose (compactSupportMvImageCohomologyIso R U hU p).hom).obj
    (colimit.cocone (compactSupportCohomologyFunctor R U p))

private def compactSupportMvImageCoconeIsColimit (U : Set X) (hU : IsOpen U) (p : ℕ) :
    IsColimit (compactSupportMvImageCocone R U hU p) :=
  (IsColimit.precomposeHomEquiv (compactSupportMvImageCohomologyIso R U hU p)
    (colimit.cocone (compactSupportCohomologyFunctor R U p))).symm
      (colimit.isColimit (compactSupportCohomologyFunctor R U p))

private def compactSupportMvAmbientIntersectionFunctor (U V : Set X) :
    Compacts U × Compacts V ⥤ Compacts X where
  obj K := K.1.map Subtype.val continuous_subtype_val ⊓
    K.2.map Subtype.val continuous_subtype_val
  map f := homOfLE (Set.inter_subset_inter (Set.image_mono (leOfHom f.1))
    (Set.image_mono (leOfHom f.2)))

private def compactSupportMvIntersectionSupportIso (U V : Set X) :
    compactSupportMvAmbientIntersectionFunctor U V ≅
      compactSupportMvIntersectionFunctor U V ⋙ compactSupportMvImageFunctor (U ∩ V) := by
  refine NatIso.ofComponents (fun K ↦ eqToIso ?_) (fun {_ _} _ ↦ Subsingleton.elim _ _)
  apply Compacts.ext
  ext x
  change x ∈ (Subtype.val '' (K.1 : Set U)) ∩ (Subtype.val '' (K.2 : Set V)) ↔
    x ∈ Subtype.val ''
      (Subtype.val ⁻¹' ((Subtype.val '' (K.1 : Set U)) ∩ (Subtype.val '' (K.2 : Set V))) :
        Set (U ∩ V : Set X))
  constructor
  · intro hx
    obtain ⟨u, _, hu⟩ := hx.1
    obtain ⟨v, _, hv⟩ := hx.2
    exact ⟨⟨x, hu ▸ u.property, hv ▸ v.property⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

private def compactSupportMvIntersectionCohomologyIso
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportMvAmbientIntersectionFunctor U V ⋙ compactSupportCohomologyFunctor R X p ≅
      compactSupportMvIntersectionFunctor U V ⋙
        compactSupportCohomologyFunctor R (U ∩ V : Set X) p :=
  Functor.isoWhiskerRight (compactSupportMvIntersectionSupportIso U V)
      (compactSupportCohomologyFunctor R X p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (compactSupportMvIntersectionFunctor U V)
      (compactSupportMvImageCohomologyIso R (U ∩ V) (hU.inter hV) p)

private def compactSupportMvIntersectionCocone
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    Cocone (compactSupportMvAmbientIntersectionFunctor U V ⋙
      compactSupportCohomologyFunctor R X p) :=
  (Cocone.precompose (compactSupportMvIntersectionCohomologyIso R U V hU hV p).hom).obj
    ((colimit.cocone (compactSupportCohomologyFunctor R (U ∩ V : Set X) p)).whisker
      (compactSupportMvIntersectionFunctor U V))

private def compactSupportMvIntersectionCoconeIsColimit
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    IsColimit (compactSupportMvIntersectionCocone R U V hU hV p) := by
  let := compactSupportMvIntersectionFunctor_final U V
  refine (IsColimit.precomposeHomEquiv
    (compactSupportMvIntersectionCohomologyIso R U V hU hV p) _).symm ?_
  exact (Functor.Final.isColimitWhiskerEquiv (compactSupportMvIntersectionFunctor U V)
    (colimit.cocone (compactSupportCohomologyFunctor R (U ∩ V : Set X) p))).symm
      (colimit.isColimit (compactSupportCohomologyFunctor R (U ∩ V : Set X) p))

private def compactSupportMvUnionCoconeIsColimit
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (p : ℕ) :
    IsColimit ((colimit.cocone (compactSupportCohomologyFunctor R X p)).whisker
      (compactSupportMvUnionFunctor U V)) := by
  let := compactSupportMvUnionFunctor_final U V hU hV hcover
  exact (Functor.Final.isColimitWhiskerEquiv (compactSupportMvUnionFunctor U V)
    (colimit.cocone (compactSupportCohomologyFunctor R X p))).symm
      (colimit.isColimit (compactSupportCohomologyFunctor R X p))

private def compactSupportMvRelativeUnionFunctor (U V : Set X) :
    Compacts U × Compacts V ⥤ (Set X)ᵒᵖ where
  obj K := op (((K.1.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ ∪
    ((K.2.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ)
  map f := (homOfLE (Set.union_subset_union
    (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f.1)))
    (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f.2))))).op

private def compactSupportMvRelativeInterFunctor (U V : Set X) :
    Compacts U × Compacts V ⥤ (Set X)ᵒᵖ where
  obj K := op (((K.1.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ ∩
    ((K.2.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ)
  map f := (homOfLE (Set.inter_subset_inter
    (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f.1)))
    (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f.2))))).op

private def compactSupportMvRelativeUnionIso (U V : Set X) :
    compactSupportMvRelativeUnionFunctor U V ≅
      compactSupportMvAmbientIntersectionFunctor U V ⋙ compactSupportComplementFunctor X := by
  refine NatIso.ofComponents (fun K ↦ eqToIso ?_) (fun {_ _} _ ↦ Subsingleton.elim _ _)
  change op (_ᶜ ∪ _ᶜ) = op ((_ ∩ _)ᶜ)
  rw [Set.compl_inter]

private def compactSupportMvRelativeInterIso (U V : Set X) :
    compactSupportMvRelativeInterFunctor U V ≅
      compactSupportMvUnionFunctor U V ⋙ compactSupportComplementFunctor X := by
  refine NatIso.ofComponents (fun K ↦ eqToIso ?_) (fun {_ _} _ ↦ Subsingleton.elim _ _)
  change op (_ᶜ ∩ _ᶜ) = op ((_ ∪ _)ᶜ)
  rw [Set.compl_union]

private def compactSupportMvLeftCocone
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    Cocone (compactSupportMvRelativeUnionFunctor U V ⋙
      relativeSingularCohomologyFunctor R X p) :=
  (Cocone.precompose (Functor.isoWhiskerRight (compactSupportMvRelativeUnionIso U V)
    (relativeSingularCohomologyFunctor R X p)).hom).obj
      (compactSupportMvIntersectionCocone R U V hU hV p)

private def compactSupportMvLeftCoconeIsColimit
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    IsColimit (compactSupportMvLeftCocone R U V hU hV p) :=
  (IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerRight (compactSupportMvRelativeUnionIso U V)
      (relativeSingularCohomologyFunctor R X p)) _).symm
        (compactSupportMvIntersectionCoconeIsColimit R U V hU hV p)

private def compactSupportMvRightCocone (U V : Set X) (p : ℕ) :
    Cocone (compactSupportMvRelativeInterFunctor U V ⋙
      relativeSingularCohomologyFunctor R X p) :=
  (Cocone.precompose (Functor.isoWhiskerRight (compactSupportMvRelativeInterIso U V)
    (relativeSingularCohomologyFunctor R X p)).hom).obj
      ((colimit.cocone (compactSupportCohomologyFunctor R X p)).whisker
        (compactSupportMvUnionFunctor U V))

private def compactSupportMvRightCoconeIsColimit
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (p : ℕ) :
    IsColimit (compactSupportMvRightCocone R U V p) :=
  (IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerRight (compactSupportMvRelativeInterIso U V)
      (relativeSingularCohomologyFunctor R X p)) _).symm
        (compactSupportMvUnionCoconeIsColimit R U V hU hV hcover p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def compactSupportMvBoundaryNatTrans (U V : Set X) (p : ℕ) :
    compactSupportMvRelativeInterFunctor U V ⋙ relativeSingularCohomologyFunctor R X p ⟶
      compactSupportMvRelativeUnionFunctor U V ⋙
        relativeSingularCohomologyFunctor R X (p + 1) where
  app K := relativeSingularCohomologyMayerVietorisBoundary R _ _
    (K.1.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
    (K.2.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl p
  naturality K L f := by
    exact (relativeSingularCohomologyMayerVietorisBoundary_naturality R (ContinuousMap.id X)
      (L.1.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
      (L.2.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
      (K.1.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
      (K.2.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
      (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f.1)))
      (Set.compl_subset_compl.mpr (Set.image_mono (leOfHom f.2))) p).symm

/-- The compact-support connecting morphism, descended from the original relative sequence. -/
@[no_expose]
def compactSupportCohomologyMayerVietorisBoundary
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (p : ℕ) :
    compactSupportCohomology R X p ⟶ compactSupportCohomology R (U ∩ V : Set X) (p + 1) :=
  (compactSupportMvRightCoconeIsColimit R U V hU hV hcover p).desc
    ((Cocone.precompose (compactSupportMvBoundaryNatTrans R U V p)).obj
      (compactSupportMvLeftCocone R U V hU hV (p + 1)))

private def compactSupportMvBiprodCocone {J : Type u} [Category J]
    (F G : J ⥤ ModuleCat.{u} R) (cF : Cocone F) (cG : Cocone G) :
    Cocone (pointwiseBinaryBicone F G).pt where
  pt := cF.pt ⊞ cG.pt
  ι :=
    { app := fun j ↦ biprod.map (cF.ι.app j) (cG.ι.app j)
      naturality := by
        intro i j f
        change biprod.map (F.map f) (G.map f) ≫
          biprod.map (cF.ι.app j) (cG.ι.app j) = _ ≫ 𝟙 _
        rw [Category.comp_id]
        apply biprod.hom_ext
        · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, cF.w]
          exact (biprod.map_fst _ _).symm
        · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc, cG.w]
          exact (biprod.map_snd _ _).symm }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def compactSupportMvBiprodCoconeIsColimit {J : Type u} [Category J]
    (F G : J ⥤ ModuleCat.{u} R) (cF : Cocone F) (cG : Cocone G)
    (hcF : IsColimit cF) (hcG : IsColimit cG) :
    IsColimit (compactSupportMvBiprodCocone R F G cF cG) where
  desc s := biprod.desc
    (hcF.desc ((Cocone.precompose (pointwiseBinaryBicone F G).inl).obj s))
    (hcG.desc ((Cocone.precompose (pointwiseBinaryBicone F G).inr).obj s))
  fac s j := by
    apply biprod.hom_ext'
    · change biprod.inl ≫ biprod.map (cF.ι.app j) (cG.ι.app j) ≫
        biprod.desc _ _ = _
      rw [biprod.inl_map_assoc, biprod.inl_desc]
      exact hcF.fac _ j
    · change biprod.inr ≫ biprod.map (cF.ι.app j) (cG.ι.app j) ≫
        biprod.desc _ _ = _
      rw [biprod.inr_map_assoc, biprod.inr_desc]
      exact hcG.fac _ j
  uniq s m hm := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc]
      apply hcF.hom_ext
      intro j
      rw [hcF.fac]
      have h := congrArg (fun f ↦ biprod.inl ≫ f) (hm j)
      change biprod.inl ≫ biprod.map (cF.ι.app j) (cG.ι.app j) ≫ m = _ at h
      rw [biprod.inl_map_assoc] at h
      exact h
    · rw [biprod.inr_desc]
      apply hcG.hom_ext
      intro j
      rw [hcG.fac]
      have h := congrArg (fun f ↦ biprod.inr ≫ f) (hm j)
      change biprod.inr ≫ biprod.map (cF.ι.app j) (cG.ι.app j) ≫ m = _ at h
      rw [biprod.inr_map_assoc] at h
      exact h

private def compactSupportMvMiddleFunctor (U V : Set X) (p : ℕ) :
    Compacts U × Compacts V ⥤ ModuleCat.{u} R :=
  (pointwiseBinaryBicone
    (CategoryTheory.Prod.fst (Compacts U) (Compacts V) ⋙ compactSupportMvImageFunctor U ⋙
      compactSupportCohomologyFunctor R X p)
    (CategoryTheory.Prod.snd (Compacts U) (Compacts V) ⋙ compactSupportMvImageFunctor V ⋙
      compactSupportCohomologyFunctor R X p)).pt

private def compactSupportMvMiddleCocone
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    Cocone (compactSupportMvMiddleFunctor R U V p) :=
  compactSupportMvBiprodCocone R _ _
    ((compactSupportMvImageCocone R U hU p).whisker
      (CategoryTheory.Prod.fst (Compacts U) (Compacts V)))
    ((compactSupportMvImageCocone R V hV p).whisker
      (CategoryTheory.Prod.snd (Compacts U) (Compacts V)))

private def compactSupportMvMiddleCoconeIsColimit
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    IsColimit (compactSupportMvMiddleCocone R U V hU hV p) :=
  compactSupportMvBiprodCoconeIsColimit R _ _ _ _
    ((Functor.Final.isColimitWhiskerEquiv
      (CategoryTheory.Prod.fst (Compacts U) (Compacts V)) _).symm
      (compactSupportMvImageCoconeIsColimit R U hU p))
    ((Functor.Final.isColimitWhiskerEquiv
      (CategoryTheory.Prod.snd (Compacts U) (Compacts V)) _).symm
      (compactSupportMvImageCoconeIsColimit R V hV p))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- The diagram comparison unfolds the pointwise biproduct and relative support functors.
private def compactSupportMvDifferenceNatTrans (U V : Set X) (p : ℕ) :
    compactSupportMvRelativeUnionFunctor U V ⋙ relativeSingularCohomologyFunctor R X p ⟶
      compactSupportMvMiddleFunctor R U V p where
  app K := biprod.lift
    (relativeSingularCohomologyRestriction R _ _ Set.subset_union_left p)
    (-(relativeSingularCohomologyRestriction R _ _ Set.subset_union_right p))
  naturality K L f := by
    let H := relativeSingularCohomologyFunctor R X p
    -- State the same two-component square before applying the biproduct projections.
    change H.map _ ≫ biprod.lift (H.map _) (-(H.map _)) =
      biprod.lift (H.map _) (-(H.map _)) ≫ biprod.map (H.map _) (H.map _)
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst,
        ← Category.assoc, biprod.lift_fst]
      rw [← H.map_comp, ← H.map_comp]
      exact congrArg H.map (Subsingleton.elim _ _)
    · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd,
        ← Category.assoc, biprod.lift_snd, Preadditive.comp_neg, Preadditive.neg_comp]
      change -(H.map _ ≫ H.map _) = -(H.map _ ≫ H.map _)
      rw [← H.map_comp, ← H.map_comp]
      exact congrArg (fun f ↦ -(H.map f)) (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def compactSupportMvSumNatTrans (U V : Set X) (p : ℕ) :
    compactSupportMvMiddleFunctor R U V p ⟶
      compactSupportMvRelativeInterFunctor U V ⋙ relativeSingularCohomologyFunctor R X p where
  app K := biprod.desc
    (relativeSingularCohomologyRestriction R _ _ Set.inter_subset_left p)
    (relativeSingularCohomologyRestriction R _ _ Set.inter_subset_right p)
  naturality K L f := by
    let H := relativeSingularCohomologyFunctor R X p
    apply biprod.hom_ext'
    · change biprod.inl ≫ biprod.map (H.map _) (H.map _) ≫
          biprod.desc (H.map _) (H.map _) =
        biprod.inl ≫ biprod.desc (H.map _) (H.map _) ≫ H.map _
      rw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
        ← H.map_comp, ← H.map_comp]
      exact congrArg H.map (Subsingleton.elim _ _)
    · change biprod.inr ≫ biprod.map (H.map _) (H.map _) ≫
          biprod.desc (H.map _) (H.map _) =
        biprod.inr ≫ biprod.desc (H.map _) (H.map _) ≫ H.map _
      rw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
        ← H.map_comp, ← H.map_comp]
      exact congrArg H.map (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMv_exact_at_pair (U V : Set X)
    (K : Compacts U × Compacts V) (p : ℕ) :
    Function.Exact ((compactSupportMvDifferenceNatTrans R U V p).app K)
      ((compactSupportMvSumNatTrans R U V p).app K) ∧
    Function.Exact ((compactSupportMvSumNatTrans R U V p).app K)
      ((compactSupportMvBoundaryNatTrans R U V p).app K) ∧
    Function.Exact ((compactSupportMvBoundaryNatTrans R U V p).app K)
      ((compactSupportMvDifferenceNatTrans R U V (p + 1)).app K) := by
  let A : Set X := ((K.1.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ
  let B : Set X := ((K.2.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ
  have hA : IsOpen A := (K.1.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
  have hB : IsOpen B := (K.2.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
  let S := relativeSingularCochainMayerVietorisSequence R A B
  let e (q : ℕ) := relativeSingularCohomologyMayerVietorisMiddleIso R A B q
  let f (q : ℕ) := (compactSupportMvDifferenceNatTrans R U V q).app K
  let g (q : ℕ) := (compactSupportMvSumNatTrans R U V q).app K
  have hf (q : ℕ) : relativeUnionCohomologyComparison R A B q ≫
      HomologicalComplex.homologyMap S.f q ≫ (e q).hom = f q :=
    relativeSingularCohomologyMayerVietorisMiddleIso_comparison_difference R A B q
  have hg : (e p).hom ≫ g p = HomologicalComplex.homologyMap S.g p :=
    relativeSingularCohomologyMayerVietorisMiddleIso_hom_sum R A B p
  obtain ⟨h₁, h₂, h₃⟩ := exact_relativeSingularCohomologyMayerVietoris R A B hA hB p
  have hf_apply (q : ℕ) (x : relativeSingularCohomology R (A ∪ B) q) :
      (e q).hom (HomologicalComplex.homologyMap S.f q
        (relativeUnionCohomologyComparison R A B q x)) = f q x :=
    congrArg (fun k ↦ k x) (hf q)
  have hg_apply (x : S.X₂.homology p) :
      g p ((e p).hom x) = HomologicalComplex.homologyMap S.g p x :=
    congrArg (fun k ↦ k x) hg
  -- Transport all three positions through the same two-summand comparison.
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e p).hom).surjective y
    rw [hg_apply, h₁ x]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (hf_apply p a).symm.trans (congrArg (e p).hom ha)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (ConcreteCategory.bijective_of_isIso (e p).hom).injective
        ((hf_apply p a).trans ha)⟩
  · intro z
    change relativeSingularCohomology R (A ∩ B) p at z
    change relativeSingularCohomologyMayerVietorisBoundary R A B hA hB p z = 0 ↔
      z ∈ Set.range (g p)
    rw [h₂ z]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(e p).hom x, (hg_apply x).trans hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e p).hom).surjective y
      exact ⟨x, (hg_apply x).symm.trans hy⟩
  · intro y
    change relativeSingularCohomology R (A ∪ B) (p + 1) at y
    constructor
    · intro hy
      apply (h₃ y).mp
      apply (ConcreteCategory.bijective_of_isIso (e (p + 1)).hom).injective
      rw [map_zero, hf_apply]
      exact hy
    · intro hy
      have hz : HomologicalComplex.homologyMap S.f (p + 1)
          (relativeUnionCohomologyComparison R A B (p + 1) y) = 0 := (h₃ y).mpr hy
      exact (hf_apply (p + 1) y).symm.trans
        ((congrArg (e (p + 1)).hom hz).trans (map_zero _))

private theorem compactSupportMv_exact_of_app {J : Type u} [Category J]
    (S : ShortComplex (J ⥤ ModuleCat.{u} R))
    (hS : ∀ j, Function.Exact (S.f.app j) (S.g.app j)) : S.Exact := by
  -- Evaluation preserves homology, and zero of a functor is detected at every object.
  rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext j
  let ev := (evaluation J (ModuleCat.{u} R)).obj j
  have h : (S.map ev).Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (hS j)
  have hz : IsZero (ev.obj S.leftHomologyData.H) :=
    (S.leftHomologyData.exact_map_iff ev).mp h
  exact hz.eq_of_src _ _

private theorem compactSupportMv_colimit_exact {J : Type u} [Category J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    [HasExactColimitsOfShape J (ModuleCat.{u} R)]
    {F G H : J ⥤ ModuleCat.{u} R} (α : F ⟶ G) (β : G ⟶ H)
    (hexact : ∀ j, Function.Exact (α.app j) (β.app j))
    {cF : Cocone F} (hcF : IsColimit cF) {cG : Cocone G} (hcG : IsColimit cG)
    {cH : Cocone H} (hcH : IsColimit cH) (f : cF.pt ⟶ cG.pt) (g : cG.pt ⟶ cH.pt)
    (hf : ∀ j, cF.ι.app j ≫ f = α.app j ≫ cG.ι.app j)
    (hg : ∀ j, cG.ι.app j ≫ g = β.app j ≫ cH.ι.app j) : Function.Exact f g := by
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) := ShortComplex.mk α β (by
    apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hexact j).apply_apply_eq_zero x)
  have hS : S.Exact := compactSupportMv_exact_of_app R S hexact
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (colim.exact_mapShortComplex hS hcF hcG hcH f g hf hg)

private def compactSupportMvAssembledDifference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportCohomology R (U ∩ V : Set X) p ⟶
      compactSupportCohomology R U p ⊞ compactSupportCohomology R V p :=
  (compactSupportMvLeftCoconeIsColimit R U V hU hV p).desc
    ((Cocone.precompose (compactSupportMvDifferenceNatTrans R U V p)).obj
      (compactSupportMvMiddleCocone R U V hU hV p))

private def compactSupportMvAssembledSum
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportCohomology R U p ⊞ compactSupportCohomology R V p ⟶
      compactSupportCohomology R X p :=
  (compactSupportMvMiddleCoconeIsColimit R U V hU hV p).desc
    ((Cocone.precompose (compactSupportMvSumNatTrans R U V p)).obj
      (compactSupportMvRightCocone R U V p))

private theorem compactSupportMv_assembled_exact
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (p : ℕ) :
    Function.Exact (compactSupportMvAssembledDifference R U V hU hV p)
      (compactSupportMvAssembledSum R U V hU hV p) ∧
    Function.Exact (compactSupportMvAssembledSum R U V hU hV p)
      (compactSupportCohomologyMayerVietorisBoundary R U V hU hV hcover p) ∧
    Function.Exact (compactSupportCohomologyMayerVietorisBoundary R U V hU hV hcover p)
      (compactSupportMvAssembledDifference R U V hU hV (p + 1)) := by
  /- All three native positions are exact before colimits. Exact filtered
  colimits preserve them, with the previously identified compact-support
  cocones as the chosen endpoints. -/
  let : HasExactColimitsOfShape (Compacts U × Compacts V) (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.domain_of_functor (Compacts U × Compacts V)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  let hL (q : ℕ) := compactSupportMvLeftCoconeIsColimit R U V hU hV q
  let hM (q : ℕ) := compactSupportMvMiddleCoconeIsColimit R U V hU hV q
  let hT (q : ℕ) := compactSupportMvRightCoconeIsColimit R U V hU hV hcover q
  refine ⟨?_, ?_, ?_⟩
  · exact compactSupportMv_colimit_exact R
      (compactSupportMvDifferenceNatTrans R U V p) (compactSupportMvSumNatTrans R U V p)
      (fun K ↦ (compactSupportMv_exact_at_pair R U V K p).1) (hL p) (hM p) (hT p) _ _
      (fun K ↦ (hL p).fac _ K) (fun K ↦ (hM p).fac _ K)
  · exact compactSupportMv_colimit_exact R
      (compactSupportMvSumNatTrans R U V p) (compactSupportMvBoundaryNatTrans R U V p)
      (fun K ↦ (compactSupportMv_exact_at_pair R U V K p).2.1) (hM p) (hT p) (hL (p + 1)) _ _
      (fun K ↦ (hM p).fac _ K) (fun K ↦ (hT p).fac _ K)
  · exact compactSupportMv_colimit_exact R
      (compactSupportMvBoundaryNatTrans R U V p)
      (compactSupportMvDifferenceNatTrans R U V (p + 1))
      (fun K ↦ (compactSupportMv_exact_at_pair R U V K p).2.2) (hT p) (hL (p + 1))
      (hM (p + 1)) _ _ (fun K ↦ (hT p).fac _ K) (fun K ↦ (hL (p + 1)).fac _ K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvImageCocone_leg_extension
    (U : Set X) (hU : IsOpen U) (K : Compacts U) (p : ℕ) :
    (compactSupportMvImageCocone R U hU p).ι.app K ≫
      compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal U)
        hU.isOpenEmbedding_subtypeVal p =
      compactSupportCohomologyClass R X
        (openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K) p := by
  let q := openEmbeddingCohomologySupportPullback R (ContinuousMap.subtypeVal U)
    hU.isOpenEmbedding_subtypeVal K p
  let := isIso_openEmbeddingCohomologySupportPullback R (ContinuousMap.subtypeVal U)
    hU.isOpenEmbedding_subtypeVal K p
  change (q ≫ compactSupportCohomologyClass R U K p) ≫ _ = _
  rw [Category.assoc]
  have h : compactSupportCohomologyClass R U K p ≫
      compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal U)
        hU.isOpenEmbedding_subtypeVal p =
      openEmbeddingCompactSupportCohomologyLeg R (ContinuousMap.subtypeVal U)
        hU.isOpenEmbedding_subtypeVal K p := colimit.ι_desc _ _
  rw [h]
  change (asIso q).hom ≫ ((asIso q).inv ≫ _) = _
  exact (asIso q).hom_inv_id_assoc _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [T2Space X] in
private theorem compactSupportMvSumNatTrans_rightCocone
    (U V : Set X) (K : Compacts U × Compacts V) (p : ℕ) :
    (compactSupportMvSumNatTrans R U V p).app K ≫
      (compactSupportMvRightCocone R U V p).ι.app K =
    biprod.desc
      (compactSupportCohomologyClass R X
        (openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K.1) p)
      (compactSupportCohomologyClass R X
        (openEmbeddingCompactImage (ContinuousMap.subtypeVal V) K.2) p) := by
  let H := relativeSingularCohomologyFunctor R X p
  let A := openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K.1
  let B := openEmbeddingCompactImage (ContinuousMap.subtypeVal V) K.2
  apply biprod.hom_ext'
  · change biprod.inl ≫ biprod.desc _ _ ≫ _ = biprod.inl ≫ biprod.desc _ _
    rw [biprod.inl_desc_assoc, biprod.inl_desc]
    change H.map _ ≫ (H.map _ ≫ compactSupportCohomologyClass R X (A ⊔ B) p) = _
    rw [← Category.assoc, ← H.map_comp]
    calc
      _ = (compactSupportCohomologyFunctor R X p).map (homOfLE (show A ≤ A ⊔ B from
          le_sup_left)) ≫ compactSupportCohomologyClass R X (A ⊔ B) p := by
        apply congrArg (fun f ↦ f ≫ compactSupportCohomologyClass R X (A ⊔ B) p)
        exact congrArg H.map (Subsingleton.elim _ _)
      _ = _ := colimit.w (compactSupportCohomologyFunctor R X p) (homOfLE le_sup_left)
  · change biprod.inr ≫ biprod.desc _ _ ≫ _ = biprod.inr ≫ biprod.desc _ _
    rw [biprod.inr_desc_assoc, biprod.inr_desc]
    change H.map _ ≫ (H.map _ ≫ compactSupportCohomologyClass R X (A ⊔ B) p) = _
    rw [← Category.assoc, ← H.map_comp]
    calc
      _ = (compactSupportCohomologyFunctor R X p).map (homOfLE (show B ≤ A ⊔ B from
          le_sup_right)) ≫ compactSupportCohomologyClass R X (A ⊔ B) p := by
        apply congrArg (fun f ↦ f ≫ compactSupportCohomologyClass R X (A ⊔ B) p)
        exact congrArg H.map (Subsingleton.elim _ _)
      _ = _ := colimit.w (compactSupportCohomologyFunctor R X p) (homOfLE le_sup_right)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvAssembledSum_eq
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportMvAssembledSum R U V hU hV p =
      biprod.desc
        (compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal U)
          hU.isOpenEmbedding_subtypeVal p)
        (compactSupportCohomologyOpenExtension R (ContinuousMap.subtypeVal V)
          hV.isOpenEmbedding_subtypeVal p) := by
  apply (compactSupportMvMiddleCoconeIsColimit R U V hU hV p).hom_ext
  intro K
  dsimp only [compactSupportMvAssembledSum]
  rw [(compactSupportMvMiddleCoconeIsColimit R U V hU hV p).fac]
  change (compactSupportMvSumNatTrans R U V p).app K ≫
    (compactSupportMvRightCocone R U V p).ι.app K = _
  rw [compactSupportMvSumNatTrans_rightCocone]
  change biprod.desc _ _ =
    biprod.map ((compactSupportMvImageCocone R U hU p).ι.app K.1)
      ((compactSupportMvImageCocone R V hV p).ι.app K.2) ≫ biprod.desc _ _
  apply biprod.hom_ext'
  · rw [biprod.inl_desc, biprod.inl_map_assoc, biprod.inl_desc]
    exact (compactSupportMvImageCocone_leg_extension R U hU K.1 p).symm
  · rw [biprod.inr_desc, biprod.inr_map_assoc, biprod.inr_desc]
    exact (compactSupportMvImageCocone_leg_extension R V hV K.2 p).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvImageCocone_extension_of_le
    (W U : Set X) (hW : IsOpen W) (hU : IsOpen U) (hWU : W ⊆ U)
    (K : Compacts W) (L : Compacts U)
    (hKL : openEmbeddingCompactImage (ContinuousMap.inclusion hWU) K ≤ L)
    (hX : openEmbeddingCompactImage (ContinuousMap.subtypeVal W) K ≤
      openEmbeddingCompactImage (ContinuousMap.subtypeVal U) L) (p : ℕ) :
    (compactSupportMvImageCocone R W hW p).ι.app K ≫
      compactSupportCohomologyOpenExtension R (ContinuousMap.inclusion hWU)
        (IsOpenEmbedding.inclusion hWU (hW.preimage continuous_subtype_val)) p =
      (compactSupportCohomologyFunctor R X p).map (homOfLE hX) ≫
        (compactSupportMvImageCocone R U hU p).ι.app L := by
  /- Pull back at the same ambient compact control, then enlarge inside U.
  The resulting square commutes before inversion. Cancelling its one
  specified excision inverse gives compatibility with actual extension. -/
  let f := ContinuousMap.subtypeVal W
  let g := ContinuousMap.subtypeVal U
  let j := ContinuousMap.inclusion hWU
  have hj : IsOpenEmbedding j :=
    IsOpenEmbedding.inclusion hWU (hW.preimage continuous_subtype_val)
  let KJ := openEmbeddingCompactImage j K
  let KX := openEmbeddingCompactImage f K
  have hgK : Set.MapsTo g ((KJ : Set U)ᶜ) ((KX : Set X)ᶜ) := by
    intro x hx
    rintro ⟨y, hy, heq⟩
    exact hx ⟨y, hy, Subtype.ext heq⟩
  let qW := openEmbeddingCohomologySupportPullback R f hW.isOpenEmbedding_subtypeVal K p
  let qj := openEmbeddingCohomologySupportPullback R j hj K p
  let qg := relativeSingularCohomologyPullback R g hgK p
  let qL := openEmbeddingCohomologySupportPullback R g hU.isOpenEmbedding_subtypeVal L p
  let rU := (compactSupportCohomologyFunctor R U p).map (homOfLE hKL)
  let rX := (compactSupportCohomologyFunctor R X p).map (homOfLE hX)
  let := isIso_openEmbeddingCohomologySupportPullback R j hj K p
  have hcomp : qg ≫ qj = qW := by
    dsimp only [qg, qj, qW, openEmbeddingCohomologySupportPullback]
    rw [← relativeSingularCohomologyPullback_comp]
    rfl
  have hsquare : rX ≫ qL = qg ≫ rU :=
    relativeSingularCohomologyPullback_restriction R g
      (Set.compl_subset_compl.mpr hKL) (Set.compl_subset_compl.mpr hX) _ hgK p
  have hleg : compactSupportCohomologyClass R W K p ≫
      compactSupportCohomologyOpenExtension R j hj p =
        (asIso qj).inv ≫ compactSupportCohomologyClass R U KJ p := colimit.ι_desc _ _
  change (qW ≫ compactSupportCohomologyClass R W K p) ≫ _ =
    rX ≫ (qL ≫ compactSupportCohomologyClass R U L p)
  rw [Category.assoc, hleg, ← hcomp, Category.assoc]
  erw [(asIso qj).hom_inv_id_assoc]
  rw [← Category.assoc, hsquare, Category.assoc]
  exact congrArg (fun k ↦ qg ≫ k)
    (colimit.w (compactSupportCohomologyFunctor R U p) (homOfLE hKL)).symm

private def compactSupportMvLeftTransport (U V : Set X) (K : Compacts U × Compacts V) :
    (compactSupportMvRelativeUnionFunctor U V).obj K ⟶
      (compactSupportComplementFunctor X).obj
        ((compactSupportMvImageFunctor (U ∩ V)).obj (compactSupportMvIntersection U V K)) :=
  (compactSupportMvRelativeUnionIso U V).hom.app K ≫
    (compactSupportComplementFunctor X).map
      ((compactSupportMvIntersectionSupportIso U V).hom.app K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvLeftCocone_leg
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (K : Compacts U × Compacts V) (p : ℕ) :
    (compactSupportMvLeftCocone R U V hU hV p).ι.app K =
      (relativeSingularCohomologyFunctor R X p).map (compactSupportMvLeftTransport U V K) ≫
        (compactSupportMvImageCocone R (U ∩ V) (hU.inter hV) p).ι.app
          (compactSupportMvIntersection U V K) := by
  simp only [compactSupportMvLeftCocone, compactSupportMvIntersectionCocone,
    compactSupportMvIntersectionCohomologyIso, compactSupportMvLeftTransport,
    Cocone.precompose, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Functor.associator_hom_app, Functor.map_comp,
    Category.assoc, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvLeftCocone_difference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (K : Compacts U × Compacts V) (p : ℕ) :
    (compactSupportMvLeftCocone R U V hU hV p).ι.app K ≫
      biprod.lift
        (compactSupportCohomologyOpenExtension R (compactSupportMvInterLeft U V)
          (compactSupportMvInterLeft_isOpenEmbedding U V hU hV) p)
        (-(compactSupportCohomologyOpenExtension R (compactSupportMvInterRight U V)
          (compactSupportMvInterRight_isOpenEmbedding U V hU hV) p)) =
      (compactSupportMvDifferenceNatTrans R U V p).app K ≫
        (compactSupportMvMiddleCocone R U V hU hV p).ι.app K := by
  let I := compactSupportMvIntersection U V K
  let H := relativeSingularCohomologyFunctor R X p
  let c := (compactSupportMvLeftCocone R U V hU hV p).ι.app K
  let cU := (compactSupportMvImageCocone R U hU p).ι.app K.1
  let cV := (compactSupportMvImageCocone R V hV p).ι.app K.2
  let A : Set X := ((K.1.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ
  let B : Set X := ((K.2.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ
  have hleft : c ≫ compactSupportCohomologyOpenExtension R (compactSupportMvInterLeft U V)
      (compactSupportMvInterLeft_isOpenEmbedding U V hU hV) p =
        relativeSingularCohomologyRestriction R A (A ∪ B) Set.subset_union_left p ≫ cU := by
    have hIL : openEmbeddingCompactImage
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) I ≤ K.1 := by
      rintro x ⟨y, hy, rfl⟩
      change y.val ∈ (Subtype.val '' (K.1 : Set U)) ∩ (Subtype.val '' (K.2 : Set V)) at hy
      obtain ⟨z, hz, heq⟩ := hy.1
      have hzy : z = ContinuousMap.inclusion
          (Set.inter_subset_left : U ∩ V ⊆ U) y := Subtype.ext heq
      exact hzy ▸ hz
    have hX : openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I ≤
        openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K.1 := by
      rintro x ⟨y, hy, rfl⟩
      exact hy.1
    change (compactSupportMvLeftCocone R U V hU hV p).ι.app K ≫ _ = _
    rw [compactSupportMvLeftCocone_leg, Category.assoc]
    have hext := compactSupportMvImageCocone_extension_of_le R (U ∩ V) U
      (hU.inter hV) hU Set.inter_subset_left I K.1 hIL hX p
    erw [hext]
    change H.map _ ≫ (H.map _ ≫ cU) = H.map _ ≫ cU
    rw [← Category.assoc, ← H.map_comp]
    apply congrArg (fun f ↦ f ≫ cU)
    exact congrArg H.map (Subsingleton.elim _ _)
  have hright : c ≫ compactSupportCohomologyOpenExtension R (compactSupportMvInterRight U V)
      (compactSupportMvInterRight_isOpenEmbedding U V hU hV) p =
        relativeSingularCohomologyRestriction R B (A ∪ B) Set.subset_union_right p ≫ cV := by
    have hIL : openEmbeddingCompactImage
        (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) I ≤ K.2 := by
      rintro x ⟨y, hy, rfl⟩
      change y.val ∈ (Subtype.val '' (K.1 : Set U)) ∩ (Subtype.val '' (K.2 : Set V)) at hy
      obtain ⟨z, hz, heq⟩ := hy.2
      have hzy : z = ContinuousMap.inclusion
          (Set.inter_subset_right : U ∩ V ⊆ V) y := Subtype.ext heq
      exact hzy ▸ hz
    have hX : openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I ≤
        openEmbeddingCompactImage (ContinuousMap.subtypeVal V) K.2 := by
      rintro x ⟨y, hy, rfl⟩
      exact hy.2
    change (compactSupportMvLeftCocone R U V hU hV p).ι.app K ≫ _ = _
    rw [compactSupportMvLeftCocone_leg, Category.assoc]
    have hext := compactSupportMvImageCocone_extension_of_le R (U ∩ V) V
      (hU.inter hV) hV Set.inter_subset_right I K.2 hIL hX p
    erw [hext]
    change H.map _ ≫ (H.map _ ≫ cV) = H.map _ ≫ cV
    rw [← Category.assoc, ← H.map_comp]
    apply congrArg (fun f ↦ f ≫ cV)
    exact congrArg H.map (Subsingleton.elim _ _)
  -- The two compatible extensions retain the native difference sign.
  change c ≫ biprod.lift _ _ = biprod.lift _ _ ≫ biprod.map cU cV
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst,
      ← Category.assoc, biprod.lift_fst]
    exact hleft
  · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc, biprod.lift_snd, Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg hright

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvAssembledDifference_eq
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportMvAssembledDifference R U V hU hV p =
      biprod.lift
        (compactSupportCohomologyOpenExtension R (compactSupportMvInterLeft U V)
          (compactSupportMvInterLeft_isOpenEmbedding U V hU hV) p)
        (-(compactSupportCohomologyOpenExtension R (compactSupportMvInterRight U V)
          (compactSupportMvInterRight_isOpenEmbedding U V hU hV) p)) := by
  apply (compactSupportMvLeftCoconeIsColimit R U V hU hV p).hom_ext
  intro K
  dsimp only [compactSupportMvAssembledDifference]
  rw [(compactSupportMvLeftCoconeIsColimit R U V hU hV p).fac]
  exact (compactSupportMvLeftCocone_difference R U V hU hV K p).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvAssembledDifference_biprodIsoProd
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    compactSupportMvAssembledDifference R U V hU hV p ≫
      (ModuleCat.biprodIsoProd (compactSupportCohomology R U p)
        (compactSupportCohomology R V p)).hom =
      compactSupportCohomologyMayerVietorisDifference R U V hU hV p := by
  rw [compactSupportMvAssembledDifference_eq]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let f := compactSupportCohomologyOpenExtension R (compactSupportMvInterLeft U V)
    (compactSupportMvInterLeft_isOpenEmbedding U V hU hV) p
  let g := -(compactSupportCohomologyOpenExtension R (compactSupportMvInterRight U V)
    (compactSupportMvInterRight_isOpenEmbedding U V hU hV) p)
  apply _root_.Prod.ext
  · exact congrArg (fun k : compactSupportCohomology R (U ∩ V : Set X) p ⟶
      compactSupportCohomology R U p ↦ k a) (biprod.lift_fst f g)
  · exact congrArg (fun k : compactSupportCohomology R (U ∩ V : Set X) p ⟶
      compactSupportCohomology R V p ↦ k a) (biprod.lift_snd f g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem compactSupportMvAssembledSum_biprodIsoProd
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ) :
    (ModuleCat.biprodIsoProd (compactSupportCohomology R U p)
      (compactSupportCohomology R V p)).hom ≫
      compactSupportCohomologyMayerVietorisSum R U V hU hV p =
        compactSupportMvAssembledSum R U V hU hV p := by
  rw [compactSupportMvAssembledSum_eq, biprod.desc_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Mayer–Vietoris is exact at all three positions for the actual compact-support maps. -/
theorem exact_compactSupportCohomologyMayerVietoris
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (p : ℕ) :
    Function.Exact (compactSupportCohomologyMayerVietorisDifference R U V hU hV p)
      (compactSupportCohomologyMayerVietorisSum R U V hU hV p) ∧
    Function.Exact (compactSupportCohomologyMayerVietorisSum R U V hU hV p)
      (compactSupportCohomologyMayerVietorisBoundary R U V hU hV hcover p) ∧
    Function.Exact (compactSupportCohomologyMayerVietorisBoundary R U V hU hV hcover p)
      (compactSupportCohomologyMayerVietorisDifference R U V hU hV (p + 1)) := by
  /- The filtered-colimit row uses categorical biproducts. Its two maps
  have been identified with the original extension maps. Transport only
  that middle object to the concrete pair of modules in the public row. -/
  let e (q : ℕ) := ModuleCat.biprodIsoProd (compactSupportCohomology R U q)
    (compactSupportCohomology R V q)
  have hf (q : ℕ) (x : compactSupportCohomology R (U ∩ V : Set X) q) :
      (e q).hom (compactSupportMvAssembledDifference R U V hU hV q x) =
        compactSupportCohomologyMayerVietorisDifference R U V hU hV q x :=
    congrArg (fun k ↦ k x) (compactSupportMvAssembledDifference_biprodIsoProd R U V hU hV q)
  have hg (x : (compactSupportCohomology R U p ⊞ compactSupportCohomology R V p :
      ModuleCat.{u} R)) :
      compactSupportCohomologyMayerVietorisSum R U V hU hV p ((e p).hom x) =
        compactSupportMvAssembledSum R U V hU hV p x :=
    congrArg (fun k ↦ k x) (compactSupportMvAssembledSum_biprodIsoProd R U V hU hV p)
  obtain ⟨h₁, h₂, h₃⟩ := compactSupportMv_assembled_exact R U V hU hV hcover p
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e p).hom).surjective y
    rw [hg, h₁ x]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (hf p a).symm.trans (congrArg (e p).hom ha)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (ConcreteCategory.bijective_of_isIso (e p).hom).injective ((hf p a).trans ha)⟩
  · intro z
    rw [h₂ z]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(e p).hom x, (hg x).trans hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e p).hom).surjective y
      exact ⟨x, (hg x).symm.trans hy⟩
  · intro y
    constructor
    · intro hy
      apply (h₃ y).mp
      apply (ConcreteCategory.bijective_of_isIso (e (p + 1)).hom).injective
      rw [map_zero, hf]
      exact hy
    · intro hy
      have hz := (h₃ y).mpr hy
      exact (hf (p + 1) y).symm.trans ((congrArg (e (p + 1)).hom hz).trans (map_zero _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The connecting map on a specified union control is the original relative boundary,
pulled back by the specified intersection excision and inserted at that compact control. -/
theorem compactSupportCohomologyMayerVietorisBoundary_representative
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (K : Compacts U) (L : Compacts V) (I : Compacts (U ∩ V : Set X))
    (hI : openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I =
      openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K ⊓
        openEmbeddingCompactImage (ContinuousMap.subtypeVal V) L) (p : ℕ)
    (a : relativeSingularCohomology R
      (((openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K : Set X)ᶜ) ∩
        ((openEmbeddingCompactImage (ContinuousMap.subtypeVal V) L : Set X)ᶜ)) p) :
    let A := openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K
    let B := openEmbeddingCompactImage (ContinuousMap.subtypeVal V) L
    compactSupportCohomologyMayerVietorisBoundary R U V hU hV hcover p
      (compactSupportCohomologyClass R X (A ⊔ B) p
        (relativeSingularCohomologyRestriction R ((A ⊔ B : Compacts X) : Set X)ᶜ
          ((A : Set X)ᶜ ∩ (B : Set X)ᶜ) (Set.compl_union _ _).subset p a)) =
    compactSupportCohomologyClass R (U ∩ V : Set X) I (p + 1)
      (openEmbeddingCohomologySupportPullback R (ContinuousMap.subtypeVal (U ∩ V))
        (hU.inter hV).isOpenEmbedding_subtypeVal I (p + 1)
        (relativeSingularCohomologyRestriction R
          ((openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I : Set X)ᶜ)
          ((A : Set X)ᶜ ∪ (B : Set X)ᶜ) (by rw [hI]; exact (Set.compl_inter _ _).subset)
          (p + 1) (relativeSingularCohomologyMayerVietorisBoundary R
            (A : Set X)ᶜ (B : Set X)ᶜ A.isCompact.isClosed.isOpen_compl
            B.isCompact.isClosed.isOpen_compl p a))) := by
  let A := openEmbeddingCompactImage (ContinuousMap.subtypeVal U) K
  let B := openEmbeddingCompactImage (ContinuousMap.subtypeVal V) L
  have hIeq : I = compactSupportMvIntersection U V (K, L) := by
    apply Compacts.ext
    ext x
    change x ∈ (I : Set (U ∩ V : Set X)) ↔ x.val ∈ (A : Set X) ∩ (B : Set X)
    constructor
    · intro hx
      have hmem : x.val ∈
          (openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I : Set X) :=
        ⟨x, hx, rfl⟩
      rw [hI] at hmem
      exact hmem
    · intro hx
      have hmem : x.val ∈
          (openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I : Set X) := by
        rw [hI]
        exact hx
      obtain ⟨y, hy, hyx⟩ := hmem
      exact (Subtype.ext hyx : y = x) ▸ hy
  subst I
  let I := compactSupportMvIntersection U V (K, L)
  let rIn := relativeSingularCohomologyRestriction R ((A ⊔ B : Compacts X) : Set X)ᶜ
    ((A : Set X)ᶜ ∩ (B : Set X)ᶜ) (Set.compl_union _ _).subset p
  let rOut := relativeSingularCohomologyRestriction R
    ((openEmbeddingCompactImage (ContinuousMap.subtypeVal (U ∩ V)) I : Set X)ᶜ)
    ((A : Set X)ᶜ ∪ (B : Set X)ᶜ) (by rw [hI]; exact (Set.compl_inter _ _).subset) (p + 1)
  let q := openEmbeddingCohomologySupportPullback R (ContinuousMap.subtypeVal (U ∩ V))
    (hU.inter hV).isOpenEmbedding_subtypeVal I (p + 1)
  -- The two De Morgan transports are the unique inclusion maps in the same subset category.
  have hin : (compactSupportMvRightCocone R U V p).ι.app (K, L) =
      rIn ≫ compactSupportCohomologyClass R X (A ⊔ B) p := by
    let H := relativeSingularCohomologyFunctor R X p
    change H.map _ ≫ compactSupportCohomologyClass R X (A ⊔ B) p =
      H.map _ ≫ compactSupportCohomologyClass R X (A ⊔ B) p
    exact congrArg (fun f ↦ H.map f ≫ compactSupportCohomologyClass R X (A ⊔ B) p)
      (Subsingleton.elim _ _)
  have hout : (compactSupportMvLeftCocone R U V hU hV (p + 1)).ι.app (K, L) =
      rOut ≫ q ≫ compactSupportCohomologyClass R (U ∩ V : Set X) I (p + 1) := by
    rw [compactSupportMvLeftCocone_leg]
    let H := relativeSingularCohomologyFunctor R X (p + 1)
    change H.map _ ≫ (q ≫ compactSupportCohomologyClass R (U ∩ V : Set X) I (p + 1)) =
      H.map _ ≫ q ≫ compactSupportCohomologyClass R (U ∩ V : Set X) I (p + 1)
    exact congrArg (fun f ↦ H.map f ≫ q ≫
      compactSupportCohomologyClass R (U ∩ V : Set X) I (p + 1)) (Subsingleton.elim _ _)
  -- Evaluate precisely the defining descent on this pair of compact controls.
  have hfac : (compactSupportMvRightCocone R U V p).ι.app (K, L) ≫
      compactSupportCohomologyMayerVietorisBoundary R U V hU hV hcover p =
    (compactSupportMvBoundaryNatTrans R U V p).app (K, L) ≫
      (compactSupportMvLeftCocone R U V hU hV (p + 1)).ι.app (K, L) :=
    (compactSupportMvRightCoconeIsColimit R U V hU hV hcover p).fac _ (K, L)
  rw [hin, hout] at hfac
  exact congrArg (fun f ↦ f a) hfac

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degree-zero Mayer–Vietoris row starts with an injective difference map. -/
theorem compactSupportCohomologyMayerVietorisDifference_injective_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    Function.Injective (compactSupportCohomologyMayerVietorisDifference R U V hU hV 0) := by
  let F := compactSupportMvDifferenceNatTrans R U V 0
  have (K : Compacts U × Compacts V) : Mono (F.app K) := by
    let A : Set X := ((K.1.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ
    let B : Set X := ((K.2.map Subtype.val continuous_subtype_val : Compacts X) : Set X)ᶜ
    have hA : IsOpen A :=
      (K.1.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
    have hB : IsOpen B :=
      (K.2.map Subtype.val continuous_subtype_val).isCompact.isClosed.isOpen_compl
    let S := relativeSingularCochainMayerVietorisSequence R A B
    -- There is no incoming differential in degree zero of the native cochain complexes.
    have : Mono (HomologicalComplex.homologyMap S.f 0) := by
      have := (shortExact_relativeSingularCochainMayerVietorisSequence R A B).mono_f
      apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
      simp
    have : IsIso (relativeUnionCohomologyComparison R A B 0) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (relativeUnionCohomologyComparison_bijective R A B hA hB 0)
    have h : relativeUnionCohomologyComparison R A B 0 ≫
        HomologicalComplex.homologyMap S.f 0 ≫
          (relativeSingularCohomologyMayerVietorisMiddleIso R A B 0).hom = F.app K :=
      relativeSingularCohomologyMayerVietorisMiddleIso_comparison_difference R A B 0
    rw [← h]
    infer_instance
  have : Mono F := NatTrans.mono_of_mono_app F
  let : HasExactColimitsOfShape (Compacts U × Compacts V) (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.domain_of_functor (Compacts U × Compacts V)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  -- Filtered colimits preserve this first monomorphism, as well as the repeating exact row.
  have : Mono (compactSupportMvAssembledDifference R U V hU hV 0) :=
    colim.map_mono' F (compactSupportMvLeftCoconeIsColimit R U V hU hV 0)
      (compactSupportMvMiddleCoconeIsColimit R U V hU hV 0) _
      (fun K ↦ (compactSupportMvLeftCoconeIsColimit R U V hU hV 0).fac _ K)
  have h : Mono (compactSupportCohomologyMayerVietorisDifference R U V hU hV 0) := by
    rw [← compactSupportMvAssembledDifference_biprodIsoProd]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp h

end AtiyahSinger
