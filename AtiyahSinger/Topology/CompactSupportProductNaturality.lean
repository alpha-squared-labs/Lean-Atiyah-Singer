/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.OpenEmbeddingKZero

/-!
# Proper pullback and open extension of the actual compact-support product

Public module ID: M1685.

E04/K02: the external product is the existing unique reduced smash lift.
It is contravariantly natural under proper maps and covariantly natural under
open embeddings. These are different operations: an open embedding need not
be proper, and arbitrary continuous pullback need not retain compact support.

Taking the second class to be the specified multiplication-by-z Bott class
gives these naturality statements for the original Bott map, without defining
another periodicity map. Compact parameter spaces may be included in the
first factor; compact support on the whole product then retains joint support
control. Endpoint or parameter restriction must use the actual proper maps.

Sources: Karoubi, K-Theory, II.5.21--5.22, pp.99--101 (relative products and
compact supports), III.1.2--1.3, p.112 (the specified relative Bott product);
Hatcher, Vector Bundles and K-Theory, Section 2.2 (reduced external product).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

variable {X X' Y Y' : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace X'] [LocallyCompactSpace X'] [T2Space X']
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Y'] [LocallyCompactSpace Y'] [T2Space Y']

/-- Proper pullback preserves the specified compact-support external product. -/
theorem compactSupportKZeroExternalProduct_properPullback
    (f : C(X, X')) (hf : IsProperMap f) (g : C(Y, Y')) (hg : IsProperMap g)
    (a : CompactSupportKZero X') (b : CompactSupportKZero Y') :
    compactSupportKZeroPullback (f.prodMap g) (hf.prodMap hg)
        (compactSupportKZeroExternalProduct a b) =
      compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback f hf a) (compactSupportKZeroPullback g hg b) := by
  /- Stage 1: extend the actual proper maps by infinity. Their product and
  the one-point extension of f times g commute with the two smash collapses:
  finite pairs keep their original images, and either infinite coordinate
  is collapsed to infinity. Properness makes these extensions continuous.
  Stage 2: pull back the defining equation for the original product along
  this square. Naturality of the absolute tensor product gives the same
  absolute class as the product of the two reduced pullbacks. The unique
  reduced smash-lift characterization identifies the displayed classes.
  This uses the split wedge construction, not injectivity of forgetting
  an arbitrary relative class. No compactness of the original bases is used. -/
  let F := properOnePointMap f hf
  let G := properOnePointMap g hg
  let H := properOnePointMap (f.prodMap g) (hf.prodMap hg)
  -- The square commutes on finite pairs and on both axes at infinity.
  have hsquare :
      (onePointProductCollapseMap (X := X') (Y := Y')).comp (F.prodMap G) =
        H.comp (onePointProductCollapseMap (X := X) (Y := Y)) := by
    ext z
    rcases z with ⟨x, y⟩
    cases x using OnePoint.rec <;> cases y using OnePoint.rec <;> rfl
  -- Pull the defining absolute identity back along exactly these two extensions.
  have hproduct := congrArg (complexKZeroPullback (F.prodMap G))
    (compactSupportKZeroExternalProduct_pullback a b)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
    complexKZeroPullback_comp, AddMonoidHom.comp_apply,
    complexKZeroExternalProduct_natural] at hproduct
  -- The transported class is the unique reduced lift of the transported inputs.
  exact (existsUnique_compactSupportProduct (compactSupportKZeroPullback f hf a)
    (compactSupportKZeroPullback g hg b)).unique hproduct
      (compactSupportKZeroExternalProduct_pullback _ _)

/-- Open extension preserves the same external product, with both actual embeddings. -/
theorem compactSupportKZeroExternalProduct_openPushforward
    (f : X → X') (hf : IsOpenEmbedding f) (g : Y → Y') (hg : IsOpenEmbedding g)
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
    compactSupportKZeroOpenPushforward (Prod.map f g) (hf.prodMap hg)
        (compactSupportKZeroExternalProduct a b) =
      compactSupportKZeroExternalProduct
        (compactSupportKZeroOpenPushforward f hf a)
        (compactSupportKZeroOpenPushforward g hg b) := by
  /- Stage 1: identify each source with the open image of its specified
  embedding. The product image is the product of those same two open sets.
  The product of the two open-collapse maps commutes with the smash maps:
  a finite pair survives precisely when both entries lie in the images.
  On that locus use the two original inverse-image identifications;
  elsewhere both routes give infinity, including boundary points.
  Stage 2: apply contravariance of reduced pullback and naturality of the
  absolute external product. Uniqueness of the same reduced smash lift
  gives equality. These are open collapses, so no properness of either
  embedding is assumed or inferred. -/
  let := hf.isOpen_range.locallyCompactSpace
  let := hg.isOpen_range.locallyCompactSpace
  let hfg := hf.prodMap hg
  let := hfg.isOpen_range.locallyCompactSpace
  let ef := hf.isEmbedding.toHomeomorph
  let eg := hg.isEmbedding.toHomeomorph
  let efg := hfg.isEmbedding.toHomeomorph
  let iF : C(Set.range f, X) := ⟨ef.symm, ef.symm.continuous⟩
  let iG : C(Set.range g, Y) := ⟨eg.symm, eg.symm.continuous⟩
  let iFG : C(Set.range (Prod.map f g), X × Y) := ⟨efg.symm, efg.symm.continuous⟩
  let cF : C(OnePoint X', OnePoint (Set.range f)) :=
    ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  let cG : C(OnePoint Y', OnePoint (Set.range g)) :=
    ⟨onePointCollapse (Set.range g), continuous_onePointCollapse _ hg.isOpen_range⟩
  let cFG : C(OnePoint (X' × Y'), OnePoint (Set.range (Prod.map f g))) :=
    ⟨onePointCollapse (Set.range (Prod.map f g)),
      continuous_onePointCollapse _ hfg.isOpen_range⟩
  let F := (properOnePointMap iF ef.symm.isProperMap).comp cF
  let G := (properOnePointMap iG eg.symm.isProperMap).comp cG
  let H := (properOnePointMap iFG efg.symm.isProperMap).comp cFG
  -- These actual image collapses recover source points and kill the complement.
  have hF (x : X) : F (f x) = (x : OnePoint X) := by
    change OnePoint.map iF (onePointCollapse (Set.range f) (f x)) = (x : OnePoint X)
    rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  have hG (y : Y) : G (g y) = (y : OnePoint Y) := by
    change OnePoint.map iG (onePointCollapse (Set.range g) (g y)) = (y : OnePoint Y)
    rw [onePointCollapse_coe_of_mem (Set.range g) (g y) ⟨y, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hg.isEmbedding.toHomeomorph_symm_apply y)
  have hH (xy : X × Y) : H (Prod.map f g xy) = (xy : OnePoint (X × Y)) := by
    change OnePoint.map iFG
      (onePointCollapse (Set.range (Prod.map f g)) (Prod.map f g xy)) =
        (xy : OnePoint (X × Y))
    rw [onePointCollapse_coe_of_mem (Set.range (Prod.map f g)) (Prod.map f g xy) ⟨xy, rfl⟩,
      OnePoint.map_some]
    exact congrArg OnePoint.some (hfg.isEmbedding.toHomeomorph_symm_apply xy)
  have hFout (x : X') (hx : x ∉ Set.range f) : F x = OnePoint.infty := by
    change OnePoint.map iF (onePointCollapse (Set.range f) x) = OnePoint.infty
    rw [onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
  have hGout (y : Y') (hy : y ∉ Set.range g) : G y = OnePoint.infty := by
    change OnePoint.map iG (onePointCollapse (Set.range g) y) = OnePoint.infty
    rw [onePointCollapse_coe_of_notMem _ _ hy, OnePoint.map_infty]
  have hHout (xy : X' × Y') (hxy : xy ∉ Set.range (Prod.map f g)) :
      H xy = OnePoint.infty := by
    change OnePoint.map iFG (onePointCollapse (Set.range (Prod.map f g)) xy) =
      OnePoint.infty
    rw [onePointCollapse_coe_of_notMem _ _ hxy, OnePoint.map_infty]
  -- Both routes retain precisely the same finite pairs in the two actual images.
  have hsquare :
      (onePointProductCollapseMap (X := X) (Y := Y)).comp (F.prodMap G) =
        H.comp (onePointProductCollapseMap (X := X') (Y := Y')) := by
    ext z
    rcases z with ⟨x, y⟩
    cases x using OnePoint.rec with
    | infty => rfl
    | coe x =>
      cases y using OnePoint.rec with
      | infty =>
        change onePointProductCollapse (F (x : OnePoint X'), OnePoint.infty) =
          OnePoint.infty
        cases F (x : OnePoint X') using OnePoint.rec <;> rfl
      | coe y =>
        change onePointProductCollapse (F x, G y) = H ((x, y) : OnePoint (X' × Y'))
        by_cases hx : x ∈ Set.range f
        · obtain ⟨x, rfl⟩ := hx
          by_cases hy : y ∈ Set.range g
          · obtain ⟨y, rfl⟩ := hy
            rw [hF, hG, show (f x, g y) = Prod.map f g (x, y) from rfl, hH]
            rfl
          · have hnot : (f x, y) ∉ Set.range (Prod.map f g) := by
              rintro ⟨xy, hxy⟩
              exact hy ⟨xy.2, congrArg Prod.snd hxy⟩
            rw [hF, hGout y hy, hHout _ hnot]
            rfl
        · have hnot : (x, y) ∉ Set.range (Prod.map f g) := by
            rintro ⟨xy, hxy⟩
            exact hx ⟨xy.1, congrArg Prod.fst hxy⟩
          rw [hFout x hx, hHout _ hnot]
          rfl
  -- The covariant extensions are pullbacks along these same reverse collapse maps.
  have hvalF : (compactSupportKZeroOpenPushforward f hf a).val =
      complexKZeroPullback F a.val := by
    change complexKZeroPullback cF
      (complexKZeroPullback (properOnePointMap iF ef.symm.isProperMap) a.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  have hvalG : (compactSupportKZeroOpenPushforward g hg b).val =
      complexKZeroPullback G b.val := by
    change complexKZeroPullback cG
      (complexKZeroPullback (properOnePointMap iG eg.symm.isProperMap) b.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  have hvalH : (compactSupportKZeroOpenPushforward (Prod.map f g) hfg
      (compactSupportKZeroExternalProduct a b)).val =
        complexKZeroPullback H (compactSupportKZeroExternalProduct a b).val := by
    change complexKZeroPullback cFG
      (complexKZeroPullback (properOnePointMap iFG efg.symm.isProperMap)
        (compactSupportKZeroExternalProduct a b).val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  -- Naturality of the absolute product identifies the unique reduced smash lift.
  have hproduct := congrArg (complexKZeroPullback (F.prodMap G))
    (compactSupportKZeroExternalProduct_pullback a b)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
    complexKZeroPullback_comp, AddMonoidHom.comp_apply,
    complexKZeroExternalProduct_natural] at hproduct
  apply (existsUnique_compactSupportProduct (compactSupportKZeroOpenPushforward f hf a)
    (compactSupportKZeroOpenPushforward g hg b)).unique ?_
      (compactSupportKZeroExternalProduct_pullback _ _)
  rw [hvalH, hvalF, hvalG]
  exact hproduct

end AtiyahSinger
