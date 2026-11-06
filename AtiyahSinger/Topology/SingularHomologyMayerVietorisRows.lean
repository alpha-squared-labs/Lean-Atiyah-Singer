/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomologyMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The ordinary Mayer--Vietoris rows with actual inclusion maps

Public module ID: M2149.

The original sum-image short exact sequence gives the usual difference, sum,
and connecting homomorphisms after the canonical biproduct and open-cover
comparisons. These adapters retain the same boundary map and its sign.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The difference of the original homology inclusions from the overlap. -/
def singularHomologyMayerVietorisDifference (A B : Set X) (k : ℕ) :
    singularHomology R ↥(A ∩ B) k ⟶
      ModuleCat.of R (singularHomology R A k × singularHomology R B k) :=
  ModuleCat.ofHom
    ((singularHomologyMap R (ContinuousMap.inclusion Set.inter_subset_left) k).hom.prod
      (-(singularHomologyMap R (ContinuousMap.inclusion Set.inter_subset_right) k).hom))

/-- The sum of the two original homology inclusions into the ambient space. -/
def singularHomologyMayerVietorisSum (A B : Set X) (k : ℕ) :
    ModuleCat.of R (singularHomology R A k × singularHomology R B k) ⟶
      singularHomology R X k :=
  ModuleCat.ofHom
    ((singularHomologyMap R (ContinuousMap.subtypeVal A) k).hom.coprod
      (singularHomologyMap R (ContinuousMap.subtypeVal B) k).hom)

/-- Homology of the native chain biproduct is the actual product of homology modules. -/
def singularHomologyMayerVietorisMiddleIso (A B : Set X) (k : ℕ) :
    (singularMayerVietorisShortComplex R A B).X₂.homology k ≅
      ModuleCat.of R (singularHomology R A k × singularHomology R B k) :=
  (homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) k).mapBiprod
      (singularChains R A) (singularChains R B) ≪≫
    ModuleCat.biprodIsoProd (singularHomology R A k) (singularHomology R B k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem singularHomologyMayerVietorisMiddleIso_hom_fst (A B : Set X) (k : ℕ) :
    (singularHomologyMayerVietorisMiddleIso R A B k).hom ≫
        ModuleCat.ofHom (LinearMap.fst R (singularHomology R A k) (singularHomology R B k)) =
      homologyMap (biprod.fst : singularChains R A ⊞ singularChains R B ⟶ _) k := by
  dsimp only [singularHomologyMayerVietorisMiddleIso]
  rw [Iso.trans_hom, Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_fst,
    Iso.hom_inv_id_assoc, Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem singularHomologyMayerVietorisMiddleIso_hom_snd (A B : Set X) (k : ℕ) :
    (singularHomologyMayerVietorisMiddleIso R A B k).hom ≫
        ModuleCat.ofHom (LinearMap.snd R (singularHomology R A k) (singularHomology R B k)) =
      homologyMap (biprod.snd : singularChains R A ⊞ singularChains R B ⟶ _) k := by
  dsimp only [singularHomologyMayerVietorisMiddleIso]
  rw [Iso.trans_hom, Category.assoc, ← ModuleCat.biprodIsoProd_inv_comp_snd,
    Iso.hom_inv_id_assoc, Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native overlap arrow becomes the difference of actual inclusions. -/
theorem singularHomologyMayerVietorisMiddleIso_difference (A B : Set X) (k : ℕ) :
    homologyMap (singularMayerVietorisShortComplex R A B).f k ≫
        (singularHomologyMayerVietorisMiddleIso R A B k).hom =
      singularHomologyMayerVietorisDifference R A B k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Prod.ext
  · have hmap : homologyMap (singularMayerVietorisShortComplex R A B).f k ≫
        homologyMap (biprod.fst : singularChains R A ⊞ singularChains R B ⟶ _) k =
      singularHomologyMap R (ContinuousMap.inclusion Set.inter_subset_left) k := by
      rw [← homologyMap_comp]
      simp only [singularMayerVietorisShortComplex, biprod.lift_fst]
      rfl
    exact (congrArg (fun f ↦ f (homologyMap
      (singularMayerVietorisShortComplex R A B).f k c))
        (singularHomologyMayerVietorisMiddleIso_hom_fst R A B k)).trans
      (congrArg (fun f ↦ f c) hmap)
  · have hmap : homologyMap (singularMayerVietorisShortComplex R A B).f k ≫
        homologyMap (biprod.snd : singularChains R A ⊞ singularChains R B ⟶ _) k =
      -singularHomologyMap R (ContinuousMap.inclusion Set.inter_subset_right) k := by
      rw [← homologyMap_comp]
      simp only [singularMayerVietorisShortComplex, biprod.lift_snd, homologyMap_neg]
      rfl
    exact (congrArg (fun f ↦ f (homologyMap
      (singularMayerVietorisShortComplex R A B).f k c))
        (singularHomologyMayerVietorisMiddleIso_hom_snd R A B k)).trans
      (congrArg (fun f ↦ f c) hmap)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native sum followed by image inclusion becomes the sum of actual inclusions. -/
theorem singularHomologyMayerVietorisMiddleIso_sum (A B : Set X) (k : ℕ) :
    (singularHomologyMayerVietorisMiddleIso R A B k).hom ≫
        singularHomologyMayerVietorisSum R A B k =
      homologyMap (singularMayerVietorisShortComplex R A B).g k ≫
        homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) k := by
  have hsum : singularHomologyMayerVietorisSum R A B k =
      ModuleCat.ofHom (LinearMap.fst R (singularHomology R A k) (singularHomology R B k)) ≫
          singularHomologyMap R (ContinuousMap.subtypeVal A) k +
        ModuleCat.ofHom (LinearMap.snd R (singularHomology R A k) (singularHomology R B k)) ≫
          singularHomologyMap R (ContinuousMap.subtypeVal B) k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  have hfac : (singularMayerVietorisShortComplex R A B).g ≫
      Abelian.image.ι (singularSubspaceSumChains R A B) = singularSubspaceSumChains R A B :=
    Abelian.image.fac _
  rw [← homologyMap_comp, hfac, hsum, Preadditive.comp_add,
    ← Category.assoc, ← Category.assoc,
    singularHomologyMayerVietorisMiddleIso_hom_fst,
    singularHomologyMayerVietorisMiddleIso_hom_snd]
  change homologyMap _ k ≫ homologyMap (singularSubspaceChains R A) k +
    homologyMap _ k ≫ homologyMap (singularSubspaceChains R B) k = _
  rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add]
  exact congrArg (fun f ↦ homologyMap f k) biprod.desc_eq.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The overlap difference and ambient sum form an exact ordinary homology row. -/
theorem singularHomologyMayerVietoris_exact_difference_sum
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (k : ℕ) : Function.Exact
      (singularHomologyMayerVietorisDifference R A B k)
      (singularHomologyMayerVietorisSum R A B k) := by
  let S := singularMayerVietorisShortComplex R A B
  let e := singularHomologyMayerVietorisMiddleIso R A B k
  let j := homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) k
  have : IsIso j := isIso_homologyMap_singularMayerVietorisImageInclusion R A B hA hB hcover k
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (homologyMap S.f k).hom) (f₂₃ := (homologyMap S.g k).hom)
    (e₁ := LinearEquiv.refl R (S.X₁.homology k))
    (e₂ := e.toLinearEquiv) (e₃ := (asIso j).toLinearEquiv)
  · exact congrArg ModuleCat.Hom.hom
      (singularHomologyMayerVietorisMiddleIso_difference R A B k).symm
  · exact congrArg ModuleCat.Hom.hom
      (singularHomologyMayerVietorisMiddleIso_sum R A B k)
  · let hS := shortExact_singularMayerVietorisShortComplex R A B
    have he := (hS.homology_exact₂ k).moduleCat_range_eq_ker
    exact LinearMap.exact_iff.mpr he.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The ambient sum is exact against the original connecting homomorphism. -/
theorem singularHomologyMayerVietoris_exact_sum_boundary
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (k : ℕ) : Function.Exact
      (singularHomologyMayerVietorisSum R A B (k + 1))
      (singularHomologyMayerVietorisBoundary R A B hA hB hcover k) := by
  let S := singularMayerVietorisShortComplex R A B
  let hS := shortExact_singularMayerVietorisShortComplex R A B
  let e := singularHomologyMayerVietorisMiddleIso R A B (k + 1)
  let j := homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) (k + 1)
  have : IsIso j :=
    isIso_homologyMap_singularMayerVietorisImageInclusion R A B hA hB hcover (k + 1)
  have hboundary : j ≫ singularHomologyMayerVietorisBoundary R A B hA hB hcover k =
      hS.δ (k + 1) k rfl := by
    change j ≫ (inv j ≫ hS.δ (k + 1) k rfl) = _
    simp
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (homologyMap S.g (k + 1)).hom) (f₂₃ := (hS.δ (k + 1) k rfl).hom)
    (e₁ := e.toLinearEquiv) (e₂ := (asIso j).toLinearEquiv)
    (e₃ := LinearEquiv.refl R (S.X₁.homology k))
  · exact congrArg ModuleCat.Hom.hom
      (singularHomologyMayerVietorisMiddleIso_sum R A B (k + 1))
  · exact congrArg ModuleCat.Hom.hom hboundary
  · have he := (hS.homology_exact₃ (k + 1) k rfl).moduleCat_range_eq_ker
    exact LinearMap.exact_iff.mpr he.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original connecting homomorphism is exact against the overlap difference. -/
theorem singularHomologyMayerVietoris_exact_boundary_difference
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (k : ℕ) : Function.Exact
      (singularHomologyMayerVietorisBoundary R A B hA hB hcover k)
      (singularHomologyMayerVietorisDifference R A B k) := by
  let S := singularMayerVietorisShortComplex R A B
  let hS := shortExact_singularMayerVietorisShortComplex R A B
  let e := singularHomologyMayerVietorisMiddleIso R A B k
  let j := homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) (k + 1)
  have : IsIso j :=
    isIso_homologyMap_singularMayerVietorisImageInclusion R A B hA hB hcover (k + 1)
  have hboundary : j ≫ singularHomologyMayerVietorisBoundary R A B hA hB hcover k =
      hS.δ (k + 1) k rfl := by
    change j ≫ (inv j ≫ hS.δ (k + 1) k rfl) = _
    simp
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (hS.δ (k + 1) k rfl).hom) (f₂₃ := (homologyMap S.f k).hom)
    (e₁ := (asIso j).toLinearEquiv) (e₂ := LinearEquiv.refl R (S.X₁.homology k))
    (e₃ := e.toLinearEquiv)
  · exact congrArg ModuleCat.Hom.hom hboundary
  · exact congrArg ModuleCat.Hom.hom
      (singularHomologyMayerVietorisMiddleIso_difference R A B k).symm
  · have he := (hS.homology_exact₁ (k + 1) k rfl).moduleCat_range_eq_ker
    exact LinearMap.exact_iff.mpr he.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In degree zero the ambient Mayer--Vietoris sum is surjective. -/
theorem singularHomologyMayerVietorisSum_zero_surjective
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    Function.Surjective (singularHomologyMayerVietorisSum R A B 0) := by
  let S := singularMayerVietorisShortComplex R A B
  have : Epi S.g := (shortExact_singularMayerVietorisShortComplex R A B).epi_g
  have : Epi (homologyMap S.g 0) := epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)
  let j := homologyMap (Abelian.image.ι (singularSubspaceSumChains R A B)) 0
  have : IsIso j := isIso_homologyMap_singularMayerVietorisImageInclusion R A B hA hB hcover 0
  intro c
  obtain ⟨d, hd⟩ := (ConcreteCategory.bijective_of_isIso j).2 c
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (homologyMap S.g 0)).mp inferInstance d
  refine ⟨(singularHomologyMayerVietorisMiddleIso R A B 0).hom b, ?_⟩
  exact (congrArg (fun f ↦ f b) (singularHomologyMayerVietorisMiddleIso_sum R A B 0)).trans
    ((congrArg j hb).trans hd)

end AtiyahSinger
