/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import AtiyahSinger.Topology.PointRelativeCohomology
public import AtiyahSinger.Topology.RelativeCohomologySequence

/-!
# Compact supports in a specified relative compactification

Public module ID: M1690.

An open embedding extends each compact-support representative by the original
excision inverse, then restricts its relative condition to the complement of
the open image. The resulting colimit comparison retains that complement;
forgetting it prematurely would generally lose supported classes.

The comparison respects multiplication by classes that extend to the ambient
space. A retraction onto the complement makes its relative-to-ordinary map
injective. These are the original singular models, with no quotient/cofibration
comparison assumed. Sources: Hatcher, Algebraic Topology, Sections 2.1, 3.1
and 3.3, for excision, relative cohomology, and compact supports.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R]

/-- A genuine subspace retraction makes the original relative-to-ordinary map injective. -/
theorem relativeSingularCohomologyToOrdinary_injective_of_retraction
    {Z : Type u} [TopologicalSpace Z] (A : Set Z) (r : C(Z, A))
    (hr : r.comp (ContinuousMap.subtypeVal A) = ContinuousMap.id A) (n : ℕ) :
    Function.Injective (relativeSingularCohomologyToOrdinary R A n) := by
  have : (singularCochainDualFunctor.{u} R).Additive := by
    change (((((linearYoneda R (ModuleCat.{u} R)).obj
      (singularCoefficient R)).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).op) ⋙
        HomologicalComplex.unopFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)).Additive
    infer_instance
  let F := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  let i := singularSubspaceChains R A
  let q := (singularChainsFunctor R).map (TopCat.ofHom r)
  -- The actual retraction splits the original subspace chain map before taking cohomology.
  have hiq : i ≫ q = 𝟙 _ := by
    change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ = _
    rw [← Functor.map_comp]
    have htop : TopCat.ofHom (ContinuousMap.subtypeVal A) ≫ TopCat.ofHom r =
        𝟙 (TopCat.of A) := congrArg TopCat.ofHom hr
    exact (congrArg ((singularChainsFunctor R).map) htop).trans
      ((singularChainsFunctor R).map_id _)
  let S := ShortComplex.cokernelSequence i
  let splitting := ShortComplex.Splitting.ofExactOfRetraction S
    (ShortComplex.cokernelSequence_exact i) q hiq inferInstance
  -- Opposite, additive dualization, and homology preserve this specified splitting.
  let T := S.op.map F
  let splitting' : T.Splitting := splitting.op.map F
  exact (ModuleCat.mono_iff_injective T.f).mp splitting'.mono_f

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A cohomological equivalence of nested subspaces preserves the original relative groups. -/
theorem isIso_relativeSingularCohomologyRestriction_of_isIso_inclusion
    {Z : Type u} [TopologicalSpace Z] {A B : Set Z} (hAB : A ⊆ B)
    (h : ∀ k, IsIso (singularCohomologyPullback R (ContinuousMap.inclusion hAB) k))
    (n : ℕ) : IsIso (relativeSingularCohomologyRestriction R A B hAB n) := by
  have hid (k : ℕ) : IsIso (singularCohomologyPullback R (ContinuousMap.id Z) k) := by
    change IsIso ((singularCohomologyFunctor R k).map (𝟙 _))
    infer_instance
  exact isIso_relativeSingularCohomologyPullback_of_absolute R (ContinuousMap.id Z)
    (fun _ hx ↦ hAB hx) hid h n

section Compactification

variable {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z] [T2Space Z]
  (j : C(X, Z)) (hj : IsOpenEmbedding j)

/-- Extend the original compact representative and retain the ambient complement condition. -/
def compactificationCohomologySupportMap (K : Compacts X) (n : ℕ) :
    relativeSingularCohomology R ((K : Set X)ᶜ) n ⟶
      relativeSingularCohomology R ((Set.range j)ᶜ) n := by
  let := isIso_openEmbeddingCohomologySupportPullback R j hj K n
  exact (asIso (openEmbeddingCohomologySupportPullback R j hj K n)).inv ≫
    relativeSingularCohomologyRestriction R ((Set.range j)ᶜ)
      ((openEmbeddingCompactImage j K : Set Z)ᶜ) (by
        intro z hz h
        obtain ⟨x, _, rfl⟩ := h
        exact hz ⟨x, rfl⟩) n

/-- The original boundary is contained in the complement of every compact-image support. -/
def compactificationComplementInclusion (K : Compacts X) :
    C(↥((Set.range j)ᶜ), ↥((openEmbeddingCompactImage j K : Set Z)ᶜ)) :=
  ContinuousMap.inclusion (by
    rintro z hz ⟨x, _, rfl⟩
    exact hz ⟨x, rfl⟩)

/-- Enlargement of the actual compact support preserves this same relative extension. -/
theorem compactificationCohomologySupportMap_naturality
    (K L : Compacts X) (h : K ≤ L) (n : ℕ) :
    (compactSupportCohomologyFunctor R X n).map (homOfLE h) ≫
        compactificationCohomologySupportMap R j hj L n =
      compactificationCohomologySupportMap R j hj K n := by
  let AK : Set Z := (openEmbeddingCompactImage j K : Set Z)ᶜ
  let AL : Set Z := (openEmbeddingCompactImage j L : Set Z)ᶜ
  let A : Set Z := (Set.range j)ᶜ
  have hLK : AL ⊆ AK := Set.compl_subset_compl.mpr (Set.image_mono h)
  have hAL : A ⊆ AL := by
    rintro z hz ⟨x, _, rfl⟩
    exact hz ⟨x, rfl⟩
  let pK := openEmbeddingCohomologySupportPullback R j hj K n
  let pL := openEmbeddingCohomologySupportPullback R j hj L n
  let rX := (compactSupportCohomologyFunctor R X n).map (homOfLE h)
  let rZ := relativeSingularCohomologyRestriction R AL AK hLK n
  let : IsIso pK := isIso_openEmbeddingCohomologySupportPullback R j hj K n
  let : IsIso pL := isIso_openEmbeddingCohomologySupportPullback R j hj L n
  have hsquare : rZ ≫ pL = pK ≫ rX :=
    relativeSingularCohomologyPullback_restriction R j
      (Set.compl_subset_compl.mpr h) hLK _ _ n
  -- Invert the actual excision square, then compose the same relative restrictions.
  change rX ≫ ((asIso pL).inv ≫ relativeSingularCohomologyRestriction R A AL _ n) =
    (asIso pK).inv ≫ relativeSingularCohomologyRestriction R A AK _ n
  apply (cancel_epi pK).mp
  erw [← Category.assoc pK rX, ← hsquare, Category.assoc rZ pL,
    (asIso pL).hom_inv_id_assoc, (asIso pK).hom_inv_id_assoc]
  let H := relativeSingularCohomologyFunctor R Z n
  change H.map (homOfLE hLK).op ≫ H.map (homOfLE hAL).op =
    H.map (homOfLE (hAL.trans hLK)).op
  rw [← H.map_comp]
  rfl

/-- The original support colimit mapped into the specified ambient relative pair. -/
def compactSupportCohomologyToCompactification (n : ℕ) :
    compactSupportCohomology R X n ⟶ relativeSingularCohomology R ((Set.range j)ᶜ) n :=
  colimit.desc (compactSupportCohomologyFunctor R X n)
    { pt := relativeSingularCohomology R ((Set.range j)ᶜ) n
      ι :=
        { app := fun K ↦ compactificationCohomologySupportMap R j hj K n
          naturality := by
            intro K L f
            change (compactSupportCohomologyFunctor R X n).map f ≫
                compactificationCohomologySupportMap R j hj L n =
              compactificationCohomologySupportMap R j hj K n ≫ 𝟙 _
            rw [Category.comp_id]
            have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
            simpa only [hf] using
              compactificationCohomologySupportMap_naturality R j hj K L (leOfHom f) n } }

/-- The colimit comparison evaluates on the same original compact representative. -/
theorem compactSupportCohomologyToCompactification_representative
    (K : Compacts X) (n : ℕ) (a : relativeSingularCohomology R ((K : Set X)ᶜ) n) :
    compactSupportCohomologyToCompactification R j hj n
        (compactSupportCohomologyClass R X K n a) =
      compactificationCohomologySupportMap R j hj K n a := by
  have h : compactSupportCohomologyClass R X K n ≫
      compactSupportCohomologyToCompactification R j hj n =
      compactificationCohomologySupportMap R j hj K n := colimit.ι_desc _ K
  exact congrArg (fun f ↦ f a) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cofinal cohomological neighborhood equivalences make this actual comparison bijective. -/
theorem compactSupportCohomologyToCompactification_bijective
    (h : ∀ K : Compacts X, ∃ L : Compacts X, K ≤ L ∧
      ∀ k : ℕ, IsIso (singularCohomologyPullback R
        (compactificationComplementInclusion j L) k)) (n : ℕ) :
    Function.Bijective (compactSupportCohomologyToCompactification R j hj n) := by
  have hleg (K : Compacts X)
      (hK : ∀ k : ℕ, IsIso (singularCohomologyPullback R
        (compactificationComplementInclusion j K) k)) :
      Function.Bijective (compactificationCohomologySupportMap R j hj K n) := by
    have hAK : ((Set.range j)ᶜ : Set Z) ⊆ (openEmbeddingCompactImage j K : Set Z)ᶜ := by
      rintro z hz ⟨x, _, rfl⟩
      exact hz ⟨x, rfl⟩
    let : IsIso (relativeSingularCohomologyRestriction R _ _ hAK n) :=
      isIso_relativeSingularCohomologyRestriction_of_isIso_inclusion R hAK hK n
    let := isIso_openEmbeddingCohomologySupportPullback R j hj K n
    have : IsIso (compactificationCohomologySupportMap R j hj K n) := by
      change IsIso ((asIso (openEmbeddingCohomologySupportPullback R j hj K n)).inv ≫
        relativeSingularCohomologyRestriction R _ _ hAK n)
      infer_instance
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  constructor
  · -- Compare the same two representatives after enlarging both supports to one valid control.
    intro a b hab
    obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X n a
    obtain ⟨L, β, rfl⟩ := compactSupportCohomology_exists_representative R X n b
    obtain ⟨N, hN, hcohom⟩ := h (K ⊔ L)
    have hK : K ≤ N := le_sup_left.trans hN
    have hL : L ≤ N := le_sup_right.trans hN
    apply (compactSupportCohomologyClass_eq_iff R X α β).mpr
    refine ⟨N, hK, hL, ?_⟩
    apply (hleg N hcohom).injective
    have hα := congrArg (fun f ↦ f α)
      (compactificationCohomologySupportMap_naturality R j hj K N hK n)
    have hβ := congrArg (fun f ↦ f β)
      (compactificationCohomologySupportMap_naturality R j hj L N hL n)
    rw [compactSupportCohomologyToCompactification_representative,
      compactSupportCohomologyToCompactification_representative] at hab
    exact hα.trans (hab.trans hβ.symm)
  · -- A single cofinal control supplies a representative for every target relative class.
    intro a
    obtain ⟨K, _, hK⟩ := h ⊥
    obtain ⟨b, hb⟩ := (hleg K hK).surjective a
    refine ⟨compactSupportCohomologyClass R X K n b, ?_⟩
    rw [compactSupportCohomologyToCompactification_representative]
    exact hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified relative extension preserves the action of an actual ambient class. -/
theorem compactSupportCohomologyToCompactification_action (p q : ℕ)
    (a : singularCohomology R Z p) (b : compactSupportCohomology R X q) :
    compactSupportCohomologyToCompactification R j hj (p + q)
        (compactSupportCohomologyAction R X p q (singularCohomologyPullback R j p a) b) =
      relativeSingularCohomologyAction R ((Set.range j)ᶜ) p q a
        (compactSupportCohomologyToCompactification R j hj q b) := by
  obtain ⟨K, β, rfl⟩ := compactSupportCohomology_exists_representative R X q b
  let A : Set Z := (Set.range j)ᶜ
  let B : Set Z := (openEmbeddingCompactImage j K : Set Z)ᶜ
  have hAB : A ⊆ B := by
    rintro z hz ⟨x, _, rfl⟩
    exact hz ⟨x, rfl⟩
  let P (n : ℕ) := openEmbeddingCohomologySupportPullback R j hj K n
  let inst (n : ℕ) : IsIso (P n) :=
    isIso_openEmbeddingCohomologySupportPullback R j hj K n
  let γ := (asIso (P q)).inv β
  have hγ : P q γ = β := (asIso (P q)).inv_hom_id_apply β
  -- Naturality identifies the product before inverting this very excision map.
  have hproduct : (asIso (P (p + q))).inv
      (relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q
        (singularCohomologyPullback R j p a) β) =
      relativeSingularCohomologyAction R B p q a γ := by
    apply (ConcreteCategory.isIso_iff_bijective (P (p + q))).mp inferInstance |>.injective
    refine ((asIso (P (p + q))).inv_hom_id_apply _).trans ?_
    have hnat := relativeSingularCohomologyPullback_action R j
      (show Set.MapsTo j ((K : Set X)ᶜ) B from by
        rintro x hx ⟨y, hy, hyx⟩
        exact hx ((hj.injective hyx) ▸ hy)) p q a γ
    change P (p + q) (relativeSingularCohomologyAction R B p q a γ) =
      relativeSingularCohomologyAction R ((K : Set X)ᶜ) p q
        (singularCohomologyPullback R j p a) (P q γ) at hnat
    rw [hγ] at hnat
    exact hnat.symm
  rw [compactSupportCohomologyAction_representative,
    compactSupportCohomologyToCompactification_representative,
    compactSupportCohomologyToCompactification_representative]
  change relativeSingularCohomologyRestriction R A B hAB (p + q)
    ((asIso (P (p + q))).inv _) =
      relativeSingularCohomologyAction R A p q a
        (relativeSingularCohomologyRestriction R A B hAB q γ)
  rw [hproduct]
  -- Restrict the relative condition only after the ordered product has been compared.
  have hnat := relativeSingularCohomologyPullback_action R (ContinuousMap.id Z)
    (show Set.MapsTo (ContinuousMap.id Z) A B from fun _ hx ↦ hAB hx) p q a γ
  have hid : singularCohomologyPullback R (ContinuousMap.id Z) p a = a := by
    change (singularCohomologyFunctor R p).map (𝟙 _) a = a
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at hnat
  exact hnat

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A continuous map of the specified compactifications preserves the original relative lift. -/
theorem compactSupportCohomologyToCompactification_naturality
    {W : Type u} [TopologicalSpace W] [T2Space W]
    (k : C(X, W)) (hk : IsOpenEmbedding k) (f : C(Z, W))
    (hcomm : f.comp j = k) (hf : Set.MapsTo f ((Set.range j)ᶜ) ((Set.range k)ᶜ))
    (n : ℕ) (a : compactSupportCohomology R X n) :
    relativeSingularCohomologyPullback R f hf n
        (compactSupportCohomologyToCompactification R k hk n a) =
      compactSupportCohomologyToCompactification R j hj n a := by
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X n a
  let AZ : Set Z := (Set.range j)ᶜ
  let AW : Set W := (Set.range k)ᶜ
  let BZ : Set Z := (openEmbeddingCompactImage j K : Set Z)ᶜ
  let BW : Set W := (openEmbeddingCompactImage k K : Set W)ᶜ
  have hZ : AZ ⊆ BZ := by
    rintro z hz ⟨x, _, rfl⟩
    exact hz ⟨x, rfl⟩
  have hW : AW ⊆ BW := by
    rintro z hz ⟨x, _, rfl⟩
    exact hz ⟨x, rfl⟩
  have hfK : Set.MapsTo f BZ BW := by
    intro z hz himage
    obtain ⟨x, hx, hfx⟩ := himage
    by_cases hrange : z ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hrange
      have hxy : x = y := hk.injective
        (hfx.trans (congrArg (fun g ↦ g y) hcomm))
      subst y
      exact hz ⟨x, hx, rfl⟩
    · exact hf hrange ⟨x, hfx⟩
  let PJ := openEmbeddingCohomologySupportPullback R j hj K n
  let PK := openEmbeddingCohomologySupportPullback R k hk K n
  let F := relativeSingularCohomologyPullback R f hfK n
  let : IsIso PJ := isIso_openEmbeddingCohomologySupportPullback R j hj K n
  let : IsIso PK := isIso_openEmbeddingCohomologySupportPullback R k hk K n
  -- The map of compactifications is the identity on the same original open space.
  have hsquare : F ≫ PJ = PK := by
    dsimp only [F, PJ, PK, openEmbeddingCohomologySupportPullback]
    rw [← relativeSingularCohomologyPullback_comp]
    subst k
    rfl
  have hα : F ((asIso PK).inv α) = (asIso PJ).inv α := by
    apply (ConcreteCategory.isIso_iff_bijective PJ).mp inferInstance |>.injective
    have h := congrArg (fun g ↦ g ((asIso PK).inv α)) hsquare
    exact h.trans ((asIso PK).inv_hom_id_apply α) |>.trans
      ((asIso PJ).inv_hom_id_apply α).symm
  -- Restricting to the boundary commutes with the same ambient pair map.
  have hrestrict := relativeSingularCohomologyPullback_restriction R f hZ hW hf hfK n
  rw [compactSupportCohomologyToCompactification_representative,
    compactSupportCohomologyToCompactification_representative]
  change relativeSingularCohomologyPullback R f hf n
    (relativeSingularCohomologyRestriction R AW BW hW n ((asIso PK).inv α)) =
      relativeSingularCohomologyRestriction R AZ BZ hZ n ((asIso PJ).inv α)
  have h := congrArg (fun g ↦ g ((asIso PK).inv α)) hrestrict
  change _ = relativeSingularCohomologyRestriction R AZ BZ hZ n (F ((asIso PK).inv α)) at h
  exact h.trans (congrArg (relativeSingularCohomologyRestriction R AZ BZ hZ n) hα)

end Compactification

end AtiyahSinger
