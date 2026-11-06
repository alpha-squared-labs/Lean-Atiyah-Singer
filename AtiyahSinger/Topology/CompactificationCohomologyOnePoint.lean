/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyOrdinary
public import AtiyahSinger.Topology.OnePointCohomology

/-!
# Ordinary comparison with the one-point collapse

Public module ID: M1691.

A map from a specified compactification to the one-point space which is the
identity on the original open space and collapses its boundary compares the
same excision extensions. The result does not assume that forgetting support
is injective. It is used for the actual product collapse in the Chern formula.

Source: naturality of singular relative cohomology and open excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits OnePoint TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A specified collapse compares the supported ordinary class in both compactifications. -/
theorem compactSupportCohomologyOpenExtension_toOrdinary_onePoint
    (R : Type) [CommRing R] {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
    [LocallyCompactSpace X] [T2Space X] [T2Space Z]
    (j : C(X, Z)) (hj : IsOpenEmbedding j) (q : C(Z, OnePoint X))
    (hfinite : ∀ x, q (j x) = (x : OnePoint X))
    (hinfty : ∀ z, z ∉ Set.range j → q z = ∞)
    (n : ℕ) (a : compactSupportCohomology R X n) :
    singularCohomologyPullback R q n
      (relativeSingularCohomologyToOrdinary R ({∞} : Set (OnePoint X)) n
        (compactSupportCohomologyToOnePoint R X n a)) =
    compactSupportCohomologyToOrdinary R Z n
      (compactSupportCohomologyOpenExtension R j hj n a) := by
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X n a
  let B : Set Z := (openEmbeddingCompactImage j K : Set Z)ᶜ
  let C : Set (OnePoint X) := (((↑) : X → OnePoint X) '' (K : Set X))ᶜ
  have hC : ({∞} : Set (OnePoint X)) ⊆ C := by
    rintro z rfl
    exact OnePoint.infty_notMem_image_coe
  have hq : Set.MapsTo q B C := by
    rintro z hz ⟨x, hx, heq⟩
    by_cases h : z ∈ Set.range j
    · obtain ⟨y, rfl⟩ := h
      have hxy : x = y := OnePoint.coe_injective (heq.trans (hfinite y))
      exact hz ⟨x, hx, congrArg j hxy⟩
    · exact OnePoint.coe_ne_infty x (heq.trans (hinfty z h))
  let PJ := openEmbeddingCohomologySupportPullback R j hj K n
  let PK := onePointCohomologySupportPullback R X K n
  let F := relativeSingularCohomologyPullback R q hq n
  let := isIso_openEmbeddingCohomologySupportPullback R j hj K n
  let := isIso_onePointCohomologySupportPullback R X K n
  -- The collapse is exactly the finite inclusion on this original support representative.
  have hsquare : F ≫ PJ = PK := by
    dsimp only [F, PJ, PK, openEmbeddingCohomologySupportPullback,
      onePointCohomologySupportPullback]
    rw [← relativeSingularCohomologyPullback_comp]
    have h : q.comp j = ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩ :=
      ContinuousMap.ext hfinite
    congr 1
  have hα : F ((asIso PK).inv α) = (asIso PJ).inv α := by
    apply (ConcreteCategory.isIso_iff_bijective PJ).mp inferInstance |>.injective
    have h := congrArg (fun f ↦ f ((asIso PK).inv α)) hsquare
    exact h.trans ((asIso PK).inv_hom_id_apply α) |>.trans
      ((asIso PJ).inv_hom_id_apply α).symm
  have hforget {Y Y' : Type u} [TopologicalSpace Y] [TopologicalSpace Y']
      (f : C(Y, Y')) {U : Set Y} {V : Set Y'} (hf : Set.MapsTo f U V)
      (c : relativeSingularCohomology R V n) :
      relativeSingularCohomologyToOrdinary R U n
        (relativeSingularCohomologyPullback R f hf n c) =
      singularCohomologyPullback R f n (relativeSingularCohomologyToOrdinary R V n c) :=
    congrArg (fun t ↦ t c) (relativeSingularCohomologyPullback_toOrdinary R f hf n)
  have hid (c : singularCohomology R (OnePoint X) n) :
      singularCohomologyPullback R (ContinuousMap.id (OnePoint X)) n c = c := by
    change (singularCohomologyFunctor R n).map (𝟙 _) c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hleg (c : relativeSingularCohomology R B n) :
      compactSupportCohomologyToOrdinary R Z n
        (compactSupportCohomologyClass R Z (openEmbeddingCompactImage j K) n c) =
      relativeSingularCohomologyToOrdinary R B n c := by
    have h : compactSupportCohomologyClass R Z (openEmbeddingCompactImage j K) n ≫
        compactSupportCohomologyToOrdinary R Z n =
      relativeSingularCohomologyToOrdinary R B n := colimit.ι_desc _ _
    exact congrArg (fun f ↦ f c) h
  -- Restriction to infinity forgets the same relative condition as the ambient open extension.
  rw [compactSupportCohomologyToOnePoint_representative,
    compactSupportCohomologyOpenExtension_representative]
  change singularCohomologyPullback R q n
    (relativeSingularCohomologyToOrdinary R {∞} n
      (relativeSingularCohomologyPullback R (ContinuousMap.id (OnePoint X)) hC n
        ((asIso PK).inv α))) =
    compactSupportCohomologyToOrdinary R Z n
      (compactSupportCohomologyClass R Z (openEmbeddingCompactImage j K) n ((asIso PJ).inv α))
  rw [hforget, hid, ← hforget q hq, hα, hleg]

end AtiyahSinger
