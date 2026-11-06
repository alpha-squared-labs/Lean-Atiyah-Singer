/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OnePointCohomology
public import AtiyahSinger.Topology.RelativeCohomologyExactness

/-!
# One-point comparison from cofinal contractible neighborhoods of infinity

Public module ID: M1620.

For a compact support whose complement near infinity is contractible, the
original excision leg to the point-relative group is an isomorphism. If such
supports are cofinal, every supported representative can be compared on one
of them, proving bijectivity of the original compact-support colimit map.

This is a criterion requiring actual control near infinity, not a general
claim for locally compact spaces. Compact metric disk bundles provide its
geometric application; the argument itself works over any commutative ring.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits OnePoint TopologicalSpace

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
  [LocallyCompactSpace X] [T2Space X]

/-- A contractible complement of a compact image makes its original one-point leg invertible. -/
theorem isIso_onePointCohomologySupportMap_of_contractible
    (K : Compacts X)
    [ContractibleSpace ((((↑) : X → OnePoint X) '' (K : Set X))ᶜ : Set (OnePoint X))]
    (n : ℕ) : IsIso (onePointCohomologySupportMap R X K n) := by
  let B : Set (OnePoint X) := (((↑) : X → OnePoint X) '' (K : Set X))ᶜ
  have hinfty : (∞ : OnePoint X) ∈ B := OnePoint.infty_notMem_image_coe
  let : IsIso (relativeSingularCohomologyRestriction R ({∞} : Set (OnePoint X)) B
      (Set.singleton_subset_iff.mpr hinfty) n) :=
    isIso_relativeSingularCohomologyRestriction_singleton R B ∞ hinfty n
  let := isIso_onePointCohomologySupportPullback R X K n
  change IsIso ((asIso (onePointCohomologySupportPullback R X K n)).inv ≫
    relativeSingularCohomologyRestriction R {∞} B _ n)
  infer_instance

/-- Cofinal contractible neighborhoods of infinity make the original comparison bijective. -/
theorem compactSupportCohomologyToOnePoint_bijective_of_contractible_complements
    (h : ∀ K : Compacts X, ∃ L : Compacts X, K ≤ L ∧
      ContractibleSpace ((((↑) : X → OnePoint X) '' (L : Set X))ᶜ : Set (OnePoint X))) (n : ℕ) :
    Function.Bijective (compactSupportCohomologyToOnePoint R X n) := by
  have hleg (K : Compacts X)
      (hK : ContractibleSpace ((((↑) : X → OnePoint X) '' (K : Set X))ᶜ : Set (OnePoint X))) :
      Function.Bijective (onePointCohomologySupportMap R X K n) := by
    let := hK
    let := isIso_onePointCohomologySupportMap_of_contractible R K n
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  constructor
  · -- Enlarge both original representatives to one compact support with an invertible leg.
    intro a b hab
    obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X n a
    obtain ⟨L, β, rfl⟩ := compactSupportCohomology_exists_representative R X n b
    obtain ⟨N, hN, hcontract⟩ := h (K ⊔ L)
    have hK : K ≤ N := le_sup_left.trans hN
    have hL : L ≤ N := le_sup_right.trans hN
    apply (compactSupportCohomologyClass_eq_iff R X α β).mpr
    refine ⟨N, hK, hL, ?_⟩
    apply (hleg N hcontract).injective
    have hα := congrArg (fun f ↦ f α)
      (onePointCohomologySupportMap_naturality R X K N hK n)
    have hβ := congrArg (fun f ↦ f β)
      (onePointCohomologySupportMap_naturality R X L N hL n)
    rw [compactSupportCohomologyToOnePoint_representative,
      compactSupportCohomologyToOnePoint_representative] at hab
    exact hα.trans (hab.trans hβ.symm)
  · -- One cofinal support already represents every class in the point-relative target.
    intro a
    obtain ⟨K, _, hK⟩ := h ⊥
    obtain ⟨b, hb⟩ := (hleg K hK).surjective a
    refine ⟨compactSupportCohomologyClass R X K n b, ?_⟩
    rw [compactSupportCohomologyToOnePoint_representative]
    exact hb

end AtiyahSinger
