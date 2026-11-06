/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportedCohomologyThom

/-!
# Relative support naturality of the specified Thom product

Public module ID: M2205.

Enlargement of a compact base support commutes with the original supported Thom
map before passage to compact-support colimits. This is the relative cup
naturality square on the same projection and the same global Thom class.
It exposes the relative square already used inside the original colimit
naturality proof, which alone cannot recover a relative equality.

Source: relative cup naturality, Hatcher, Algebraic Topology, Section 3.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits TopologicalSpace

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  [T2Space X] (E : X → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

set_option backward.isDefEq.respectTransparency false in
/-- The actual relative Thom maps commute with the original support restrictions. -/
theorem supportedCohomologyThomMap_restriction_naturality
    (K L : Compacts X) (hKL : K ≤ L) (p : ℕ) :
    (compactSupportCohomologyFunctor R X p).map (homOfLE hKL) ≫
        supportedCohomologyThomMap R r E o L p =
      supportedCohomologyThomMap R r E o K p ≫
        (compactSupportCohomologyFunctor R
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)).map
          (homOfLE (show supportedCohomologyThomSupport r E K ≤
            supportedCohomologyThomSupport r E L from Set.image_mono hKL)) := by
  /- Compare projection pullback and the two-relative product before transporting
  their union complements to the original zero-section support complements. -/
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
  let B := (bundleProjection r E) ⁻¹' ((L : Set X)ᶜ)
  let N := bundleNonzero r E
  let ZK := supportedCohomologyThomSupport r E K
  let ZL := supportedCohomologyThomSupport r E L
  have hZ : ZK ≤ ZL := by
    change (bundleZeroSection r E) '' (K : Set X) ⊆
      (bundleZeroSection r E) '' (L : Set X)
    exact Set.image_mono hKL
  have hBA : B ⊆ A := Set.preimage_mono (Set.compl_subset_compl.mpr hKL)
  have hU : B ∪ N ⊆ A ∪ N := Set.union_subset_union_left N hBA
  have hK := supportedCohomologyThomSupport_compl r E K
  have hL := supportedCohomologyThomSupport_compl r E L
  have hoK := isOpen_supportedCohomologyThomSubspaces r E K
  have hoL := isOpen_supportedCohomologyThomSubspaces r E L
  -- Equality of the original support complements is transported by their actual restriction maps.
  have hcast (S S' : Set T) (h : S = S') (j : ℕ) :
      (eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C j) h)).hom =
        relativeSingularCohomologyRestriction R S' S h.symm.le j := by
    subst S'
    change 𝟙 _ = (relativeSingularCohomologyFunctor R T j).map (𝟙 (Opposite.op S))
    exact ((relativeSingularCohomologyFunctor R T j).map_id _).symm
  have htransport :
      relativeSingularCohomologyRestriction R (B ∪ N) (A ∪ N) hU (p + r) ≫
          (eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hL)).hom =
        (eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hK)).hom ≫
          relativeSingularCohomologyRestriction R ((ZL : Set T)ᶜ) ((ZK : Set T)ᶜ)
            (Set.compl_subset_compl.mpr hZ) (p + r) := by
    rw [hcast _ _ hL (p + r), hcast _ _ hK (p + r)]
    dsimp only [T]
    unfold relativeSingularCohomologyRestriction
    simp only [← CategoryTheory.Functor.map_comp]
    rfl
  -- Naturality of the projection and the two-relative product uses the same Thom class.
  have hstep : (compactSupportCohomologyFunctor R X p).map (homOfLE hKL) ≫
        supportedCohomologyThomMap R r E o L p =
      supportedCohomologyThomMap R r E o K p ≫
        (compactSupportCohomologyFunctor R T (p + r)).map (homOfLE hZ) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hpr := congrArg (fun f ↦ f a)
      (relativeSingularCohomologyPullback_restriction R (bundleProjection r E)
        hBA (Set.compl_subset_compl.mpr hKL) (fun _ hx ↦ hx) (fun _ hx ↦ hx) p)
    have hc := relativeSingularCohomologyPullback_unionCup R (ContinuousMap.id T)
      hoL.1 hoL.2 hoK.1 hoK.2 hBA (fun _ hx ↦ hx) p r
      (relativeSingularCohomologyPullback R (bundleProjection r E)
        (show Set.MapsTo (bundleProjection r E) A ((K : Set X)ᶜ) from fun _ hx ↦ hx) p a)
      (cohomologyThomClass R r E o)
    have hid : relativeSingularCohomologyPullback R (ContinuousMap.id T)
        (show Set.MapsTo (ContinuousMap.id T) N N from fun _ hx ↦ hx) r = 𝟙 _ := by
      change (relativeSingularCohomologyFunctor R T r).map (𝟙 (Opposite.op N)) = _
      exact (relativeSingularCohomologyFunctor R T r).map_id _
    rw [hid] at hc
    change _ = relativeSingularCohomologyUnionCup R B N hoL.1 hoL.2 p r
      (relativeSingularCohomologyRestriction R B A hBA p
        (relativeSingularCohomologyPullback R (bundleProjection r E)
          (fun _ hx ↦ hx) p a)) (cohomologyThomClass R r E o) at hc
    change relativeSingularCohomologyPullback R (bundleProjection r E) (fun _ hx ↦ hx) p
        (relativeSingularCohomologyRestriction R ((L : Set X)ᶜ) ((K : Set X)ᶜ)
          (Set.compl_subset_compl.mpr hKL) p a) =
      relativeSingularCohomologyRestriction R B A hBA p
        (relativeSingularCohomologyPullback R (bundleProjection r E) (fun _ hx ↦ hx) p a) at hpr
    change (eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hL)).hom
        (relativeSingularCohomologyUnionCup R B N hoL.1 hoL.2 p r
          (relativeSingularCohomologyPullback R (bundleProjection r E)
            (show Set.MapsTo (bundleProjection r E) B ((L : Set X)ᶜ) from fun _ hx ↦ hx) p
            (relativeSingularCohomologyRestriction R ((L : Set X)ᶜ) ((K : Set X)ᶜ)
              (Set.compl_subset_compl.mpr hKL) p a)) (cohomologyThomClass R r E o)) =
      relativeSingularCohomologyRestriction R ((ZL : Set T)ᶜ) ((ZK : Set T)ᶜ)
        (Set.compl_subset_compl.mpr hZ) (p + r)
        ((eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hK)).hom
          (relativeSingularCohomologyUnionCup R A N hoK.1 hoK.2 p r
            (relativeSingularCohomologyPullback R (bundleProjection r E)
              (fun _ hx ↦ hx) p a) (cohomologyThomClass R r E o)))
    dsimp only [A, B, N, T] at hpr hc ⊢
    erw [hpr, ← hc]
    exact congrArg (fun f ↦ f
      (relativeSingularCohomologyUnionCup R A N hoK.1 hoK.2 p r
        (relativeSingularCohomologyPullback R (bundleProjection r E)
          (fun _ hx ↦ hx) p a) (cohomologyThomClass R r E o))) htransport
  exact hstep

end AtiyahSinger
