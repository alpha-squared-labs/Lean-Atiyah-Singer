/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThom
public import AtiyahSinger.Topology.CompactSupportCohomology
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup
public import AtiyahSinger.Topology.RelativeSingularFunctoriality

/-!
# Thom multiplication on each original compact support

Public module ID: M2204.

For a compact subset K of the base, its image under the original zero
section is compact in the original bundle total space. Pulling an actual
class of H^p(X,X minus K) along the original projection gives a relative
class on the complement of the fibers over K. Its two-relative cup with
the original Thom class lies on the union with the nonzero vectors.
This union is exactly the complement of the same zero-section image.

The resulting actual relative morphism, followed by the original
compact-support colimit injection, is compatible with enlarging K.
This is the cocone needed for the compact-support Thom map on a
possibly noncompact base. The native bundle fibers, topology, specified
cohomological orientation and order pi*(a) cup U all remain fixed.

Sources: Hatcher, Algebraic Topology, section 3.2, for the relative cup
of excisive pairs, section 3.3 for compact supports, and Corollary 4D.9
for Thom multiplication; Milnor--Stasheff, sections 9--10. The explicit
composition on these original support pairs is a project supplement.

Only a Hausdorff base and the original finite-rank native vector bundle
are used. No global continuous fiber norm, metric, compact base, proper
bundle projection or local compactness is assumed. In particular, the
zero-section compact images are not claimed to be cofinal among all
compact subsets of the total space. This file does not assert a global
compact-support Thom isomorphism; that is a separate theorem about the
colimit of these precise maps. Support naturality uses the separately
constructed global Thom class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  [hHausdorff : T2Space X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [hFiber : FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [hVector : VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

/-- The actual compact image of K under the original zero section. -/
def supportedCohomologyThomSupport (K : Compacts X) :
    Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
  K.map (bundleZeroSection r E) (bundleZeroSection r E).continuous

include hHausdorff hFiber hVector in
/-- The two original relative subspaces used by supported Thom multiplication are open. -/
theorem isOpen_supportedCohomologyThomSubspaces (K : Compacts X) :
    IsOpen ((bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)) ∧
      IsOpen (bundleNonzero r E) := by
  /- The compact subset K is closed in the Hausdorff base. Its open
  complement pulls back to an open set under the original continuous
  projection. For the second subspace, use the original native linear
  charts: the zero section is locally the product with {0}, which is
  closed in the real model fiber. Thus its complement is locally open,
  and the chart domains cover the total space. This argument uses
  fiberwise continuity and local triviality, not a continuous global
  norm on the total space or a compactness assumption on the base. -/
  refine ⟨K.isCompact.isClosed.isOpen_compl.preimage (bundleProjection r E).continuous, ?_⟩
  -- A native linear chart detects nonzero vectors in an open neighborhood of each point.
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  let e := trivializationAt (EuclideanSpace ℝ (Fin r)) E z.proj
  have hzBase : z.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ z.proj
  have hzSource : z ∈ e.source := e.mem_source.mpr hzBase
  have hcoords : (e z).2 ≠ 0 := by
    have hformula := congrArg Prod.snd
      (e.apply_eq_prod_continuousLinearEquivAt ℝ z.proj hzBase z.snd)
    rw [hformula]
    intro hzero
    apply hz
    apply (e.continuousLinearEquivAt ℝ z.proj hzBase).injective
    simpa only [map_zero] using hzero
  have hnear := (e.continuousAt hzSource).snd.preimage_mem_nhds
    (isClosed_singleton.isOpen_compl.mem_nhds hcoords)
  filter_upwards [hnear, e.open_source.mem_nhds hzSource] with w hw hwSource
  change w.snd ≠ 0
  intro hzero
  apply hw
  change (e w).2 = 0
  have hformula := congrArg Prod.snd
    (e.apply_eq_prod_continuousLinearEquivAt ℝ w.proj (e.mem_source.mp hwSource) w.snd)
  rw [hformula, hzero, map_zero]


set_option linter.unusedSectionVars false in
/-- The union of the two original relative conditions is exactly the compact-image complement. -/
theorem supportedCohomologyThomSupport_compl (K : Compacts X) :
    ((bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)) ∪ bundleNonzero r E =
      ((supportedCohomologyThomSupport r E K :
        Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) := by
  /- An original vector belongs to the image of K under the zero
  section exactly when its base point belongs to K and the vector
  itself is zero. Negating this conjunction gives precisely the two
  displayed alternatives. Both directions use the same vector and
  its original base projection, with no replacement of the support.
  This set identity also includes empty supports and rank zero. -/
  classical
  ext z
  change z.proj ∉ (K : Set X) ∨ z.snd ≠ 0 ↔
    ¬ ∃ x ∈ (K : Set X), (⟨x, 0⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E) = z
  constructor
  · rintro (hbase | hnonzero) ⟨x, hx, rfl⟩
    · exact hbase hx
    · exact hnonzero rfl
  · intro h
    by_cases hbase : z.proj ∈ (K : Set X)
    · right
      intro hzero
      apply h
      refine ⟨z.proj, hbase, ?_⟩
      cases z
      simp_all
    · exact Or.inl hbase

variable (o : CohomologyOrientation R r E)

/-- Pull back an original supported base class and cup it with the same original Thom class. -/
def supportedCohomologyThomMap (K : Compacts X) (p : ℕ) :
    relativeSingularCohomology R ((K : Set X)ᶜ) p ⟶
      relativeSingularCohomology R
        ((supportedCohomologyThomSupport r E K :
          Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) (p + r) := by
  let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
  let B := bundleNonzero r E
  let hOpen := isOpen_supportedCohomologyThomSubspaces r E K
  -- Pull back on the same projection, with its exact inverse-image relative condition.
  let pullback : relativeSingularCohomology R ((K : Set X)ᶜ) p ⟶
      relativeSingularCohomology R A p :=
    relativeSingularCohomologyPullback R (bundleProjection r E)
      (show Set.MapsTo (bundleProjection r E) A ((K : Set X)ᶜ) from fun _ hx ↦ hx) p
  -- Keep the ordinary base-factor order and the specified original global Thom class.
  let product := (relativeSingularCohomologyUnionCup R A B hOpen.1 hOpen.2 p r).flip
    (cohomologyThomClass R r E o)
  -- Transport only the proved equality of the original relative subspaces.
  let comparison : relativeSingularCohomology R (A ∪ B) (p + r) ≅
      relativeSingularCohomology R
        ((supportedCohomologyThomSupport r E K :
          Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) (p + r) :=
    eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r))
      (supportedCohomologyThomSupport_compl r E K))
  exact pullback ≫ ModuleCat.ofHom product ≫ comparison.hom

set_option backward.isDefEq.respectTransparency false in
/-- Enlarging the base support gives the same original compact-support Thom class. -/
theorem supportedCohomologyThomMap_support_naturality
    (K L : Compacts X) (hKL : K ≤ L) (p : ℕ) :
    (compactSupportCohomologyFunctor R X p).map (homOfLE hKL) ≫
        supportedCohomologyThomMap R r E o L p ≫
        compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
          (supportedCohomologyThomSupport r E L) (p + r) =
      supportedCohomologyThomMap R r E o K p ≫
        compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
          (supportedCohomologyThomSupport r E K) (p + r) := by
  /- Stage 1: the original image of K under the same zero section
  is contained in that of L. Complement inclusion gives the actual
  transition between these two target relative groups. Projection
  pullback commutes with the corresponding base-complement inclusion.
  Stage 2: use two-relative cup naturality for the identity map of
  the original total space. Only the inverse-image base complement
  shrinks; the nonzero complement and the original Thom class remain
  fixed. The two support-complement equalities identify this square
  with the original target transition, not a new support transport.
  Stage 3: compose with the L-th original colimit injection. Its
  cocone identity for the same compact-image inclusion gives exactly
  the displayed equality. No claim that these supports are cofinal
  or that the bundle projection is proper enters this argument. -/
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
  -- The original compact-support cocone identifies the two resulting support representatives.
  rw [← Category.assoc, hstep, Category.assoc]
  exact congrArg (fun f ↦ supportedCohomologyThomMap R r E o K p ≫ f)
    (colimit.w (compactSupportCohomologyFunctor R T (p + r)) (homOfLE hZ))

end AtiyahSinger
