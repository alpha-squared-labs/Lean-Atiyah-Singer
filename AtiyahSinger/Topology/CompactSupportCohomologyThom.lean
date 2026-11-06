/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.CompactSupportCohomologyRadialControl
public import AtiyahSinger.Topology.RelativeSupportedCohomologyThom
public import AtiyahSinger.Topology.SupportedCohomologyThom
public import AtiyahSinger.Topology.SupportedCohomologyThomNaturality

/-!
# Thom multiplication on the original compact-support cohomology

Public module ID: M1668.

C03. A representative supported in a compact subset K of the base is pulled
back as a relative class and multiplied by the original Thom class. The two
relative factors give support on the actual zero section over K. The resulting
cocone descends through the original compact-support colimit. The Thom theorem
asserts bijectivity of this precise map, whose inverse is the supported fiber
integral. On a compact base it agrees with the existing zero-section map.

The base need only be Hausdorff for the supported construction; it need not be
compact or locally compact. No continuous global fiber norm is assumed. The
fixed-support proof compares the actual relative cup maps. Compact radial
hulls and positive-dilation Cech descent handle arbitrary total-space compact
controls. Zero-section supports are not asserted to be literally cofinal.

The relative zero-section self-intersection formula requires no compactness
or separation hypothesis. Rank zero retains the specified local unit
orientation, so its Thom map need not be the identity without normalization.

Sources: Hatcher, Algebraic Topology, section 3.2 (relative cup), section 3.3
(compact supports), and Corollary 4D.9 (the specified Thom multiplication);
Milnor--Stasheff, sections 9--10. The general Hausdorff supported assembly is
the supplementary singular-chain argument described below, not a literal
quotation of the CW-pair Kunneth theorem. ThomGysinComparison proves the signed
rational PD-Gysin comparison under its additional manifold hypotheses. The
general Hausdorff bijection and its inverse formulas use the same support cocone.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

section GeneralBundle

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Relative Thom self-intersection on any base, with the original order a cup Euler. -/
theorem zeroSectionPullback_cohomologyThomMap (p : ℕ) (a : singularCohomology R X p) :
    singularCohomologyPullback R (bundleZeroSection r E) (p + r)
        (relativeSingularCohomologyToOrdinary R (bundleNonzero r E) (p + r)
          (cohomologyThomMap R r E o p a)) =
      singularCohomologyCup R X p r a (cohomologyEulerClass R r E o) := by
  /- Stage 1: forgetting the relative condition sends the original
  pi*(a) cup U to the ordinary cup product with the same factors.
  Stage 2: pull back along the actual zero section. Cup naturality and
  pi composed with the zero section equal to the identity leave a as
  the first factor. The second factor is the Euler class by definition.
  No interchange of factors or compact-support claim is used. This is
  the general relative self-intersection statement, including odd rank,
  rank zero and bases that are neither compact nor Hausdorff. -/
  change singularCohomologyPullback R (bundleZeroSection r E) (p + r)
    (relativeSingularCohomologyToOrdinary R (bundleNonzero r E) (p + r)
      (relativeSingularCohomologyAction R (bundleNonzero r E) p r
        (singularCohomologyPullback R (bundleProjection r E) p a)
        (cohomologyThomClass R r E o))) = _
  rw [relativeSingularCohomologyToOrdinary_action, singularCohomologyPullback_cup]
  have hcomp : singularCohomologyPullback R (bundleProjection r E) p ≫
      singularCohomologyPullback R (bundleZeroSection r E) p = 𝟙 _ := by
    let F := singularCohomologyFunctor R p
    change F.map (TopCat.ofHom (bundleProjection r E)).op ≫
      F.map (TopCat.ofHom (bundleZeroSection r E)).op = _
    rw [← F.map_comp, ← op_comp]
    exact F.map_id _
  have hbase := congrArg (fun f ↦ f a) hcomp
  change singularCohomologyPullback R (bundleZeroSection r E) p
    (singularCohomologyPullback R (bundleProjection r E) p a) = a at hbase
  rw [hbase]
  rfl

variable [T2Space X]

/-- The actual compact-support Thom map, descended from the original supported relative maps. -/
def compactSupportCohomologyThomMap (p : ℕ) :
    compactSupportCohomology R X p →ₗ[R]
      compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r) :=
  (colimit.desc (compactSupportCohomologyFunctor R X p)
    { pt := compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
      ι :=
        { app := fun K ↦ supportedCohomologyThomMap R r E o K p ≫
            compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
              (supportedCohomologyThomSupport r E K) (p + r)
          naturality := by
            intro K L f
            change (compactSupportCohomologyFunctor R X p).map f ≫
                (supportedCohomologyThomMap R r E o L p ≫
                  compactSupportCohomologyClass R _
                    (supportedCohomologyThomSupport r E L) (p + r)) =
              (supportedCohomologyThomMap R r E o K p ≫
                compactSupportCohomologyClass R _
                  (supportedCohomologyThomSupport r E K) (p + r)) ≫ 𝟙 _
            rw [Category.comp_id]
            have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
            simpa only [hf] using
              supportedCohomologyThomMap_support_naturality R r E o K L (leOfHom f) p } }).hom

/-- On each original compact support, the global map is exactly the prescribed relative cup map. -/
theorem compactSupportCohomologyThomMap_representative (K : Compacts X) (p : ℕ)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) p) :
    compactSupportCohomologyThomMap R r E o p (compactSupportCohomologyClass R X K p a) =
      compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
        (supportedCohomologyThomSupport r E K) (p + r)
        (supportedCohomologyThomMap R r E o K p a) := by
  /- The defining colimit descent evaluated at its K-th original injection
  is its K-th cocone leg. That leg is the actual relative projection
  pullback, the specified two-relative cup with U, and the injection at
  the same zero-section support. No support representative is replaced. -/
  change (colimit.ι (compactSupportCohomologyFunctor R X p) K ≫
    colimit.desc (compactSupportCohomologyFunctor R X p) _) a = _
  rw [colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Thom multiplication is bijective on total compact supports, also over a noncompact base. -/
theorem compactSupportCohomologyThomMap_bijective (p : ℕ) :
    Function.Bijective (compactSupportCohomologyThomMap R r E o p) := by
  /- The fixed-support theorem concerns the specified pullback and two-relative cup.
  Each total compact control enlarges to a compact radial hull whose original
  restriction from its projected zero support is bijective. Apply these facts to
  both representatives and relations in the actual filtered support colimit. -/
  have hsupp (K : Compacts X) : Function.Bijective (supportedCohomologyThomMap R r E o K p) :=
    supportedCohomologyThomMap_bijective R r E o K p
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let F := compactSupportCohomologyFunctor R X p
  let G := compactSupportCohomologyFunctor R T (p + r)
  constructor
  · -- A relation is detected at a compact control, then at its same radial enlargement.
    intro x y hxy
    obtain ⟨K, a, rfl⟩ := compactSupportCohomology_exists_representative R X p x
    obtain ⟨L, b, rfl⟩ := compactSupportCohomology_exists_representative R X p y
    rw [compactSupportCohomologyThomMap_representative,
      compactSupportCohomologyThomMap_representative] at hxy
    obtain ⟨Q, hKQ, hLQ, hrel⟩ := (compactSupportCohomologyClass_eq_iff R T _ _).mp hxy
    let J := Q.map (bundleProjection r E) (bundleProjection r E).continuous
    have hKJ : K ≤ J := fun x hx ↦
      ⟨bundleZeroSection r E x, hKQ ⟨x, hx, rfl⟩, rfl⟩
    have hLJ : L ≤ J := fun x hx ↦
      ⟨bundleZeroSection r E x, hLQ ⟨x, hx, rfl⟩, rfl⟩
    have hZKJ : supportedCohomologyThomSupport r E K ≤
        supportedCohomologyThomSupport r E J := Set.image_mono hKJ
    have hZLJ : supportedCohomologyThomSupport r E L ≤
        supportedCohomologyThomSupport r E J := Set.image_mono hLJ
    obtain ⟨D, hQD, hZD, hD⟩ :=
      exists_compact_thomSupport_restriction_bijective R r E Q (p + r)
    apply (compactSupportCohomologyClass_eq_iff R X a b).mpr
    refine ⟨J, hKJ, hLJ, ?_⟩
    apply (hsupp J).injective
    apply hD.injective
    have hna := congrArg (fun f ↦ f a)
      (supportedCohomologyThomMap_restriction_naturality R r E o K J hKJ p)
    have hnb := congrArg (fun f ↦ f b)
      (supportedCohomologyThomMap_restriction_naturality R r E o L J hLJ p)
    change supportedCohomologyThomMap R r E o J p (F.map (homOfLE hKJ) a) =
      G.map (homOfLE hZKJ) (supportedCohomologyThomMap R r E o K p a) at hna
    change supportedCohomologyThomMap R r E o J p (F.map (homOfLE hLJ) b) =
      G.map (homOfLE hZLJ) (supportedCohomologyThomMap R r E o L p b) at hnb
    change G.map (homOfLE hZD)
        (supportedCohomologyThomMap R r E o J p (F.map (homOfLE hKJ) a)) =
      G.map (homOfLE hZD)
        (supportedCohomologyThomMap R r E o J p (F.map (homOfLE hLJ) b))
    rw [hna, hnb]
    change (G.map (homOfLE hZKJ) ≫ G.map (homOfLE hZD))
        (supportedCohomologyThomMap R r E o K p a) =
      (G.map (homOfLE hZLJ) ≫ G.map (homOfLE hZD))
        (supportedCohomologyThomMap R r E o L p b)
    have h := congrArg (G.map (homOfLE hQD)) hrel
    change (G.map (homOfLE hKQ) ≫ G.map (homOfLE hQD))
        (supportedCohomologyThomMap R r E o K p a) =
      (G.map (homOfLE hLQ) ≫ G.map (homOfLE hQD))
        (supportedCohomologyThomMap R r E o L p b) at h
    rw [← G.map_comp, ← G.map_comp] at h ⊢
    have hKcomp : homOfLE hZKJ ≫ homOfLE hZD = homOfLE hKQ ≫ homOfLE hQD :=
      Subsingleton.elim _ _
    have hLcomp : homOfLE hZLJ ≫ homOfLE hZD = homOfLE hLQ ≫ homOfLE hQD :=
      Subsingleton.elim _ _
    rw [hKcomp, hLcomp]
    exact h
  · -- Every total compact representative comes from the same zero-support Thom map.
    intro x
    obtain ⟨Q, a, rfl⟩ := compactSupportCohomology_exists_representative R T (p + r) x
    let J := Q.map (bundleProjection r E) (bundleProjection r E).continuous
    obtain ⟨D, hQD, hZD, hD⟩ :=
      exists_compact_thomSupport_restriction_bijective R r E Q (p + r)
    obtain ⟨c, hc⟩ := hD.surjective (G.map (homOfLE hQD) a)
    obtain ⟨b, hb⟩ := (hsupp J).surjective c
    refine ⟨compactSupportCohomologyClass R X J p b, ?_⟩
    rw [compactSupportCohomologyThomMap_representative]
    calc
      compactSupportCohomologyClass R T (supportedCohomologyThomSupport r E J) (p + r)
          (supportedCohomologyThomMap R r E o J p b) =
        compactSupportCohomologyClass R T D (p + r)
          (G.map (homOfLE hZD) (supportedCohomologyThomMap R r E o J p b)) :=
        (congrArg (fun f ↦ f (supportedCohomologyThomMap R r E o J p b))
          (colimit.w G (homOfLE hZD))).symm
      _ = compactSupportCohomologyClass R T D (p + r) (G.map (homOfLE hQD) a) := by
        rw [hb, hc]
      _ = compactSupportCohomologyClass R T Q (p + r) a :=
        congrArg (fun f ↦ f a) (colimit.w G (homOfLE hQD))

/-- The supported Thom equivalence has the actual colimit map as its forward map. -/
def compactSupportCohomologyThomEquiv (p : ℕ) :
    compactSupportCohomology R X p ≃ₗ[R]
      compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r) :=
  LinearEquiv.ofBijective (compactSupportCohomologyThomMap R r E o p)
    (compactSupportCohomologyThomMap_bijective R r E o p)

/-- Integration with total compact support is the inverse of that same supported Thom map. -/
def compactSupportCohomologyThomIntegral (p : ℕ) :
    compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r) →ₗ[R]
      compactSupportCohomology R X p :=
  (compactSupportCohomologyThomEquiv R r E o p).symm.toLinearMap

/-- The supported fiber integral returns the same original base class from its Thom image. -/
theorem compactSupportCohomologyThomIntegral_thomMap (p : ℕ)
    (a : compactSupportCohomology R X p) :
    compactSupportCohomologyThomIntegral R r E o p
        (compactSupportCohomologyThomMap R r E o p a) = a := by
  /- Cancel the inverse of the specified equivalence against its own
  forward map. Both use the same original support cocone and orientation. -/
  exact (compactSupportCohomologyThomEquiv R r E o p).symm_apply_apply a

/-- The supported Thom map recovers every original total-space class from its fiber integral. -/
theorem compactSupportCohomologyThomMap_thomIntegral (p : ℕ)
    (a : compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)) :
    compactSupportCohomologyThomMap R r E o p
        (compactSupportCohomologyThomIntegral R r E o p a) = a := by
  /- The same forward map cancels its own inverse on all original
  compact-support classes; no zero-section representative is assumed. -/
  exact (compactSupportCohomologyThomEquiv R r E o p).apply_symm_apply a

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Over a compact base, this map agrees with the existing original zero-section pushforward. -/
theorem compactSupportCohomologyThomMap_compact [CompactSpace X] (p : ℕ)
    (a : compactSupportCohomology R X p) :
    compactSupportCohomologyThomMap R r E o p a =
      cohomologyZeroSectionPushforward R r E o p
        (compactSupportCohomologyToOrdinary R X p a) := by
  /- Enlarge the zero-section support of an actual representative to the
  whole compact zero section. Restricting its two-relative cup to the
  punctured bundle gives the original ordinary-relative action. The
  original support cocone identifies the two resulting representatives. -/
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R X p a
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
  let N := bundleNonzero r E
  let ZK := supportedCohomologyThomSupport r E K
  let Z := cohomologyZeroSectionSupport r E
  let H := compactSupportCohomologyFunctor R T (p + r)
  have hZ : ZK ≤ Z := by
    rintro z ⟨x, _hx, rfl⟩
    rfl
  have hK := supportedCohomologyThomSupport_compl r E K
  have hopen := isOpen_supportedCohomologyThomSubspaces r E K
  -- The equality transport to the support complement is its original restriction map.
  have hcast (S S' : Set T) (h : S = S') :
      (eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) h)).hom =
        relativeSingularCohomologyRestriction R S' S h.symm.le (p + r) := by
    subst S'
    change 𝟙 _ = (relativeSingularCohomologyFunctor R T (p + r)).map (𝟙 (op S))
    exact ((relativeSingularCohomologyFunctor R T (p + r)).map_id _).symm
  have htransport :
      (eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hK)).hom ≫
        H.map (homOfLE hZ) =
      relativeSingularCohomologyRestriction R N (A ∪ N) (fun _ hz ↦ Or.inr hz) (p + r) := by
    rw [hcast _ _ hK]
    change (relativeSingularCohomologyFunctor R T (p + r)).map _ ≫
      (relativeSingularCohomologyFunctor R T (p + r)).map _ =
        (relativeSingularCohomologyFunctor R T (p + r)).map _
    rw [← Functor.map_comp]
    rfl
  have hpair : H.map (homOfLE hZ) (supportedCohomologyThomMap R r E o K p b) =
      cohomologyThomMap R r E o p
        (relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) p b) := by
    let z := relativeSingularCohomologyPullback R (bundleProjection r E)
      (show Set.MapsTo (bundleProjection r E) A ((K : Set X)ᶜ) from fun _ hx ↦ hx) p b
    change H.map (homOfLE hZ)
      ((eqToIso (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hK)).hom
        (relativeSingularCohomologyUnionCup R A N hopen.1 hopen.2 p r z
          (cohomologyThomClass R r E o))) = _
    have hvalue := congrArg (fun f ↦ f
      (relativeSingularCohomologyUnionCup R A N hopen.1 hopen.2 p r z
        (cohomologyThomClass R r E o))) htransport
    change H.map (homOfLE hZ) ((eqToIso
      (congrArg (fun C ↦ relativeSingularCohomology R C (p + r)) hK)).hom _) = _ at hvalue
    erw [hvalue, relativeSingularCohomologyUnionCup_restrict_right]
    have h := congrArg (fun f ↦ f b)
      (relativeSingularCohomologyPullback_toOrdinary R (bundleProjection r E)
        (show Set.MapsTo (bundleProjection r E) A ((K : Set X)ᶜ) from fun _ hx ↦ hx) p)
    change relativeSingularCohomologyToOrdinary R A p z =
      singularCohomologyPullback R (bundleProjection r E) p
        (relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) p b) at h
    rw [h]
    rfl
  -- Both colimit injections and the forget-support map are the original cocone legs.
  have hforget : compactSupportCohomologyToOrdinary R X p
      (compactSupportCohomologyClass R X K p b) =
      relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) p b := by
    have hleg : colimit.ι (compactSupportCohomologyFunctor R X p) K ≫
        compactSupportCohomologyToOrdinary R X p =
      relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) p := colimit.ι_desc _ _
    exact congrArg (fun f ↦ f b) hleg
  rw [compactSupportCohomologyThomMap_representative, hforget]
  change compactSupportCohomologyClass R T ZK (p + r) _ =
    compactSupportCohomologyClass R T Z (p + r) _
  calc
    _ = compactSupportCohomologyClass R T Z (p + r)
        (H.map (homOfLE hZ) (supportedCohomologyThomMap R r E o K p b)) :=
      congrArg (fun f ↦ f (supportedCohomologyThomMap R r E o K p b))
        (colimit.w H (homOfLE hZ)).symm
    _ = _ := congrArg (compactSupportCohomologyClass R T Z (p + r)) hpair

end GeneralBundle

end AtiyahSinger
