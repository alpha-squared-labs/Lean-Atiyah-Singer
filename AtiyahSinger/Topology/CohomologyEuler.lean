/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThom
public import AtiyahSinger.Topology.CompactSupportCohomology

/-!
# Euler classes, relative fiber integration and the zero section

Public module ID: M1621.

C03 and SL05: Milnor--Stasheff Section 9, Hatcher Vector Bundles and
K-Theory Section 3.2, and SG III.12.1--12.2. The Euler class is the
actual restriction of the specified Thom class along the original zero
section, after the original relative-to-ordinary map. Relative fiber
integration is the inverse of the specified Thom multiplication.

Over a compact base the actual zero-section image is a compact support.
The same relative class therefore defines a genuinely compactly supported
class using the existing colimit injection. The zero-section formula below
uses that map, the same forget-support map, and the same zero section.
No compactness of the whole vector-bundle total space is assumed.

The input is a locally compatible cohomological R-orientation.
GeometricCohomologyOrientation constructs integral orientations from compatible
real frames, and RationalCohomologyOrientation proves rational Thom and Euler
coefficient comparisons. The signed rational Poincare-Gysin comparison is
proved in ThomGysinComparison under its additional manifold hypotheses.
The inverse here is the relative cohomological fiber integral. Integration
of differential forms and noncompact-base support comparisons use different
constructions from the maps defined in this module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Opposite TopologicalSpace

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

/-- The Euler class for the specified cohomological orientation, on the original base. -/
def cohomologyEulerClass : singularCohomology R X r :=
  singularCohomologyPullback R (bundleZeroSection r E) r
    (relativeSingularCohomologyToOrdinary R (bundleNonzero r E) r
      (cohomologyThomClass R r E o))

/-- Relative fiber integration is the inverse of the actual original Thom multiplication. -/
def cohomologyFiberIntegral (p : ℕ) :
    relativeSingularCohomology R (bundleNonzero r E) (p + r) →ₗ[R]
      singularCohomology R X p :=
  (cohomologyThomEquiv R r E o p).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The projection formula for the relative integral, with the original order of cup factors. -/
theorem cohomologyFiberIntegral_projection (p q : ℕ)
    (a : singularCohomology R X p)
    (b : relativeSingularCohomology R (bundleNonzero r E) (q + r)) :
    cohomologyFiberIntegral R r E o (p + q)
        ((eqToIso (by rw [Nat.add_assoc]) :
            relativeSingularCohomology R (bundleNonzero r E) (p + (q + r)) ≅
              relativeSingularCohomology R (bundleNonzero r E) ((p + q) + r)).hom
          (relativeSingularCohomologyAction R (bundleNonzero r E) p (q + r)
            (singularCohomologyPullback R (bundleProjection r E) p a) b)) =
      singularCohomologyCup R X p q a (cohomologyFiberIntegral R r E o q b) := by
  /- Stage 1: use the actual Thom equivalence to write b as pi*(c) cup U,
  with c its displayed relative fiber integral. This uses the same U, the
  same ordinary projection pullback and the same relative action.
  Stage 2: associativity of that action identifies pi*(a) cup b with
  pi*(a cup c) cup U. Ordinary pullback preserves the actual cup product.
  Only reassociation of the degree is needed; no factors are interchanged.
  Stage 3: the inverse of the original Thom equivalence returns a cup c.
  This is the cohomological projection formula. No additional assertion
  about integration of differential forms or noncompact total supports
  is used to define either side. -/
  let c := cohomologyFiberIntegral R r E o q b
  let i : relativeSingularCohomology R (bundleNonzero r E) ((p + q) + r) ≅
      relativeSingularCohomology R (bundleNonzero r E) (p + (q + r)) :=
    eqToIso (by rw [Nat.add_assoc])
  have hb : cohomologyThomMap R r E o q c = b :=
    (cohomologyThomEquiv R r E o q).apply_symm_apply b
  have hproduct : i.hom (cohomologyThomMap R r E o (p + q)
      (singularCohomologyCup R X p q a c)) =
      relativeSingularCohomologyAction R (bundleNonzero r E) p (q + r)
        (singularCohomologyPullback R (bundleProjection r E) p a) b := by
    rw [← hb]
    change i.hom (relativeSingularCohomologyAction R (bundleNonzero r E) (p + q) r
      (singularCohomologyPullback R (bundleProjection r E) (p + q)
        (singularCohomologyCup R X p q a c)) (cohomologyThomClass R r E o)) = _
    rw [singularCohomologyPullback_cup]
    exact relativeSingularCohomologyAction_assoc R (bundleNonzero r E) p q r
      (singularCohomologyPullback R (bundleProjection r E) p a)
      (singularCohomologyPullback R (bundleProjection r E) q c) (cohomologyThomClass R r E o)
  -- Cancel the same Thom equivalence after reassociating, without permuting cup factors.
  let e := cohomologyThomEquiv R r E o (p + q)
  apply e.injective
  change e (e.symm (i.inv _)) = e _
  rw [e.apply_symm_apply, ← hproduct]
  exact congrArg (fun F ↦ F (e (singularCohomologyCup R X p q a c))) i.hom_inv_id

variable [CompactSpace X]

/-- The actual zero-section image, regarded as a compact subset of the original total space. -/
def cohomologyZeroSectionSupport : Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E) where
  carrier := {z | z.snd = 0}
  isCompact' := by
    -- The carrier is exactly the continuous image of the compact base.
    have hzero : Set.range (bundleZeroSection r E) =
        {z : TotalSpace (EuclideanSpace ℝ (Fin r)) E | z.snd = 0} := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        rfl
      · intro hz
        refine ⟨z.proj, ?_⟩
        cases z with
        | mk x v =>
          dsimp at hz ⊢
          exact congrArg
            (fun w : E x ↦ (⟨x, w⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E)) hz.symm
    rw [← hzero]
    exact isCompact_range (bundleZeroSection r E).continuous

/-- The same Thom class in compactly supported cohomology, using the zero-section support. -/
def compactSupportCohomologyThomClass :
    compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) r :=
  compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
    (cohomologyZeroSectionSupport r E) r (cohomologyThomClass R r E o)

/-- The compact-support zero-section pushforward defined by the actual Thom multiplication. -/
def cohomologyZeroSectionPushforward (p : ℕ) :
    singularCohomology R X p →ₗ[R]
      compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r) :=
  (compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
    (cohomologyZeroSectionSupport r E) (p + r)).hom.comp (cohomologyThomMap R r E o p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Zero-section self-intersection, preserving the specified order a cup e. -/
theorem zeroSectionPullback_cohomologyZeroSectionPushforward (p : ℕ)
    (a : singularCohomology R X p) :
    singularCohomologyPullback R (bundleZeroSection r E) (p + r)
        (compactSupportCohomologyToOrdinary R
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
          (cohomologyZeroSectionPushforward R r E o p a)) =
      singularCohomologyCup R X p r a (cohomologyEulerClass R r E o) := by
  /- Stage 1: the compact-support forgetful map composed with the actual
  zero-section support injection is the original relative-to-ordinary map.
  Thus the left side is the zero-section pullback of the ordinary image
  of pi*(a) cup U, for the original Thom class and original relative action.
  Stage 2: compatibility of that action with the relative-to-ordinary
  map gives pi*(a) cup forget(U). Apply ordinary cup naturality to the
  same zero section. Its composite with pi is literally the identity.
  Stage 3: the first factor is a, and the second is cohomologyEulerClass
  by its actual definition. No graded interchange has occurred, so this
  order works in every rank, including odd rank and rank zero. The result
  concerns the constructed compact-support Thom pushforward. The signed
  rational manifold comparison with Poincare-Gysin is in ThomGysinComparison. -/
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let K := cohomologyZeroSectionSupport r E
  have hforget : compactSupportCohomologyClass R T K (p + r) ≫
      compactSupportCohomologyToOrdinary R T (p + r) =
        relativeSingularCohomologyToOrdinary R (bundleNonzero r E) (p + r) :=
    Limits.colimit.ι_desc _ K
  have hforgetValue := congrArg (fun f ↦ f (cohomologyThomMap R r E o p a)) hforget
  change compactSupportCohomologyToOrdinary R T (p + r)
    (compactSupportCohomologyClass R T K (p + r) (cohomologyThomMap R r E o p a)) =
    relativeSingularCohomologyToOrdinary R (bundleNonzero r E) (p + r)
      (cohomologyThomMap R r E o p a) at hforgetValue
  change singularCohomologyPullback R (bundleZeroSection r E) (p + r)
    (compactSupportCohomologyToOrdinary R T (p + r)
      (compactSupportCohomologyClass R T K (p + r) (cohomologyThomMap R r E o p a))) = _
  rw [hforgetValue]
  change singularCohomologyPullback R (bundleZeroSection r E) (p + r)
    (relativeSingularCohomologyToOrdinary R (bundleNonzero r E) (p + r)
      (relativeSingularCohomologyAction R (bundleNonzero r E) p r
        (singularCohomologyPullback R (bundleProjection r E) p a)
        (cohomologyThomClass R r E o))) = _
  rw [relativeSingularCohomologyToOrdinary_action, singularCohomologyPullback_cup]
  -- The original zero section is an actual right inverse of the original bundle projection.
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

/-- In even rank the Euler factor can be placed first without a graded sign. -/
theorem zeroSectionPullback_cohomologyZeroSectionPushforward_of_even
    (hr : Even r) (p : ℕ) (a : singularCohomology R X p) :
    singularCohomologyPullback R (bundleZeroSection r E) (p + r)
        (compactSupportCohomologyToOrdinary R
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
          (cohomologyZeroSectionPushforward R r E o p a)) =
      (eqToIso (by rw [Nat.add_comm r p]) :
          singularCohomology R X (r + p) ≅ singularCohomology R X (p + r)).hom
        (singularCohomologyCup R X r p (cohomologyEulerClass R r E o) a) := by
  /- First use the self-intersection formula with its original order.
  Graded commutativity interchanges the factors with sign (-1)^(p*r).
  Since r is even, p*r is even and this coefficient equals one in R.
  The remaining equality is precisely the canonical degree transport
  shown in the statement. No torsion-free or characteristic-zero
  coefficient condition is needed to remove this even-degree sign. -/
  rw [zeroSectionPullback_cohomologyZeroSectionPushforward]
  let i : singularCohomology R X (p + r) ≅ singularCohomology R X (r + p) :=
    eqToIso (by rw [Nat.add_comm p r])
  have hcomm := singularCohomologyCup_comm R X p r a (cohomologyEulerClass R r E o)
  have hsign : (-1 : R) ^ (p * r) = 1 := (hr.mul_left p).neg_one_pow
  rw [hsign, one_smul] at hcomm
  change singularCohomologyCup R X p r a (cohomologyEulerClass R r E o) = i.inv _
  rw [← hcomm]
  exact (congrArg (fun f ↦ f
    (singularCohomologyCup R X p r a (cohomologyEulerClass R r E o))) i.hom_inv_id).symm

end AtiyahSinger
