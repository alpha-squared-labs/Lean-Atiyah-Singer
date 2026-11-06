/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.CompactSupportCohomologyAction

/-!
# Projection formula for the original real bundle Thom inverse

Public module ID: M2039.

The compact-base zero-section map uses the prescribed orientation and its actual
Thom class. Associativity gives the ordered module law, and the inverse of this
same map gives the fiber-integral formula. These statements retain arbitrary
commutative coefficients and the original real total-space topology.

Source: the cup-product construction of the Thom map, Hatcher, Algebraic
Topology, Section 3.3; the specified inverse is used in SG III.12.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

variable (R : Type) [CommRing R] (r : ℕ) {B : Type u}
  [TopologicalSpace B] [CompactSpace B] [T2Space B]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

omit [T2Space B] [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original zero-section Thom map preserves the ordered cohomology action. -/
theorem cohomologyZeroSectionPushforward_cup (p q : ℕ)
    (a : singularCohomology R B p) (b : singularCohomology R B q) :
    (eqToIso (by rw [Nat.add_assoc]) :
        compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) ((p + q) + r) ≅
          compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + (q + r))).hom
      (cohomologyZeroSectionPushforward R r E o (p + q)
        (singularCohomologyCup R B p q a b)) =
      compactSupportCohomologyAction R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) p (q + r)
        (singularCohomologyPullback R (bundleProjection r E) p a)
        (cohomologyZeroSectionPushforward R r E o q b) := by
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let U := compactSupportCohomologyThomClass R r E o
  -- Both factors use the same normalized relative Thom representative at the zero section.
  have hzero (n : ℕ) (c : singularCohomology R B n) :
      cohomologyZeroSectionPushforward R r E o n c =
        compactSupportCohomologyAction R T n r
          (singularCohomologyPullback R (bundleProjection r E) n c) U := by
    dsimp only [U, compactSupportCohomologyThomClass]
    rw [compactSupportCohomologyAction_representative]
    rfl
  rw [hzero, hzero, singularCohomologyPullback_cup]
  exact compactSupportCohomologyAction_assoc R T p q r
    (singularCohomologyPullback R (bundleProjection r E) p a)
    (singularCohomologyPullback R (bundleProjection r E) q b) U

/-- Integration by the specified real Thom inverse satisfies the ordered projection formula. -/
theorem compactSupportCohomologyFiberIntegral_action (p q : ℕ)
    (a : singularCohomology R B p)
    (b : compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (q + r)) :
    compactSupportCohomologyFiberIntegral R r E o (p + q)
      ((eqToIso (by rw [Nat.add_assoc]) :
          compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) ((p + q) + r) ≅
            compactSupportCohomology R
              (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + (q + r))).inv
        (compactSupportCohomologyAction R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) p (q + r)
          (singularCohomologyPullback R (bundleProjection r E) p a) b)) =
      singularCohomologyCup R B p q a (compactSupportCohomologyFiberIntegral R r E o q b) := by
  let e := compactBaseCohomologyThomEquiv R r E o
  -- Represent this same supported class by its unique coefficient under the original Thom map.
  obtain ⟨c, rfl⟩ := (e q).surjective b
  change (e (p + q)).symm
    ((eqToIso (by rw [Nat.add_assoc]) :
        compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) ((p + q) + r) ≅
          compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + (q + r))).inv
      (compactSupportCohomologyAction R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) p (q + r)
        (singularCohomologyPullback R (bundleProjection r E) p a)
        (cohomologyZeroSectionPushforward R r E o q c))) =
    singularCohomologyCup R B p q a ((e q).symm (e q c))
  rw [← cohomologyZeroSectionPushforward_cup, Iso.hom_inv_id_apply]
  exact (e (p + q)).symm_apply_apply _ |>.trans
    (congrArg (singularCohomologyCup R B p q a) ((e q).symm_apply_apply c).symm)

end AtiyahSinger
