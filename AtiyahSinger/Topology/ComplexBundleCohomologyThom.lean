/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# Compact-support Thom integration for the original complex bundle

Public module ID: M1694.

C04. The original complex bundle has the canonical real orientation defined
by interleaved complex frames. Its geometrically normalized integral
cohomological orientation is rationalized by the existing actual coefficient
map. The native real Thom map and its inverse use this precise orientation.

The identity-on-vectors nativeModelTotalHomeomorph transfers compact supports
between the native real phantom model and the original Unit total space.
The forward map uses the inverse of this actual colimit pullback equivalence;
the integral uses the original compact-support fiber integral composed with
that pullback. Both endpoints therefore remain the original groups used by
the complex K-theoretic Thom construction. No arbitrary Gysin inverse or
cohomology equivalence is supplied as an assumption.

Sources: Milnor--Stasheff, sections 9, 10 and 14, for Thom classes and the
canonical complex orientation; Lawson--Michelsohn, Spin Geometry, III.12,
for the cohomological Thom inverse in the character comparison. The explicit
transport through the original singular compact-support colimit is a project
adapter. The base is compact Hausdorff and the complex rank is any fixed
natural number, including zero. Independent Poincare-duality and differential
form identifications remain outside this adapter. The inverse identities cancel
these same two specified equivalences.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (r : ℕ)
  (hr : ∀ x : X, Module.finrank ℂ (E x) = r)

/-- The canonically oriented rational Thom map with the original Unit total-space target. -/
def complexCohomologyThomMap (p : ℕ) :
    singularCohomology ℚ X p →ₗ[ℚ]
      compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r) := by
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  letI := h.realNativeFiberBundle r hr
  letI := h.realNativeVectorBundle r hr
  letI := h.realNativeRiemannianBundle r hr
  -- Transfer the original native Thom image along the same identity-on-vectors homeomorphism.
  exact (compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r))))
      (p + 2 * r)).symm.toLinearMap.comp
      (cohomologyZeroSectionPushforward ℚ (2 * r) E
        (h.complexCohomologyOrientation r hr).rationalization p)

/-- Integration is the original compact-support Thom inverse after the actual native pullback. -/
def complexCohomologyFiberIntegral (p : ℕ) :
    compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r) →ₗ[ℚ]
      singularCohomology ℚ X p := by
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  letI := h.realNativeFiberBundle r hr
  letI := h.realNativeVectorBundle r hr
  letI := h.realNativeRiemannianBundle r hr
  -- Pull back the same original compact-support class, then use the specified Thom inverse.
  exact (compactSupportCohomologyFiberIntegral ℚ (2 * r) E
    (h.complexCohomologyOrientation r hr).rationalization p).comp
      (compactSupportCohomologyHomeomorphPullback ℚ
        (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)).hom

/-- The specified integral returns the original base class from its original complex Thom image. -/
theorem complexCohomologyFiberIntegral_thomMap (p : ℕ) (a : singularCohomology ℚ X p) :
    h.complexCohomologyFiberIntegral r hr p (h.complexCohomologyThomMap r hr p a) = a := by
  /- Stage 1: the native pullback in the integral is the forward map
  of the exact homeomorphism equivalence inverted by the Thom map.
  Cancel these two maps on the same native compact-support class.
  Stage 2: compactSupportCohomologyFiberIntegral is the inverse of
  the existing compactBaseCohomologyThomEquiv, whose forward map is
  precisely cohomologyZeroSectionPushforward. Both use the rationalized
  canonical integral orientation of the same original complex bundle.
  Cancel this second pair. No factor order, coefficient, rank, metric,
  support or orientation changes during either cancellation. -/
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let e := compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)
  let t := compactBaseCohomologyThomEquiv ℚ (2 * r) E
    (h.complexCohomologyOrientation r hr).rationalization p
  change t.symm (e (e.symm (t a))) = a
  rw [e.apply_symm_apply, t.symm_apply_apply]

/-- The complex Thom map recovers every original compact-support class from its integral. -/
theorem complexCohomologyThomMap_fiberIntegral (p : ℕ)
    (a : compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r)) :
    h.complexCohomologyThomMap r hr p (h.complexCohomologyFiberIntegral r hr p a) = a := by
  /- First pull a to the native real total space using the actual
  compact-colimit homeomorphism map. The existing compact-base Thom
  equivalence cancels its forward map against its own inverse on this
  exact pulled-back class. Then the inverse homeomorphism equivalence
  cancels the original pullback and returns a. This works for every
  rational compact-support class, with no integral lift or image
  hypothesis. Rank zero uses the same positive empty-frame orientation. -/
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let e := compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)
  let t := compactBaseCohomologyThomEquiv ℚ (2 * r) E
    (h.complexCohomologyOrientation r hr).rationalization p
  change e.symm (t (t.symm (e a))) = a
  rw [t.apply_symm_apply, e.symm_apply_apply]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
