/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyThom
public import AtiyahSinger.Topology.ComplexBundleCohomologyThom

/-!
# Complex Thom integration with compactly supported coefficients

Public module ID: M2208.

C04. The supported real Thom map and its inverse are transported to the
original Unit total space of the same complex bundle. The base is Hausdorff
and may be noncompact. In particular the coefficient class on the base is
compactly supported; no ordinary-to-supported inverse on a noncompact base
is introduced. The forward map and integral use the same Hermitian metric,
fixed complex rank, canonical interleaved complex orientation, rational
coefficient map and identity-on-vectors native total-space homeomorphism.
Rank zero is included.

Sources: Hatcher, Algebraic Topology, section 3.3 and Corollary 4D.9;
Milnor--Stasheff, sections 9--10 and 14; Lawson--Michelsohn, Spin Geometry,
III.12--13. The transport between the native real model and the original
complex bundle total space is a project adapter. The compact-base comparison
identifies this supported map with the existing ordinary-coefficient map.
These constructions do not assert a
noncompact one-point comparison isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (r : ℕ)
  (hr : ∀ x : X, Module.finrank ℂ (E x) = r)

/-- The complex Thom map with compactly supported coefficients on any Hausdorff base. -/
def supportedComplexCohomologyThomMap (p : ℕ) :
    compactSupportCohomology ℚ X p →ₗ[ℚ]
      compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r) := by
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  letI := h.realNativeFiberBundle r hr
  letI := h.realNativeVectorBundle r hr
  -- Apply the actual supported Thom map, then return to the original complex total space.
  exact (compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r))))
      (p + 2 * r)).symm.toLinearMap.comp
      (compactSupportCohomologyThomMap ℚ (2 * r) E
        (h.complexCohomologyOrientation r hr).rationalization p)

/-- The supported complex fiber integral, using the inverse of the same native Thom map. -/
def supportedComplexCohomologyThomIntegral (p : ℕ) :
    compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r) →ₗ[ℚ]
      compactSupportCohomology ℚ X p := by
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  letI := h.realNativeFiberBundle r hr
  letI := h.realNativeVectorBundle r hr
  -- Pull back the same original class before applying the supported native inverse.
  exact (compactSupportCohomologyThomIntegral ℚ (2 * r) E
    (h.complexCohomologyOrientation r hr).rationalization p).comp
      (compactSupportCohomologyHomeomorphPullback ℚ
        (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)).hom

/-- On a compact base the supported complex map is the existing ordinary-coefficient map. -/
theorem supportedComplexCohomologyThomMap_compact [CompactSpace X] (p : ℕ)
    (a : compactSupportCohomology ℚ X p) :
    h.supportedComplexCohomologyThomMap r hr p a =
      h.complexCohomologyThomMap r hr p (compactSupportCohomologyToOrdinary ℚ X p a) := by
  /- Stage 1: install the same h-induced norm, real inner product and
  selected real native bundle charts on the same native total topology.
  The supported map's native factor is compactSupportCohomologyThomMap
  for precisely the rationalization of h.complexCohomologyOrientation.
  Stage 2: use compactSupportCohomologyThomMap_compact on a. Its terminal
  compact support is the full base, and its ordinary comparison is the
  exact compactSupportCohomologyToOrdinary appearing on the right.
  Stage 3: apply the inverse of the same nativeModelTotalHomeomorph
  pullback equivalence to both sides. The resulting equality has the
  original Unit total space as target, with unchanged degree, rank,
  metric, orientation and factor order. No comparison through a one-point
  compactification, independent Gysin map or unrelated inverse is used. -/
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let e := compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)
  change e.symm (compactSupportCohomologyThomMap ℚ (2 * r) E
      (h.complexCohomologyOrientation r hr).rationalization p a) =
    e.symm (cohomologyZeroSectionPushforward ℚ (2 * r) E
      (h.complexCohomologyOrientation r hr).rationalization p
        (compactSupportCohomologyToOrdinary ℚ X p a))
  exact congrArg e.symm (compactSupportCohomologyThomMap_compact ℚ (2 * r) E
    (h.complexCohomologyOrientation r hr).rationalization p a)

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
