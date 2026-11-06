/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleInfinityContraction
public import AtiyahSinger.Topology.CofinalOnePointCohomology
public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.OnePointCohomology
public import AtiyahSinger.Topology.ReducedChernCharacter
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Compact-support Chern character on the original real bundle total space

Public module ID: M1573.

For a finite-rank real vector bundle over a compact Hausdorff base, with
the specified continuous native inner products, the actual comparison
from compact-support singular cohomology to the one-point relative pair
is bijective. Compact disk bundles are cofinal among total-space compact
supports. Their complementary neighborhoods of infinity contract radially
to that same point. This is additional geometry, not a general assertion
about locally compact spaces or arbitrary one-point compactifications.

The inverse of this particular comparison sends the reduced Chern
character of the original compact-support K class to compactly supported
rational cohomology on precisely the same total space. Its degree-2k
component uses the already constructed absolute Chern character and
the canonical point-relative lift. No new K theory, cohomology theory,
fiber norm, bundle topology or freely specified comparison is introduced.

Sources: Hatcher, Algebraic Topology, sections 2.1 and 3.3, for excision,
relative cohomology and compact supports; Milnor--Stasheff, section 10,
for the disk-sphere description; Lawson--Michelsohn, Spin Geometry,
III.12, for the compact-support Chern character in the Thom formula.
The explicit comparison through the existing colimit is a project
supplement combining these standard constructions. Rank zero is included:
the total space is then compact and infinity is isolated. The comparison is
proved, and its defining Chern-character comparison and forget-support
identities use precisely this equivalence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory OnePoint

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  [hCompact : CompactSpace X] [hHausdorff : T2Space X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [hVector : VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  [hMetric : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E]

include hCompact hHausdorff hVector hMetric in
/-- The actual one-point comparison is bijective for the original finite-rank bundle total space. -/
theorem compactSupportCohomologyToOnePoint_bundle_bijective (n : ℕ) :
    Function.Bijective
      (compactSupportCohomologyToOnePoint R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) n) := by
  -- Compact supports have bounded norm in the given continuous native metric.
  apply compactSupportCohomologyToOnePoint_bijective_of_contractible_complements R
  intro K
  have hnorm : Continuous
      (fun v : TotalSpace (EuclideanSpace ℝ (Fin r)) E ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
  let a : ℝ := max b 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdisk : IsCompact
      {v : TotalSpace (EuclideanSpace ℝ (Fin r)) E | ‖v.snd‖ ≤ a} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := EuclideanSpace ℝ (Fin r)) (E := E) (K := Set.univ) isCompact_univ a
  let L : TopologicalSpace.Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
    ⟨{v | ‖v.snd‖ ≤ a}, hdisk⟩
  refine ⟨L, ?_, ?_⟩
  · intro v hv
    exact (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
  · -- The same positive-radius disk has a contractible complement at infinity.
    exact contractibleSpace_bundleInfinityNeighborhood (EuclideanSpace ℝ (Fin r)) E a ha


/-- The equivalence whose forward map is the original compact-support colimit comparison. -/
def bundleCompactSupportCohomologyOnePointEquiv (n : ℕ) :
    compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) n ≃ₗ[R]
      relativeSingularCohomology R
        ({∞} : Set (OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E))) n :=
  LinearEquiv.ofBijective
    (compactSupportCohomologyToOnePoint R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) n).hom
    (compactSupportCohomologyToOnePoint_bundle_bijective R r E n)

/-- The reduced Chern character transported through the actual bundle compact-support comparison. -/
def bundleCompactSupportChernCharacterComponent (k : ℕ) :
    CompactSupportKZero (TotalSpace (EuclideanSpace ℝ (Fin r)) E) →+
      compactSupportCohomology ℚ (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (2 * k) :=
  (bundleCompactSupportCohomologyOnePointEquiv ℚ r E (2 * k)).symm.toAddMonoidHom.comp
    (reducedChernCharacterComponent
      (∞ : OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) k)

/-- The character is sent back to the same reduced class in the original one-point relative pair. -/
theorem bundleCompactSupportChernCharacterComponent_toOnePoint (k : ℕ)
    (a : CompactSupportKZero (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) :
    compactSupportCohomologyToOnePoint ℚ (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (2 * k)
        (bundleCompactSupportChernCharacterComponent r E k a) =
      reducedChernCharacterComponent
        (∞ : OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) k a := by
  /- The defining character first takes the original reduced character
  and then applies the inverse of this exact comparison. Cancel that
  inverse by the linear equivalence's apply_symm_apply identity. The
  reduced input class, degree and singleton infinity remain unchanged. -/
  exact (bundleCompactSupportCohomologyOnePointEquiv ℚ r E (2 * k)).apply_symm_apply
    (reducedChernCharacterComponent
      (∞ : OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) k a)

/-- Forgetting support gives the ordinary restriction of the original absolute Chern character. -/
theorem bundleCompactSupportChernCharacterComponent_toOrdinary (k : ℕ)
    (a : CompactSupportKZero (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) :
    compactSupportCohomologyToOrdinary ℚ (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (2 * k)
        (bundleCompactSupportChernCharacterComponent r E k a) =
      singularCohomologyPullback ℚ
        ⟨((↑) : TotalSpace (EuclideanSpace ℝ (Fin r)) E →
            OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E)), OnePoint.continuous_coe⟩
        (2 * k)
        (chernCharacterKZeroComponent
          (OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) k a.val) := by
  /- Stage 1: compactSupportCohomologyToOnePoint_toOrdinary rewrites
  the original forget-support image through the actual comparison.
  The preceding theorem identifies that same relative image with the
  original reduced Chern character, with no choice of representative.
  Stage 2: reducedChernCharacterComponent_toOrdinary identifies the
  point-relative lift with the original absolute character of a.val.
  Pull back along the same inclusion of the original total space into
  its one-point compactification. These two comparisons give exactly
  the stated formula on the original ordinary cohomology group. -/
  rw [← compactSupportCohomologyToOnePoint_toOrdinary ℚ
    (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (2 * k),
    bundleCompactSupportChernCharacterComponent_toOnePoint,
    reducedChernCharacterComponent_toOrdinary]

end AtiyahSinger
