/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GeometricCohomologyOrientation
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# The geometrically normalized rational Thom self-intersection formula

Public module ID: M1865.

A locally compatible geometric orientation of the original real bundle
determines its normalized integral orientation. Its actual coefficient image
determines the rational Thom class. The original compact-support Thom
pushforward then satisfies the zero-section formula for every rational class.
The Euler factor is the rationalization of the original integral Euler class.

Sources: Hatcher, Vector Bundles and K-Theory, section 3.2, p.88, the Gysin
diagram and Euler multiplication; Algebraic Topology, Corollary 4D.9 and
the preceding coefficient-change discussion; MS Theorem 10.4. The ordinary
class precedes the Thom class, so the result is a cup e in every rank.
In even rank the factors can be interchanged without a graded sign.

The pushforward here is the cohomological Thom map on a compact base,
without manifold hypotheses. SG III.12 also defines a Poincare-duality
Gysin map on manifolds. An identification with that map must compare the
two constructions and their orientation conventions separately.
The proofs specialize the same cohomological orientation and original Euler coefficient map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X] [CompactSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : ∀ x, Orientation ℝ (E x) (Fin r))
  (ho : IsLocallyCompatibleBundleOrientation r E o)

local notation "oℤ" => geometricCohomologyOrientation r E o ho

/-- Geometric rational Thom self-intersection for every rational class, with a cup Euler order. -/
theorem zeroSectionPullback_geometricThomPushforward (p : ℕ)
    (a : singularCohomology ℚ X p) :
    singularCohomologyPullback ℚ (bundleZeroSection r E) (p + r)
        (compactSupportCohomologyToOrdinary ℚ
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
          (cohomologyZeroSectionPushforward ℚ r E (oℤ).rationalization p a)) =
      singularCohomologyCup ℚ X p r a
        (singularCohomologyRationalization X r (cohomologyEulerClass ℤ r E oℤ)) := by
  /- Stage 1: the original positive local frames normalize oℤ. Its
  rationalization supplies the actual rational fiber generators and their
  common local extensions; Thom uniqueness fixes the rational Thom class.
  Stage 2: apply the existing rational-coefficient self-intersection
  theorem to this exact orientation and the arbitrary rational class a.
  The zero-section compact support, forget-support map and zero section
  are the original ones. No lift of a to integral cohomology is assumed.
  Stage 3: cohomologyEulerClass_rationalization identifies the Euler factor
  with the displayed image of the original normalized integral Euler.
  The cup factors remain in their original order, with no sign change. -/
  rw [zeroSectionPullback_cohomologyZeroSectionPushforward,
    cohomologyEulerClass_rationalization]

/-- In even rank, the normalized rational Euler factor may be placed before any rational class. -/
theorem zeroSectionPullback_geometricThomPushforward_of_even (hr : Even r) (p : ℕ)
    (a : singularCohomology ℚ X p) :
    singularCohomologyPullback ℚ (bundleZeroSection r E) (p + r)
        (compactSupportCohomologyToOrdinary ℚ
          (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
          (cohomologyZeroSectionPushforward ℚ r E (oℤ).rationalization p a)) =
      (eqToIso (by rw [Nat.add_comm r p]) :
          singularCohomology ℚ X (r + p) ≅ singularCohomology ℚ X (p + r)).hom
        (singularCohomologyCup ℚ X r p
          (singularCohomologyRationalization X r (cohomologyEulerClass ℤ r E oℤ)) a) := by
  /- Use the same normalized rational orientation in the existing even-rank
  self-intersection theorem. The Euler comparison replaces only its Euler
  factor by the actual integral coefficient image. Graded commutativity
  contributes (-1)^(p*r), which is one since r is even. The explicit degree
  transport changes r+p to p+r; no orientation or support is reselected.
  The rank-zero canonical positive-frame case and empty bases remain valid. -/
  rw [zeroSectionPullback_cohomologyZeroSectionPushforward_of_even ℚ r E
    (oℤ).rationalization hr, cohomologyEulerClass_rationalization]

end AtiyahSinger
