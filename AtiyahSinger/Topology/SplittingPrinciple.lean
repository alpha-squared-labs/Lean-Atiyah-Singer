/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagSplitting
public import AtiyahSinger.Topology.HermitianFlagTowerCohomology
public import AtiyahSinger.Topology.HermitianProjectiveBundleCohomology
public import AtiyahSinger.Topology.SingularCohomologyCup

/-!
# Cohomological injectivity of the actual complete flag projection

Public module ID: M2182.

C01: SG III.11 Proposition 11.1 and Appendix C.14, with Hatcher's
Vector Bundles and K-Theory Proposition 3.3 and Algebraic Topology
Theorem 4D.1 supplying the topological splitting and Leray-Hirsch route.

The projection here is the original projection from the concrete space
of ordered orthogonal rank-one projections in each original fiber.
Its tautological line bundles and actual summation splitting were
constructed in HermitianFlagSplitting. The theorem below compares
exactly that map with the original singular cohomology pullback.

The degree and coefficient ring are arbitrary. There is no nonempty,
positive-rank, compactness or characteristic-zero hypothesis. A fixed
continuous Hermitian metric is explicit; existence of such a metric
over paracompact Hausdorff bases is a separate existing theorem.

This is the continuous fixed-rank input for the smooth and locally
varying-rank versions. The proof uses the actual orthogonal-complement
tower and the original projective bundle theorem, including its open-cover
descent over arbitrary bases. The same-universe presentation of base and
fibers matches the current singular pullback API; it is bookkeeping,
not a dimension restriction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
  (r : ℕ) (E : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianFlagTopology

/-- The original complete-flag projection is injective on singular cohomology in every degree. -/
theorem hermitianFlagProjection_cohomology_injective (n : ℕ) :
    Function.Injective (singularCohomologyPullback R (hermitianFlagProjection r E h) n) := by
  /- The projective bundle theorem identifies pullback with its degree-zero
  unit summand at each positive rank. The flag induction uses the literal
  kernel of the chosen first projector, its restricted original metric,
  and the actual assembly map over the same original base. At rank zero,
  the empty projection family supplies a continuous section directly. -/
  refine hermitianFlagProjection_cohomology_injective_of_projective R n ?_ r E h
  intro s Y tY F hnorm hspace tF fb vb hF
  exact hermitianProjectiveProjection_cohomology_injective R (s + 1) F hF
    (Nat.succ_pos s) n

end AtiyahSinger.ComplexBundle
