/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyNaturality
public import AtiyahSinger.Topology.FiniteCupVanishing
public import AtiyahSinger.Topology.ProjectiveLineCoordinates

/-!
# The projective root relation from actual line coordinates

Public module ID: M2022.

For a family of actual line-valued bundle maps with joint kernel zero, their
nonzero loci on the projective tautological line form a finite open cover.
On the respective open set the tautological line is isomorphic to that same
pulled-back coordinate line. The corresponding difference of first Chern
classes therefore vanishes there, and their product is zero by relative cup.

The coordinate lines need not be orthogonal for the metric defining the
projective bundle. This permits the same splitting to compare constructions
made using different auxiliary metrics.

Source: Hatcher, Vector Bundles and K-Theory, proof of Theorem 3.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual line coordinates with joint kernel zero give
the projective Chern-root product relation. -/
theorem hermitianProjectiveChernRoot_prod_sub_eq_zero {ι : Type*} [Fintype ι]
    (L : ι → X → Type u) [∀ i x, NormedAddCommGroup (L i x)]
    [∀ i x, NormedSpace ℂ (L i x)] [∀ i, TopologicalSpace (TotalSpace Unit (L i))]
    [∀ i, IsFiniteRank (L i)]
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ i : ι, Hom E (L i))
    (hL : ∀ i x, Module.finrank ℂ (L i x) = 1)
    (hdetect : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (x : X) (v : E x), (∀ i, (a i).linearMap x v = 0) → v = 0) :
    ∏ i : ι,
      (singularEvenCohomologyOf ℤ (HermitianProjectiveBundle r E h) 1
          (hermitianProjectiveChernRoot r E h) -
        singularEvenCohomologyPullback ℤ (hermitianProjectiveProjection r E h)
          (singularEvenCohomologyOf ℤ X 1 (firstChernClass (L i) (hL i)))) = 0 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let Q := HermitianProjectiveBundle r E h
  let p := hermitianProjectiveProjection r E h
  let U (i : ι) := hermitianProjectiveCoordinateDomain r E h (a i)
  let b (i : ι) : singularCohomology ℤ Q 2 :=
    hermitianProjectiveChernRoot r E h -
      singularCohomologyPullback ℤ p 2 (firstChernClass (L i) (hL i))
  -- The same coordinate maps supply both the open cover and the local line isomorphisms.
  have hU (i : ι) : IsOpen (U i) := isOpen_hermitianProjectiveCoordinateDomain r E h (a i)
  have hcover : (⋃ i, U i) = Set.univ :=
    iUnion_hermitianProjectiveCoordinateDomain r E h L a hL hdetect
  have hb (i : ι) : singularCohomologyPullback ℤ (ContinuousMap.subtypeVal (U i)) 2
      (b i) = 0 := by
    change singularCohomologyPullback ℤ (ContinuousMap.subtypeVal (U i)) 2
      (hermitianProjectiveChernRoot r E h -
        singularCohomologyPullback ℤ p 2 (firstChernClass (L i) (hL i))) = 0
    rw [map_sub, hermitianProjectiveChernRoot_restrict_coordinate r E h (a i) (hL i)]
    exact sub_self _
  -- Relative cup on this finite cover annihilates the original homogeneous product.
  have hprod := singularEvenCohomologyOf_prod_eq_zero_of_openCover ℤ U hU hcover b hb
  simpa only [b, map_sub, singularEvenCohomologyPullback_of] using hprod

end AtiyahSinger.ComplexBundle
