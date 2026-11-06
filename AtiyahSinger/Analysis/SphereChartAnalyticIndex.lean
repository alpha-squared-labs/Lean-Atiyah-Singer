/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OrthogonalPointIndex
public import AtiyahSinger.Analysis.SphereTangentIndexDimension
public import AtiyahSinger.Topology.ExteriorBottComparison

/-!
# The ordinary index of classes extended through a sphere tangent chart

Public module ID: M1005.

The normalized pole chart sends the original positive exterior Bott class to
the actual pole pushforward. The full equivariant point normalization therefore
evaluates every class extended from this chart by its specified Bott integer.
The statement concerns this open-chart image, not the whole sphere K group.

Source: SG III.13, the embedding proof of Theorem 13.2, with the orthogonal
fixed-point normalization in place of Euler-class cancellation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphereTangent
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option maxHeartbeats 800000 in
-- Keep the original pole quotient, forgetful map and positive exterior Bott coordinates.
/-- The index on the actual sphere-chart image is the specified positive Bott coordinate. -/
theorem tangentAnalyticIndex_sphereTangentChart (r : ℕ) (atInfinity : Bool)
    (μ : Measure (OrthogonalSphere r)) [IsSmoothPositiveMeasure (n := r) μ]
    (u : CompactSupportKZero (EuclideanSpace ℂ (Fin r))) :
    letI : T2Space (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) _
    tangentAnalyticIndex μ
        (compactSupportKZeroOpenPushforward (orthogonalSphereTangentChart r atInfinity)
          (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity) u) =
      bottEuclideanClassEquivInt r
        (compactSupportKZeroHomeomorph (PiLp.homeomorph 2 (fun _ : Fin r ↦ ℂ)) u) := by
  classical
  let : T2Space (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  let : LocallyCompactSpace (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) _
  let := compactSpace_orthogonalGroup r
  let V := EuclideanSpace ℂ (Fin r)
  let b := exteriorBottClass V
  let e := PiLp.homeomorph 2 (fun _ : Fin r ↦ ℂ)
  let κ := (compactSupportKZeroHomeomorphEquiv e).trans (bottEuclideanClassEquivInt r)
  have hb : κ b = 1 := bottEuclideanClassEquivInt_exteriorBottEuclideanClass r
  -- Forget the actual coefficient-one pole class, retaining its exact open chart.
  have hpole : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (orthogonalSpherePolePushforward r atInfinity 1)) =
      compactSupportKZeroOpenPushforward (orthogonalSphereTangentChart r atInfinity)
        (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity) b := by
    change supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportTripleKZeroOpenPushforward (orthogonalSphereTangentChart r atInfinity)
          (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity)
          (orthogonalSphereTangentChart_equivariant r atInfinity)
          ((1 : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) •
            equivariantExteriorBottClass (orthogonalComplexification_unitary r)))) = _
    rw [one_smul, equivariantSupportTripleKZeroOpenPushforward_forget,
      equivariantExteriorBottClass_forget]
  have hunit := representationDimension_orthogonalSphereTangentAnalyticIndex r μ
    (orthogonalSpherePolePushforward r atInfinity 1)
  rw [orthogonalSphereTangentAnalyticIndex_polePushforward,
    (representationDimension_multiplicative _).2, hpole] at hunit
  -- The pre-existing Bott equivalence expresses this arbitrary original class uniquely.
  have hu : u = κ u • b := by
    apply κ.injective
    rw [map_zsmul, hb]
    simp
  change tangentAnalyticIndex μ
      (compactSupportKZeroOpenPushforward (orthogonalSphereTangentChart r atInfinity)
        (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity) u) = κ u
  conv_lhs => rw [hu]
  rw [map_zsmul, map_zsmul, ← hunit]
  simp

end AtiyahSinger
