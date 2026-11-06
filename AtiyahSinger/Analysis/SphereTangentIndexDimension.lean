/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndexDimension
public import AtiyahSinger.Analysis.SphereTangentIndex
public import AtiyahSinger.Analysis.TangentAnalyticIndex

/-!
# Forgetting the sphere tangent index

Public module ID: M1013.

The representation dimension of the full orthogonal sphere index is the
ordinary tangent index on the same forgotten support class. The proof retains
the actual round musical map and reconciles the Borel presentations explicitly.
This comparison supplies the integer fixed-point normalization in T01.

Source: SG III.9 and III.13; the comparison of the same support class is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

set_option maxHeartbeats 800000 in
-- Compare the native actions, round musical transport and the Borel-index adapter together.
/-- Forgetting the full sphere representation gives the ordinary index of the same tangent class. -/
theorem representationDimension_orthogonalSphereTangentAnalyticIndex (r : ℕ)
    (μ : Measure (OrthogonalSphere r)) [IsSmoothPositiveMeasure (n := r) μ]
    (u : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r))) :
    letI : T2Space (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) _
    representationDimension (Matrix.orthogonalGroup (Fin r) ℝ)
        (orthogonalSphereTangentAnalyticIndex r u) =
      tangentAnalyticIndex μ
        (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget u)) := by
  let : T2Space (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  let : LocallyCompactSpace (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
    ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) _
  let := orthogonalGroupChartedSpace r
  let := lieGroup_orthogonalGroup r
  let := compactSpace_orthogonalGroup r
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  -- The intrinsic index uses the same measure space as the supplied density.
  have hmap : orthogonalSphereAnalyticIndex r = equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel r) (G := Matrix.orthogonalGroup (Fin r) ℝ)
      (n := r) (M := OrthogonalSphere r) := by
    simp only [orthogonalSphereAnalyticIndex, id_eq]
    congr 1
    · exact (BorelSpace.measurable_eq (α := OrthogonalSphere r)).symm
    · exact proof_irrel_heq _ _
  have hdimension := DFunLike.congr_fun
    (representationDimension_equivariantAnalyticIndexMap (n := r) (M := OrthogonalSphere r)
      (VG := OrthogonalGroupModel r) (G := Matrix.orthogonalGroup (Fin r) ℝ) μ)
    (orthogonalSphereMusicalKMap r u)
  let g := orthogonalSphereRoundMetric r
  -- Both forgetful maps commute with pullback by this exact inverse musical map.
  have hforget := DFunLike.congr_fun
    (equivariantSupportTripleKZeroForget_pullback
      ⟨g.flatHomeomorph.symm, g.flatHomeomorph.symm.continuous⟩
      (orthogonalSphereRoundMetric_flat_symm_equivariant r)
      g.flatHomeomorph.symm.isProperMap) u
  have hcompact := DFunLike.congr_fun
    (supportTripleKZeroToCompactSupport_pullback
      ⟨g.flatHomeomorph.symm, g.flatHomeomorph.symm.continuous⟩
      g.flatHomeomorph.symm.isProperMap)
    (equivariantSupportTripleKZeroForget u)
  simp only [AddMonoidHom.comp_apply] at hforget hcompact hdimension
  have hmusical : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (orthogonalSphereMusicalKMap r u)) =
      (tangentCotangentKZeroEquiv g)
        (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget u)) := by
    change supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportTripleKZeroPullback
          ⟨g.flatHomeomorph.symm, g.flatHomeomorph.symm.continuous⟩
          (orthogonalSphereRoundMetric_flat_symm_equivariant r)
          g.flatHomeomorph.symm.isProperMap u)) = _
    rw [hforget, hcompact]
    rfl
  rw [orthogonalSphereTangentAnalyticIndex, AddMonoidHom.comp_apply, hmap,
    tangentAnalyticIndex_eq μ g]
  change representationDimension (Matrix.orthogonalGroup (Fin r) ℝ)
      (equivariantAnalyticIndexMap (VG := OrthogonalGroupModel r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (orthogonalSphereMusicalKMap r u)) =
    analyticIndexOfComponents μ (supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (orthogonalSphereMusicalKMap r u))) at hdimension
  rw [hmusical] at hdimension
  exact hdimension

end AtiyahSinger
