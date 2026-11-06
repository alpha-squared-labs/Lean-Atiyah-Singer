/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanCotangentCoordinates
public import AtiyahSinger.Geometry.SphereMusical
public import AtiyahSinger.Geometry.SphereMusicalPoleCoordinates

/-!
# Cotangent pole charts and the actual round musical map

Public module ID: M1423.

The normalized pole diffeomorphism gives an inverse-dual cotangent chart.
In the specified real Riesz coordinates the round musical tangent chart
is this same cotangent chart after a positive rescaling of the imaginary
fiber. The coefficient is retained explicitly, including dimension zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 30

/-- The inverse-dual pole chart in the original ordered complex Euclidean coordinates. -/
def orthogonalSphereCotangentChart (r : ℕ) (atInfinity : Bool) :
    C(EuclideanSpace ℂ (Fin r), CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
  ⟨fun z ↦ cotangentOpenInclusion (orthogonalSpherePoleOpen r atInfinity)
      (cotangentDiffeomorph (orthogonalSpherePoleDiffeomorph r atInfinity)
        ((euclideanCotangentComplexHomeomorph r).symm z)),
    (isOpenEmbedding_cotangentOpenInclusion (orthogonalSpherePoleOpen r atInfinity)).continuous.comp
      ((cotangentDiffeomorph (orthogonalSpherePoleDiffeomorph r atInfinity)).continuous.comp
        (euclideanCotangentComplexHomeomorph r).symm.continuous)⟩

/-- The same native inverse-dual chart is an open embedding. -/
theorem orthogonalSphereCotangentChart_isOpenEmbedding (r : ℕ) (atInfinity : Bool) :
    Topology.IsOpenEmbedding (orthogonalSphereCotangentChart r atInfinity) :=
  (isOpenEmbedding_cotangentOpenInclusion (orthogonalSpherePoleOpen r atInfinity)).comp
    ((cotangentDiffeomorph (orthogonalSpherePoleDiffeomorph r atInfinity)).isOpenEmbedding.comp
      (euclideanCotangentComplexHomeomorph r).symm.isOpenEmbedding)

set_option maxHeartbeats 1000000 in
-- The inherited open chart has the same derivative as its actual ambient inclusion.
/-- The chart covector is the real Riesz covector composed with the forward pole-chart
derivative at the inverse-chart point. -/
theorem orthogonalSphereCotangentChart_apply (r : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin r)) :
    let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).re)
    let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).im)
    orthogonalSphereCotangentChart r atInfinity z =
      ⟨(orthogonalSphereNormalizedChart r atInfinity).symm u,
        (innerSL ℝ v).comp (mfderiv (𝓡 r) (𝓡 r)
          (orthogonalSphereNormalizedChart r atInfinity)
          ((orthogonalSphereNormalizedChart r atInfinity).symm u))⟩ := by
  let I := 𝓡 r
  let E := EuclideanSpace ℝ (Fin r)
  let U := orthogonalSpherePoleOpen r atInfinity
  have hinclusion (y : U) : mfderiv I I (Subtype.val : U → OrthogonalSphere r) y =
      ContinuousLinearMap.id ℝ E := by
    have hι : MDifferentiableAt (𝓡 r) (𝓡 r) (Subtype.val : U → OrthogonalSphere r) y :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
    have hrep : writtenInExtChartAt (𝓡 r) (𝓡 r) y (Subtype.val : U → OrthogonalSphere r) =ᶠ[
        𝓝 ((extChartAt (𝓡 r) y) y)]
        writtenInExtChartAt (𝓡 r) (𝓡 r) (y : OrthogonalSphere r)
          (id : OrthogonalSphere r → OrthogonalSphere r) := by
      change (fun v ↦ (chartAt (EuclideanSpace ℝ (Fin r)) (y : OrthogonalSphere r))
          (((chartAt (EuclideanSpace ℝ (Fin r)) y).symm v : U) : OrthogonalSphere r)) =ᶠ[
            𝓝 (chartAt (EuclideanSpace ℝ (Fin r)) (y : OrthogonalSphere r) y)]
        (fun v ↦ (chartAt (EuclideanSpace ℝ (Fin r)) (y : OrthogonalSphere r))
          ((chartAt (EuclideanSpace ℝ (Fin r)) (y : OrthogonalSphere r)).symm v))
      exact
        (U.chartAt_subtype_val_symm_eventuallyEq (x := y)).symm.fun_comp
          (chartAt (EuclideanSpace ℝ (Fin r)) (y : OrthogonalSphere r))
    have hD := hrep.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := Set.range (𝓡 r))
    have hid := mfderiv_id (I := 𝓡 r) (x := (y : OrthogonalSphere r))
    rw [mfderiv, ite_eq_left hι]
    change fderivWithin ℝ (writtenInExtChartAt (𝓡 r) (𝓡 r) y
      (Subtype.val : U → OrthogonalSphere r)) (Set.range (𝓡 r)) ((extChartAt (𝓡 r) y) y) = _
    rw [hD]
    simp only [mfderiv, mdifferentiableAt_id, ↓reduceIte] at hid
    change fderivWithin ℝ (writtenInExtChartAt (𝓡 r) (𝓡 r) (y : OrthogonalSphere r)
      (id : OrthogonalSphere r → OrthogonalSphere r)) (Set.range (𝓡 r))
        ((extChartAt (𝓡 r) (y : OrthogonalSphere r)) y) = _ at hid
    exact hid
  let e := orthogonalSphereNormalizedChart r atInfinity
  let f := orthogonalSpherePoleDiffeomorph r atInfinity
  have hD (x : U) : mfderiv (𝓡 r) (𝓡 r) f.symm x =
      mfderiv (𝓡 r) (𝓡 r) e x.val := by
    have he := ((orthogonalSphereNormalizedChart_smooth r atInfinity).1.contMDiffAt
      (e.open_source.mem_nhds x.property)).mdifferentiableAt (by simp)
    have h := mfderiv_comp x he
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    change mfderiv (𝓡 r) (𝓡 r) f.symm x = _ at h
    rw [hinclusion] at h
    change (mfderiv (𝓡 r) (𝓡 r) f.symm x : E →L[ℝ] E) =
      (mfderiv (𝓡 r) (𝓡 r) e x.val : E →L[ℝ] E).comp
        (ContinuousLinearMap.id ℝ E) at h
    exact h.trans (ContinuousLinearMap.comp_id _)
  let u : E := WithLp.toLp 2 (fun i ↦ (z i).re)
  let v : E := WithLp.toLp 2 (fun i ↦ (z i).im)
  have hR : (euclideanCotangentComplexHomeomorph r).symm z =
      (⟨u, innerSL ℝ v⟩ : CotangentTotalSpace (n := r) (M := E)) := rfl
  change cotangentOpenInclusion U (cotangentDiffeomorph f
    ((euclideanCotangentComplexHomeomorph r).symm z)) = _
  rw [hR]
  change (⟨(f u).val, (innerSL ℝ v).comp (mfderiv (𝓡 r) (𝓡 r) f.symm (f u))⟩ :
    CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) = _
  rw [hD]
  rfl

/-- The positive round conformal factor on the full Euclidean base. -/
def orthogonalSpherePoleConformalFactor (r : ℕ) : C(EuclideanSpace ℝ (Fin r), ℝ) :=
  ⟨fun u ↦ 4 / (1 + ‖u‖ ^ 2) ^ 2, continuous_const.div
    ((continuous_const.add (continuous_norm.pow 2)).pow 2)
      (fun u ↦ pow_ne_zero 2 (by positivity))⟩

/-- The round conformal factor is strictly positive, with no dimension restriction. -/
theorem orthogonalSpherePoleConformalFactor_pos (r : ℕ)
    (u : EuclideanSpace ℝ (Fin r)) : 0 < orthogonalSpherePoleConformalFactor r u := by
  change 0 < 4 / (1 + ‖u‖ ^ 2) ^ 2
  positivity

/-- The actual round-metric correction rescales only the imaginary vector coordinate. -/
def orthogonalSpherePoleImaginaryScale (r : ℕ) :
    EuclideanSpace ℂ (Fin r) ≃ₜ EuclideanSpace ℂ (Fin r) :=
  euclideanComplexImaginaryScale r (orthogonalSpherePoleConformalFactor r)
    (orthogonalSpherePoleConformalFactor_pos r)

set_option maxHeartbeats 1000000 in
-- Retain the full native round covector, including its strictly positive scalar coefficient.
/-- Round musical transport factors through the actual inverse-dual cotangent pole chart. -/
theorem orthogonalSphereRoundMetric_flat_tangentChart (r : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin r)) :
    (orthogonalSphereRoundMetric r).flatHomeomorph
        (orthogonalSphereTangentChart r atInfinity z) =
      orthogonalSphereCotangentChart r atInfinity (orthogonalSpherePoleImaginaryScale r z) := by
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).im)
  have hre : (WithLp.toLp 2 (fun i ↦ (orthogonalSpherePoleImaginaryScale r z i).re) :
      EuclideanSpace ℝ (Fin r)) = u := by
    ext i
    rfl
  have him : (WithLp.toLp 2 (fun i ↦ (orthogonalSpherePoleImaginaryScale r z i).im) :
      EuclideanSpace ℝ (Fin r)) = (4 / (1 + ‖u‖ ^ 2) ^ 2) • v := by
    ext i
    rfl
  rw [orthogonalSphereCotangentChart_apply]
  dsimp only
  rw [hre, him]
  change (⟨(orthogonalSphereNormalizedChart r atInfinity).symm u,
    (orthogonalSphereRoundMetric r).inner _
      (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u v)⟩ :
        CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) = _
  congr 1
  rw [orthogonalSphereNormalizedChart_roundFlat, map_smul]
  rfl

/-- The round conformal correction intertwines the same original real matrix action. -/
theorem orthogonalSpherePoleImaginaryScale_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)) :
    orthogonalSpherePoleImaginaryScale r (orthogonalComplexificationRepresentation r A z) =
      orthogonalComplexificationRepresentation r A (orthogonalSpherePoleImaginaryScale r z) := by
  let R := euclideanComplexRealProductHomeomorph r
  let Q := orthogonalEuclideanIsometry r A
  have hcoords (w : EuclideanSpace ℂ (Fin r)) :
      R (orthogonalComplexificationRepresentation r A w) = (Q (R w).1, Q (R w).2) := by
    apply Prod.ext
    · ext i
      change (∑ j, (A.val i j : ℂ) * w j).re = ∑ j, A.val i j * (w j).re
      simp
    · ext i
      change (∑ j, (A.val i j : ℂ) * w j).im = ∑ j, A.val i j * (w j).im
      simp
  have hscale (w : EuclideanSpace ℂ (Fin r)) :
      R (orthogonalSpherePoleImaginaryScale r w) =
        ((R w).1, orthogonalSpherePoleConformalFactor r (R w).1 • (R w).2) :=
    R.apply_symm_apply _
  apply R.injective
  rw [hscale, hcoords, hcoords, hscale]
  change (Q (R z).1, (4 / (1 + ‖Q (R z).1‖ ^ 2) ^ 2) • Q (R z).2) =
    (Q (R z).1, Q ((4 / (1 + ‖(R z).1‖ ^ 2) ^ 2) • (R z).2))
  rw [Q.norm_map, Q.map_smul]

set_option maxHeartbeats 1200000 in
-- Transfer equivariance through the specified musical map and actual positive correction.
/-- The original inverse-dual cotangent pole chart intertwines the native cotangent action. -/
theorem orthogonalSphereCotangentChart_equivariant (r : ℕ) (atInfinity : Bool)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)) :
    orthogonalSphereCotangentChart r atInfinity (orthogonalComplexificationRepresentation r A z) =
      A • orthogonalSphereCotangentChart r atInfinity z := by
  let S := orthogonalSpherePoleImaginaryScale r
  let g := (orthogonalSphereRoundMetric r).flatHomeomorph
  have hg (w : TangentBundle (𝓡 r) (OrthogonalSphere r)) : g (A • w) = A • g w := by
    apply g.symm.injective
    rw [g.symm_apply_apply, orthogonalSphereRoundMetric_flat_symm_equivariant,
      g.symm_apply_apply]
  obtain ⟨w, rfl⟩ := S.surjective z
  rw [← orthogonalSpherePoleImaginaryScale_equivariant,
    ← orthogonalSphereRoundMetric_flat_tangentChart,
    ← orthogonalSphereRoundMetric_flat_tangentChart]
  exact (congrArg g (orthogonalSphereTangentChart_equivariant r atInfinity A w)).trans (hg _)

end AtiyahSinger
