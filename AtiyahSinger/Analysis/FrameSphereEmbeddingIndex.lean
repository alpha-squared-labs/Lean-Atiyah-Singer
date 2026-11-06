/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereIndex
public import AtiyahSinger.Analysis.FixedPointAnalyticIndex
public import AtiyahSinger.Analysis.FrameSpherePolePushforward
public import AtiyahSinger.Analysis.TangentAnalyticIndex

/-!
# Analytic index of the original normal sphere zero section

Public module ID: M0640.

The exact geometric comparison identifies the tangent normal pushforward
with the actual south-pole associated twisted product. The sphere-bundle
multiplicativity theorem and the full orthogonal pole normalization then
recover the base index with the original trivial-line coefficient.

This is the zero-section case in SG III.13 Property 2. It retains the supplied
compatible metrics and adapted lift, and does not invoke an embedding-index
or final index theorem. The general embedding reduction and Euclidean model
transport are separate applications.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Function Manifold MeasureTheory Topology
open scoped ContDiff TensorProduct

variable {n : ℕ} (r : ℕ)
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold (𝓡 n) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V (𝓡 n)]
  [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere
  verticalTangentTopology

local notation "BModel" => EuclideanSpace ℝ (Fin n)
local notation "RModel" => EuclideanSpace ℝ (Fin r)
local notation "GO" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle GO P (OrthogonalSphere r)


attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  ComplexBundle.t2Space_totalSpace ComplexBundle.locallyCompactSpace_totalSpace
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  complexifiedNormalPullbackTopology continuousSMul_orthogonalSphereCotangent
  compactSpace_orthogonalGroup

variable [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r))]
  [SecondCountableTopology (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r))]

variable [MeasurableSpace B] [BorelSpace B]

set_option maxSynthPendingDepth 55 in
set_option maxHeartbeats 20000000 in
-- Preserve the same principal quotient, musical map, zero section and normal tube.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual adapted zero-section normal pushforward preserves the analytic index. -/
theorem exists_frameSphere_tangentPushforward_index
    (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]
    (H : letI := continuousSMul_orthogonalFrame r V (𝓡 n)
      let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (g : SmoothTangentMetric (n := n) (M := B))
    (h : letI := continuousSMul_orthogonalFrame r V (𝓡 n)
      let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      ContMDiffRiemannianMetric 𝓘(ℝ, BModel × RModel) ∞ (BModel × RModel)
        (TangentSpace 𝓘(ℝ, BModel × RModel) : Z → Type _)) :
    letI := continuousSMul_orthogonalFrame r V (𝓡 n)
    let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let I := 𝓡 n
    let J := 𝓘(ℝ, BModel × RModel)
    let q := smoothAssociatedSphereProjection S
    let H' : SmoothHorizontalLift q := H
    let h' : ContMDiffRiemannianMetric J ∞ (BModel × RModel) (TangentSpace J : Z → Type _) := h
    let d := (exists_tangentMusical_diffeomorph h').choose
    let eCot := associatedSphereCotangentHomeomorph S H'
    let a := frameSphereStereographic (EB := BModel) r V
    let j : ContMDiffMap I J B Z ∞ :=
      ⟨fun x ↦ a.symm ⟨x, 0⟩,
        (frameSphereStereographic_spec (EB := BModel) r V).2.2.2.2.2.comp
          (contMDiff_zeroSection ℝ V)⟩
    let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := BModel) r V
    letI : T2Space (TangentBundle I B) := (tangentBundle_topology BModel B).1
    letI : LocallyCompactSpace (TangentBundle I B) :=
      ChartedSpace.locallyCompactSpace (BModel × BModel) (TangentBundle I B)
    letI : T2Space (TangentBundle J Z) := (tangentBundle_topology (BModel × RModel) Z).1
    letI : LocallyCompactSpace (TangentBundle J Z) :=
      ChartedSpace.locallyCompactSpace ((BModel × RModel) × (BModel × RModel)) (TangentBundle J Z)
    let hQ := isPrincipalBundle_pullback (G := GO)
      (projection := orthogonalFrameProjection r V) (cotangentProjection (n := n) (M := B))
    letI := associatedBundle_t2Space
      (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
    letI := associatedBundle_locallyCompactSpace
      (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
    letI := eCot.t2Space
    letI := eCot.symm.isOpenEmbedding.locallyCompactSpace
    letI := isFiniteRank_complexifiedNormalPullback j hj.isImmersion
    (∀ (x : Z) (v : TangentSpace I (q x)),
      h'.inner x (H'.lift x v) = (g.inner (q x) v).comp (mfderiv J I q x)) →
    (∀ x : B, H'.lift (j x) = mfderiv I J j x) →
    ∃ K : TangentNormalSplitting j hj,
      ∃ T : TubularNeighborhood (smoothTangentMap j) (isImmersion_smoothTangentMap j hj),
        ∀ (hN : ContinuousHermitianMetric (ComplexifiedNormalPullback j))
          (u : CompactSupportKZero (TangentBundle I B)),
          associatedSphereAnalyticIndex S
            (compactSupportKZeroHomeomorph d.toHomeomorph
              (tangentEmbeddingPushforwardWith j hj K T hN u)) =
            tangentAnalyticIndex μ u := by
  classical
  let := continuousSMul_orthogonalFrame r V (𝓡 n)
  let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓡 n
  let J := 𝓘(ℝ, BModel × RModel)
  let q := smoothAssociatedSphereProjection S
  let d := (exists_tangentMusical_diffeomorph h).choose
  let eCot := associatedSphereCotangentHomeomorph S H
  let a := frameSphereStereographic (EB := BModel) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩,
      (frameSphereStereographic_spec (EB := BModel) r V).2.2.2.2.2.comp
        (contMDiff_zeroSection ℝ V)⟩
  let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := BModel) r V
  let TM := TangentBundle I B
  let TZ := TangentBundle J Z
  let X := CotangentTotalSpace (n := n) (M := B)
  let f := cotangentProjection (n := n) (M := B)
  let : T2Space TM := (tangentBundle_topology BModel B).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (BModel × BModel) TM
  let : T2Space TZ := (tangentBundle_topology (BModel × RModel) Z).1
  let : LocallyCompactSpace TZ :=
    ChartedSpace.locallyCompactSpace ((BModel × RModel) × (BModel × RModel)) TZ
  let hQ := isPrincipalBundle_pullback (G := GO)
    (projection := orthogonalFrameProjection r V) (cotangentProjection (n := n) (M := B))
  let := associatedBundle_t2Space
    (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
  let := associatedBundle_locallyCompactSpace
    (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
  let := eCot.t2Space
  let := eCot.symm.isOpenEmbedding.locallyCompactSpace
  let := isFiniteRank_complexifiedNormalPullback j hj.isImmersion
  dsimp only
  intro hcompat hH
  obtain ⟨K, T, hcomparison⟩ :=
    exists_frameSpherePole_tangentPushforward_comparison r V H g h hcompat hH
  refine ⟨K, T, ?_⟩
  intro hN u
  let v := orthogonalSphereMusicalKMap r (orthogonalSpherePolePushforward r false 1)
  /- Sphere-bundle multiplicativity uses this associated class; lift independence
  changes its realization. -/
  have hindex := analyticIndex_associatedSphereTwistedProduct S μ
    (compactSupportKZeroHomeomorph g.flatHomeomorph u) v
  rw [associatedSphereTwistedProduct_eq_of_horizontalLift S H] at hindex
  change associatedSphereAnalyticIndex S
    (compactSupportKZeroHomeomorph eCot
      (associatedSupportTwistedProduct (G := GO)
        (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) f
        (compactSupportKZeroHomeomorph g.flatHomeomorph u) v)) = _ at hindex
  rw [hcomparison hN u] at hindex
  -- The full O(r) representation is one, hence its actual associated bundle is the trivial line.
  have hv : orthogonalSphereAnalyticIndex r v = 1 :=
    orthogonalSphereTangentAnalyticIndex_polePushforward r false 1
  rw [hv, map_one] at hindex
  change associatedSphereAnalyticIndex S
    (compactSupportKZeroHomeomorph d.toHomeomorph
      (tangentEmbeddingPushforwardWith j hj K T hN u)) =
    analyticIndexOfComponents μ
      (complexKZeroCompactSupportAction f
        (kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1))
        (compactSupportKZeroHomeomorph g.flatHomeomorph u)) at hindex
  rw [complexKZeroCompactSupportAction_one] at hindex
  -- The base musical map is exactly the supplied metric used in the geometric comparison.
  rw [tangentAnalyticIndex_eq μ g]
  exact hindex

end AtiyahSinger
