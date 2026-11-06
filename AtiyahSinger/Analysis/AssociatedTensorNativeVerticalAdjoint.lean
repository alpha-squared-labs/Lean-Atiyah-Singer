/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalFormalAdjoint
public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Geometry.AssociatedProductDensity

/-!
# The actual native adjoint supplies the associated vertical adjunction

Public module ID: M0187.

For the specified invariant native sphere metrics and density, take the full
native metric formal adjoint of the same equivariant PDO. Its identity-valued
atlas conversion is equivariant and supplies the original sphere integral
adjunction. The already constructed associated vertical maps therefore satisfy
the global adjunction for the actual associated product measure. All smoothing
remainders and independent source and target ranks are retained.

This is a smooth-section formal adjunction, before any closed-domain equality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
  (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (y : OrthogonalSphere r) (u v : F.Fiber y),
      k.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = k.pairing y u v)
  (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (y : OrthogonalSphere r) (u v : F'.Fiber y),
      k'.pairing (g • y) (σ'.linearMap g y u) (σ'.linearMap g y v) = k'.pairing y u v)
  [MeasurableSpace B] [BorelSpace B] [CompactSpace B]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

include hk hk' in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in
-- The extended limit accommodates the native vertical metric-adjoint integral comparison.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same native metric adjoint gives the actual associated vertical integral adjunction. -/
theorem associatedSphereTensorNativeVertical_integral_adjoint
    (μ : Measure B) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    {m : ℝ} (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν m)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hE : ∀ x, InnerProductSpace.Core ℂ (E x)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let QA := Q.toAtlasPseudodifferentialOperator
    let JA := (Q.metricFormalAdjoint k k').toAtlasPseudodifferentialOperator
    ∃ hQA : QA.IsEquivariant IG σ σ' hA hA',
      ∃ hJA : JA.IsEquivariant IG σ' σ hA' hA,
        letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
        letI : TopologicalSpace (TotalSpace Unit T) :=
          tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
        letI : TopologicalSpace (TotalSpace Unit T') :=
          tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
        letI := associatedSphereChartedSpace S
        letI := linearModelChartedSpace
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
        ∀ (l : ContinuousHermitianMetric T) (l' : ContinuousHermitianMetric T'),
          (associatedSphereTensorBundleAtlas (a := a) S E A σ hA).IsSmoothHermitianMetric l →
          (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA').IsSmoothHermitianMetric l' →
          (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F.Fiber y),
            (l.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
              (hE (projection p)).inner u v * k.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F'.Fiber y),
            (l'.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E σ' p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ' p y (v ⊗ₜ[ℂ] t)) =
              (hE (projection p)).inner u v * k'.pairing y s t) →
          ∀ (s : (associatedSphereTensorBundleAtlas (a := a) S E A σ hA).smoothSections)
            (t : (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA').smoothSections),
            (∫ z, (l'.toCore z).inner
                ((associatedSphereTensorVerticalOperator (a := a)
                  S E A σ hA A' σ' hA' QA hQA s).val z) (t.val z)
                    ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
              ∫ z, (l.toCore z).inner (s.val z)
                ((associatedSphereTensorVerticalOperator (a := a)
                  S E A' σ' hA' A σ hA JA hJA t).val z)
                    ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν := by
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
  let J := Q.metricFormalAdjoint k k'
  let QA := Q.toAtlasPseudodifferentialOperator
  let JA := J.toAtlasPseudodifferentialOperator
  have hJ : J.IsEquivariant IG σ' σ hσ' hσ :=
    Q.isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hν hQ
  have hQA : QA.IsEquivariant IG σ σ' hA hA' :=
    (Q.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQ
  have hJA : JA.IsEquivariant IG σ' σ hA' hA :=
    (J.isEquivariant_toAtlas_iff IG σ' σ hσ' hσ).mpr hJ
  refine ⟨hQA, hJA, ?_⟩
  let e := nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber
  let e' := nativeSmoothSectionLinearEquiv (n := r) (r := F'.rank) F'.Fiber
  have hInt (s t : A.smoothSections) :
      Integrable (fun y ↦ (k.toCore y).inner (s.val y) (t.val y)) ν :=
    k.integrable_pairing ν (e s) (e t)
  have hInt' (s t : A'.smoothSections) :
      Integrable (fun y ↦ (k'.toCore y).inner (s.val y) (t.val y)) ν :=
    k'.integrable_pairing ν (e' s) (e' t)
  -- Native-to-atlas conversion preserves every section value, including the complete adjoint.
  have hAdj (s : A.smoothSections) (t : A'.smoothSections) :
      (∫ y, (k'.toCore y).inner ((QA.toLinearMap s).val y) (t.val y) ∂ν) =
        ∫ y, (k.toCore y).inner (s.val y) ((JA.toLinearMap t).val y) ∂ν :=
    Q.isMetricFormalAdjoint_metricFormalAdjoint k k' (e s) (e' t)
  exact associatedSphereTensorVerticalOperator_integral_adjoint (a := a)
    S E A σ hA A' σ' hA' QA JA hQA hJA μ ν hν hE k.toCore k'.toCore hInt hInt' hAdj

end AtiyahSinger
