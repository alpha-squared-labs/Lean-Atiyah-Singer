/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCoefficientEllipticity
public import AtiyahSinger.Analysis.AssociatedKernelL2Embedding
public import AtiyahSinger.Analysis.AssociatedKernelMetricAdjoint
public import AtiyahSinger.Analysis.AssociatedTensorNativeVerticalAdjoint
public import AtiyahSinger.Analysis.AssociatedTensorVerticalGreenIdentity
public import AtiyahSinger.Analysis.AssociatedTensorVerticalL2Realization
public import AtiyahSinger.Analysis.AtlasNativeEllipticConjugate
public import AtiyahSinger.Analysis.ClosedJointGreenBound
public import AtiyahSinger.Analysis.EquivariantGreenAtlasData
public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev

/-!
# The original reverse horizontal joint kernel through actual Green maps

Public module ID: M0132.

Use the original native sphere metric adjoint, its actual kernel projection
and Green operator. The original reverse horizontal map is retained through
its integral adjunction and is identified on the same full-kernel evaluation
with the native coefficient metric adjoint. Actual completion embeddings and
vertical extensions then give regularity and closed range of the prescribed
reverse joint graph, in its original vertical-first output order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w w'

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a a' : ℕ} {P : Type u} {B : Type v}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type w) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type w') [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

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
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z
local notation "C" => fun b : B ↦ E b ⊗[ℂ] K b
local notation "C'" => fun b : B ↦ E' b ⊗[ℂ] K b

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 96000000 in
-- The extended limit accommodates the full reverse joint Green maps and closed-range proof.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Actual Green maps identify the original reverse joint kernel and give closed range. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_adjointGreenKernelRealization
    (μ : Measure B) [IsFiniteMeasure μ] [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C₀.baseOperator.IsElliptic)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
    (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (y : Y) (s t : F.Fiber y),
      k.pairing (g • y) (σ.linearMap g y s) (σ.linearMap g y t) = k.pairing y s t)
    (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (y : Y) (s t : F'.Fiber y),
      k'.pairing (g • y) (σ'.linearMap g y s) (σ'.linearMap g y t) = k'.pairing y s t)
    (Qn : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1) (hQn : Qn.IsElliptic)
    (hQng : Qn.IsEquivariant IG σ σ' hσ hσ')
    (L₀ : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L₁ : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (Jbase : SmoothBundlePresentation (n := n) (r := a) E)
    (Jbase' : SmoothBundlePresentation (n := n) (r := a') E')
    (b : Fin Jbase.size → B) (b' : Fin Jbase'.size → B)
    (hJbase : ∀ j, tsupport (Jbase.cutoff j) ⊆ (S.trivialization (b j)).baseSet)
    (hJbase' : ∀ j, tsupport (Jbase'.cutoff j) ⊆ (S.trivialization (b' j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let Q := Qn.toAtlasPseudodifferentialOperator
    let hQ := (Qn.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQng
    let Qa := (Qn.metricFormalAdjoint k k').toAtlasPseudodifferentialOperator
    let hQa := ((Qn.metricFormalAdjoint k k').isEquivariant_toAtlas_iff
      IG σ' σ hσ' hσ).mpr
        (Qn.isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hν hQng)
    ∀ (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Qa.toLinearMap.ker),
      (∀ (g : G) (y : Y) (v : Fin ρ.dimension → ℂ),
        (e (ρ.representation g v)).val.val (g • y) =
          σ'.linearMap g y ((e v).val.val y)) →
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
      letI : TopologicalSpace (TotalSpace Unit U) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
      letI : TopologicalSpace (TotalSpace Unit U') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
      letI : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
      letI : TopologicalSpace (TotalSpace Unit C') := tensorTopology (E := E') (F := K)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI := isManifold_linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
      letI : IsSmoothPositiveMeasure (n := n + r) η :=
        isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      let AU := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
      let AU' := associatedSphereTensorBundleAtlas (a := a') S E' A' σ' hA'
      let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ)
      let AC' := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
        (associatedOrthogonalRepresentationAtlas S ρ)
      let H := C₀.horizontalLift S E A' σ' E' hA'
      let _V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
      let _V' := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A' σ' hA' Q hQ
      let Va := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hA' A σ hA Qa hQa
      let Va' := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hA' A σ hA Qa hQa
      let Pc := C₀.coefficientOperator S E E' ρ
      ∀ (_Γ₀ : AtlasBundlePresentation AT) (_Γ₁ : AtlasBundlePresentation AU)
        (_Γ₂ : AtlasBundlePresentation AT') (_Γ₃ : AtlasBundlePresentation AU')
        (l₀ : ContinuousHermitianMetric T) (l₁ : ContinuousHermitianMetric U)
        (l₂ : ContinuousHermitianMetric T') (l₃ : ContinuousHermitianMetric U')
        (c₀ : ContinuousHermitianMetric C) (c₁ : ContinuousHermitianMetric C')
        (NC₀ NC₁ : SmoothFiniteComplexBundle (n := n) B)
        (N₀ N₁ N₂ N₃ : SmoothFiniteComplexBundle (n := n + r) Z)
        (kC₀ : SmoothHermitianMetric (n := n) (r := NC₀.rank) NC₀.Fiber)
        (kC₁ : SmoothHermitianMetric (n := n) (r := NC₁.rank) NC₁.Fiber)
        (k₀ : SmoothHermitianMetric (n := n + r) (r := N₀.rank) N₀.Fiber)
        (k₁ : SmoothHermitianMetric (n := n + r) (r := N₁.rank) N₁.Fiber)
        (k₂ : SmoothHermitianMetric (n := n + r) (r := N₂.rank) N₂.Fiber)
        (k₃ : SmoothHermitianMetric (n := n + r) (r := N₃.rank) N₃.Fiber),
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₃.rank)) N₃.Fiber
        ∀ (cIso₀ : Iso C NC₀.Fiber) (cIso₁ : Iso C' NC₁.Fiber)
          (tIso₀ : Iso T N₀.Fiber) (tIso₁ : Iso U N₁.Fiber) (tIso₂ : Iso T' N₂.Fiber)
          (tIso₃ : Iso U' N₃.Fiber)
          (heC₀ : IsSmoothAtlasBundleMap AC (nativeSmoothComplexBundleAtlas NC₀.Fiber)
            cIso₀.toHom.linearMap)
          (hiC₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas NC₀.Fiber) AC
            cIso₀.symm.toHom.linearMap)
          (heC₁ : IsSmoothAtlasBundleMap AC' (nativeSmoothComplexBundleAtlas NC₁.Fiber)
            cIso₁.toHom.linearMap)
          (hiC₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas NC₁.Fiber) AC'
            cIso₁.symm.toHom.linearMap)
          (heT₀ : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N₀.Fiber)
            tIso₀.toHom.linearMap)
          (hiT₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀.Fiber) AT
            tIso₀.symm.toHom.linearMap)
          (heT₁ : IsSmoothAtlasBundleMap AU (nativeSmoothComplexBundleAtlas N₁.Fiber)
            tIso₁.toHom.linearMap)
          (hiT₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁.Fiber) AU
            tIso₁.symm.toHom.linearMap)
          (heT₂ : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N₂.Fiber)
            tIso₂.toHom.linearMap)
          (hiT₂ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₂.Fiber) AT'
            tIso₂.symm.toHom.linearMap)
          (heT₃ : IsSmoothAtlasBundleMap AU' (nativeSmoothComplexBundleAtlas N₃.Fiber)
            tIso₃.toHom.linearMap)
          (hiT₃ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₃.Fiber) AU'
            tIso₃.symm.toHom.linearMap),
          AT.IsSmoothHermitianMetric l₀ → AU.IsSmoothHermitianMetric l₁ →
          AT'.IsSmoothHermitianMetric l₂ → AU'.IsSmoothHermitianMetric l₃ →
          (∀ (x : B) (u v : C x),
            kC₀.pairing x (cIso₀.linearEquiv x u) (cIso₀.linearEquiv x v) =
              (c₀.toCore x).inner u v) →
          (∀ (x : B) (u v : C' x),
            kC₁.pairing x (cIso₁.linearEquiv x u) (cIso₁.linearEquiv x v) =
              (c₁.toCore x).inner u v) →
          (∀ (x : Z) (u v : T x),
            k₀.pairing x (tIso₀.linearEquiv x u) (tIso₀.linearEquiv x v) =
              (l₀.toCore x).inner u v) →
          (∀ (x : Z) (u v : U x),
            k₁.pairing x (tIso₁.linearEquiv x u) (tIso₁.linearEquiv x v) =
              (l₁.toCore x).inner u v) →
          (∀ (x : Z) (u v : T' x),
            k₂.pairing x (tIso₂.linearEquiv x u) (tIso₂.linearEquiv x v) =
              (l₂.toCore x).inner u v) →
          (∀ (x : Z) (u v : U' x),
            k₃.pairing x (tIso₃.linearEquiv x u) (tIso₃.linearEquiv x v) =
              (l₃.toCore x).inner u v) →
          (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F.Fiber y),
            (l₀.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
              h.pairing (projection p) u v * k.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E' (projection p)) (s t : F.Fiber y),
            (l₁.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E' σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E' σ p y (v ⊗ₜ[ℂ] t)) =
              h'.pairing (projection p) u v * k.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F'.Fiber y),
            (l₂.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E σ' p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ' p y (v ⊗ₜ[ℂ] t)) =
              h.pairing (projection p) u v * k'.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E' (projection p)) (s t : F'.Fiber y),
            (l₃.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E' σ' p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E' σ' p y (v ⊗ₜ[ℂ] t)) =
              h'.pairing (projection p) u v * k'.pairing y s t) →
          (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
            (c₀.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
              h.pairing (projection p) u v *
                ∫ y, k'.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) →
          (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρ.dimension → ℂ),
            (c₁.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
              h'.pairing (projection p) u v *
                ∫ y, k'.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) →
          ∀ H₁a : AU'.smoothSections →ₗ[ℂ] AT'.smoothSections,
            (∀ u v, (∫ z, (l₃.toCore z).inner ((H u).val z) (v.val z) ∂η) =
              ∫ z, (l₂.toCore z).inner (u.val z) ((H₁a v).val z) ∂η) →
          let S₀ := (atlasSmoothSectionEquiv AC
            (nativeSmoothComplexBundleAtlas NC₀.Fiber) cIso₀ heC₀ hiC₀).trans
              (nativeSmoothSectionLinearEquiv NC₀.Fiber)
          let S₁ := (atlasSmoothSectionEquiv AC'
            (nativeSmoothComplexBundleAtlas NC₁.Fiber) cIso₁ heC₁ hiC₁).trans
              (nativeSmoothSectionLinearEquiv NC₁.Fiber)
          let T₀ := (atlasSmoothSectionEquiv AT
            (nativeSmoothComplexBundleAtlas N₀.Fiber) tIso₀ heT₀ hiT₀).trans
              (nativeSmoothSectionLinearEquiv N₀.Fiber)
          let T₁ := (atlasSmoothSectionEquiv AU
            (nativeSmoothComplexBundleAtlas N₁.Fiber) tIso₁ heT₁ hiT₁).trans
              (nativeSmoothSectionLinearEquiv N₁.Fiber)
          let T₂ := (atlasSmoothSectionEquiv AT'
            (nativeSmoothComplexBundleAtlas N₂.Fiber) tIso₂ heT₂ hiT₂).trans
              (nativeSmoothSectionLinearEquiv N₂.Fiber)
          let T₃ := (atlasSmoothSectionEquiv AU'
            (nativeSmoothComplexBundleAtlas N₃.Fiber) tIso₃ heT₃ hiT₃).trans
              (nativeSmoothSectionLinearEquiv N₃.Fiber)
          let _i₀ := (k₀.smoothToL2 η).comp T₀.toLinearMap
          let i₁ := (k₁.smoothToL2 η).comp T₁.toLinearMap
          let i₂ := (k₂.smoothToL2 η).comp T₂.toLinearMap
          let i₃ := (k₃.smoothToL2 η).comp T₃.toLinearMap
          ∀ R : k₃.L2SectionSpace η →ₗ.[ℂ] (k₁.L2SectionSpace η × k₂.L2SectionSpace η),
            R.graph = (i₃.prod ((i₁.comp Va').prod (i₂.comp H₁a))).range.topologicalClosure →
            ∃ ev : Hom ((πS : Z → B) *ᵖ K) D',
              (∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
                ev.linearMap (associatedBundleMk G P Y p y)
                    (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
                  associatedEquivariantFiberMk S.toIsPrincipalBundle σ' p y rfl ((e v).val.val y)) ∧
              ∃ (Φ : AC.smoothSections ≃ₗ[ℂ] Va.ker) (Ψ : AC'.smoothSections ≃ₗ[ℂ] Va'.ker),
                (∀ u z, (Φ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                (∀ u z, (Ψ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                ∃ Pn : PseudodifferentialOperator (n := n) (r := NC₀.rank) (q := NC₁.rank)
                    NC₀.Fiber NC₁.Fiber μ 1,
                  Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
                  Pn.IsElliptic ∧
                  ∃ κ : (Pn.metricFormalAdjoint kC₀ kC₁).toLinearMap.ker ≃ₗ[ℂ] R.ker,
                    (∀ u, (κ u).val = i₃ (Ψ (S₁.symm u.val)).val) ∧
                    ∃ cBound : ℝ, 0 ≤ cBound ∧
                      (∀ u : R.domain, (u : k₃.L2SectionSpace η) ∈ R.ker.orthogonal →
                        ‖(u : k₃.L2SectionSpace η)‖ ≤ cBound * ‖R u‖) ∧
                      IsClosed (R.toFun.range : Set (k₁.L2SectionSpace η × k₂.L2SectionSpace η)) ∧
                      FiniteDimensional ℂ R.ker := by
  classical
  -- Obtain vertical integral adjunction and ellipticity of the native sphere adjoint.
  have hV₀Data := associatedSphereTensorNativeVertical_integral_adjoint (a := a)
    S E F F' σ σ' hσ hσ' k k' hk hk' μ ν hν Qn hQng h.toCore
  have hV₁Data := associatedSphereTensorNativeVertical_integral_adjoint (a := a')
    S E' F F' σ σ' hσ hσ' k k' hk hk' μ ν hν Qn hQng h'.toCore
  let Qna := Qn.metricFormalAdjoint k k'
  have hQna : Qna.IsElliptic := (Qn.isElliptic_metricFormalAdjoint_iff k k').mpr hQn
  have hQnag : Qna.IsEquivariant IG σ' σ hσ' hσ :=
    Qn.isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hν hQng
  have hGreenData := Qna.exists_equivariantGreenAtlasData IG F' F σ' σ hσ' hσ k' k
    hk' hk ν hν hQnag L₁ L₀ hQna
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  intro A A' hA hA' Q hQ Qa hQa e he
  obtain ⟨Green, J, hGreen, hJ, hJproj, hQaJ, hGQa, Rzero, hRzero, Jzero, hJzero⟩ := hGreenData
  have hAdjointData := C₀.exists_associated_coefficientMetricAdjoint
    S E E' A' σ' hA' A σ hA ρ h h' ν hν
      k'.toContinuousHermitianMetric k'.isSmoothHermitianMetric_nativeAtlas Q hQ Qa hQa e he
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
  let : TopologicalSpace (TotalSpace Unit C') := tensorTopology (E := E') (F := K)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro η
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  intro AT AT' AU AU' AC AC' H V V' Va Va' Pc Γ₀ Γ₁ Γ₂ Γ₃ l₀ l₁ l₂ l₃ c₀ c₁
    NC₀ NC₁ N₀ N₁ N₂ N₃ kC₀ kC₁ k₀ k₁ k₂ k₃
  let := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₃.rank)) N₃.Fiber
  intro cIso₀ cIso₁ tIso₀ tIso₁ tIso₂ tIso₃ heC₀ hiC₀ heC₁ hiC₁
    heT₀ hiT₀ heT₁ hiT₁ heT₂ hiT₂ heT₃ hiT₃ hl₀ hl₁ hl₂ hl₃
    hmetricC₀ hmetricC₁ hmetricT₀ hmetricT₁ hmetricT₂ hmetricT₃
    hpure₀ hpure₁ hpure₂ hpure₃ hgram₀ hgram₁ H₁a hH₁a
    S₀ S₁ T₀ T₁ T₂ T₃ i₀ i₁ i₂ i₃ R hR
  -- Native adjunction supplies both original vertical pairing identities.
  obtain ⟨_, _, hV₀⟩ := hV₀Data
  obtain ⟨_, _, hV₁⟩ := hV₁Data
  obtain ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pn, hPn, hreverse, κs, hκs⟩ :=
    hAdjointData l₀ l₁ l₂ l₃ c₀ c₁ N₀ NC₀ NC₁ k₀ kC₀ kC₁
      tIso₀ cIso₀ cIso₁ heT₀ hiT₀ heC₀ hiC₀ heC₁ hiC₁ hl₂ hl₃
      hmetricT₀ hmetricC₀ hmetricC₁ hpure₂ hpure₃ hgram₀ hgram₁ H₁a hH₁a
      (hV₀ l₀ l₂ hl₀ hl₂ hpure₀ hpure₂) (hV₁ l₁ l₃ hl₁ hl₃ hpure₁ hpure₃)
  -- The coefficient action is exactly the elliptic conjugate under these same native maps.
  have hPc := C₀.coefficientOperator_isElliptic S E E' ρ hC
  obtain ⟨Pe, hPe, hPeEll⟩ : ∃ Pe : PseudodifferentialOperator
      (n := n) (r := NC₀.rank) (q := NC₁.rank) NC₀.Fiber NC₁.Fiber μ 1,
      Pe.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
      Pe.IsElliptic := by
    exact Pc.exists_elliptic_native_conjugate (μ := μ) hPc NC₀ NC₁
      cIso₀ cIso₁ heC₀ hiC₀ heC₁ hiC₁
  have hPnPe : Pn = Pe := by
    have heq := hPn.trans hPe.symm
    -- Both native coefficient representatives have the same conjugated smooth map.
    clear hκs κs hreverse hPn hPe hPeEll
    cases Pn
    cases Pe
    cases heq
    rfl
  have hEll : Pn.IsElliptic := hPnPe.symm ▸ hPeEll
  let Pa := Pn.metricFormalAdjoint kC₀ kC₁
  have hPaEll : Pa.IsElliptic := (Pn.isElliptic_metricFormalAdjoint_iff kC₀ kC₁).mpr hEll
  let J₀ := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hA' A' σ' hA' J hJ
  let J₁ := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hA' A' σ' hA' J hJ
  let G₀ := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A' σ' hA'
    Green hGreen
  -- Use the actual Green map of the original sphere adjoint, with its fixed presentations.
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : k₃.L2SectionSpace η →L[ℂ] k₃.L2SectionSpace η,
      ∀ u : AU'.smoothSections, P₀ (i₃ u) = i₃ (J₁ u) := by
    exact exists_associatedSphereTensorVertical_global_l2_realization
      (n := n) (r := r) (a := a') (m := 0)
      S E' F' F' σ' σ' hσ' hσ' k' k' ν L₁ L₁ Jbase' b' hJbase'
        J hJ Jzero hJzero
        Γ₃ Γ₃ l₃ hl₃ l₃ hl₃ N₃ N₃ k₃ k₃ η tIso₃ heT₃ hiT₃ tIso₃ heT₃ hiT₃
          hmetricT₃ hmetricT₃
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : k₂.L2SectionSpace η →L[ℂ] k₂.L2SectionSpace η,
      ∀ u : AT'.smoothSections, P₁ (i₂ u) = i₂ (J₀ u) := by
    exact exists_associatedSphereTensorVertical_global_l2_realization
      (n := n) (r := r) (a := a) (m := 0)
      S E F' F' σ' σ' hσ' hσ' k' k' ν L₁ L₁ Jbase b hJbase
        J hJ Jzero hJzero
        Γ₂ Γ₂ l₂ hl₂ l₂ hl₂ N₂ N₂ k₂ k₂ η tIso₂ heT₂ hiT₂ tIso₂ heT₂ hiT₂
          hmetricT₂ hmetricT₂
  obtain ⟨G₁, hG₁⟩ : ∃ G₁ : k₁.L2SectionSpace η →L[ℂ] k₃.L2SectionSpace η,
      ∀ u : AU.smoothSections, G₁ (i₁ u) = i₃ (G₀ u) := by
    exact exists_associatedSphereTensorVertical_global_l2_realization
      (n := n) (r := r) (a := a') (m := -1)
      S E' F F' σ σ' hσ hσ' k k' ν L₀ L₁ Jbase' b' hJbase'
        Green hGreen Rzero hRzero
        Γ₁ Γ₃ l₁ hl₁ l₃ hl₃ N₁ N₃ k₁ k₃ η tIso₁ heT₁ hiT₁ tIso₃ heT₃ hiT₃
          hmetricT₁ hmetricT₃
  -- The original evaluation and Gram pairings extend these exact Phi/Psi witnesses.
  let f := Qa.toLinearMap.ker.subtype.comp e.toLinearMap
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : kC₀.L2SectionSpace μ →ₗᵢ[ℂ] k₂.L2SectionSpace η,
      ∀ u : AC.smoothSections, e₀ (kC₀.smoothToL2 μ (S₀ u)) = i₂ (Φ u).val := by
    exact exists_associatedTensorKernelEvaluation_l2_isometry (a := a)
      S E A' σ' hA' ρ h k'.toContinuousHermitianMetric k'.isSmoothHermitianMetric_nativeAtlas
        μ ν hν f ev hev l₂ c₀ hl₂ hpure₂ hgram₀ (Va.ker.subtype.comp Φ.toLinearMap) hΦ
          NC₀ N₂ kC₀ k₂ cIso₀ tIso₂ heC₀ hiC₀ heT₂ hiT₂ hmetricC₀ hmetricT₂
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : kC₁.L2SectionSpace μ →ₗᵢ[ℂ] k₃.L2SectionSpace η,
      ∀ u : AC'.smoothSections, e₁ (kC₁.smoothToL2 μ (S₁ u)) = i₃ (Ψ u).val := by
    exact exists_associatedTensorKernelEvaluation_l2_isometry (a := a')
      S E' A' σ' hA' ρ h' k'.toContinuousHermitianMetric k'.isSmoothHermitianMetric_nativeAtlas
        μ ν hν f ev hev l₃ c₁ hl₃ hpure₃ hgram₁ (Va'.ker.subtype.comp Ψ.toLinearMap) hΨ
          NC₁ N₃ kC₁ k₃ cIso₁ tIso₃ heC₁ hiC₁ heT₃ hiT₃ hmetricC₁ hmetricT₃
  -- Symmetry of the same sphere orthogonal projection gives symmetry of both actual lifts.
  let W : Submodule ℂ (k'.SmoothL2Section ν) := Qna.toLinearMap.ker
  let : FiniteDimensional ℂ W := Qna.finiteDimensional_ker_of_isElliptic L₁ L₀ hQna
  let en := nativeSmoothSectionLinearEquiv (n := r) (r := F'.rank) F'.Fiber
  have hInt (s t : A'.smoothSections) :
      Integrable (fun y ↦ (k'.toCore y).inner (s.val y) (t.val y)) ν :=
    k'.integrable_pairing ν (en s) (en t)
  have hJpair (s t : A'.smoothSections) :
      (∫ y, (k'.toCore y).inner ((J.toLinearMap s).val y) (t.val y) ∂ν) =
        ∫ y, (k'.toCore y).inner (s.val y) ((J.toLinearMap t).val y) ∂ν := by
    have hs : en (J.toLinearMap s) = W.starProjection (en s) :=
      (congrArg en (hJproj s)).trans (en.apply_symm_apply _)
    have ht : en (J.toLinearMap t) = W.starProjection (en t) :=
      (congrArg en (hJproj t)).trans (en.apply_symm_apply _)
    change k'.sectionPairing ν (en (J.toLinearMap s)) (en t) =
      k'.sectionPairing ν (en s) (en (J.toLinearMap t))
    rw [hs, ht]
    exact W.inner_starProjection_left_eq_right (en s) (en t)
  have hJ₀adj := associatedSphereTensorVerticalOperator_integral_adjoint (a := a)
    S E A' σ' hA' A' σ' hA' J J hJ hJ μ ν hν h.toCore k'.toCore k'.toCore
      hInt hInt hJpair l₂ l₂ hl₂ hl₂ hpure₂ hpure₂
  have hJ₁adj := associatedSphereTensorVerticalOperator_integral_adjoint (a := a')
    S E' A' σ' hA' A' σ' hA' J J hJ hJ μ ν hν h'.toCore k'.toCore k'.toCore
      hInt hInt hJpair l₃ l₃ hl₃ hl₃ hpure₃ hpure₃
  have hsep (u v : AT'.smoothSections)
      (huv : ∀ s : AT'.smoothSections,
        (∫ z, (l₂.toCore z).inner (s.val z) (u.val z) ∂η) =
          ∫ z, (l₂.toCore z).inner (s.val z) (v.val z) ∂η) : u = v := by
    apply T₂.injective
    have heq : (show k₂.SmoothL2Section η from T₂ u) = T₂ v := by
      apply ext_inner_left ℂ
      intro w
      obtain ⟨s, rfl⟩ := T₂.surjective w
      change k₂.sectionPairing η (T₂ s) (T₂ u) = k₂.sectionPairing η (T₂ s) (T₂ v)
      calc
        _ = ∫ z, (l₂.toCore z).inner (s.val z) (u.val z) ∂η := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z ↦ hmetricT₂ z (s.val z) (u.val z)
        _ = ∫ z, (l₂.toCore z).inner (s.val z) (v.val z) ∂η := huv s
        _ = _ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z ↦ (hmetricT₂ z (s.val z) (v.val z)).symm
    exact heq
  -- Commute the reverse horizontal map with the fixed projection by testing against all sections.
  have hforward (s : AT'.smoothSections) : J₁ (H s) = H (J₀ s) :=
    LinearMap.congr_fun (C₀.horizontalLift_vertical_commute
      S E A' σ' hA' A' σ' hA' E' J hJ) s
  have hcommute (s : AU'.smoothSections) : J₀ (H₁a s) = H₁a (J₁ s) := by
    apply hsep
    intro u
    calc
      _ = ∫ z, (l₂.toCore z).inner ((J₀ u).val z) ((H₁a s).val z) ∂η :=
        (hJ₀adj u (H₁a s)).symm
      _ = ∫ z, (l₃.toCore z).inner ((H (J₀ u)).val z) (s.val z) ∂η :=
        (hH₁a (J₀ u) s).symm
      _ = ∫ z, (l₃.toCore z).inner ((J₁ (H u)).val z) (s.val z) ∂η := by
        rw [hforward]
      _ = ∫ z, (l₃.toCore z).inner ((H u).val z) ((J₁ s).val z) ∂η :=
        hJ₁adj (H u) s
      _ = _ := hH₁a u (J₁ s)
  let (x : B) : FiniteDimensional ℂ (E' x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a')) E' x
  have hJker (s : AU'.smoothSections) : J₁ s ∈ Va'.ker := by
    let restr := associatedSphereTensorFiberRestriction (a := a') S E' A' σ' hA'
    have hrestrict (p : P) : restr p (J₁ s) =
        tensorSectionOperator (E' (projection p)) A'.smoothSections A'.smoothSections
          J.toLinearMap (restr p s) := by
      apply Subtype.ext
      funext y
      apply (associatedSphereTensorFiberEquiv S E' σ' p y).injective
      rw [associatedSphereTensorFiberRestriction_apply,
        associatedSphereTensorVerticalOperator_apply]
      rfl
    have htensor (p : P) : tensorSectionOperator (E' (projection p))
        A'.smoothSections A.smoothSections Qa.toLinearMap (restr p (J₁ s)) = 0 := by
      rw [hrestrict]
      obtain ⟨z, hz⟩ := (tensorSectionEquiv (E' (projection p)) A'.smoothSections).surjective
        (restr p s)
      rw [← hz]
      simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rw [← LinearMap.lTensor_comp_apply, hQaJ, LinearMap.lTensor_zero]
      simp only [LinearMap.zero_apply, map_zero]
    change Va' (J₁ s) = 0
    apply Subtype.ext
    funext z
    induction z using Quotient.inductionOn with
    | h z =>
      change (Va' (J₁ s)).val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2) = 0
      calc
        _ = associatedSphereTensorFiberEquiv S E' σ z.1 z.2
            ((tensorSectionOperator (E' (projection z.1)) A'.smoothSections A.smoothSections
              Qa.toLinearMap (restr z.1 (J₁ s))).val z.2) :=
          associatedSphereTensorVerticalOperator_apply (a := a')
            S E' A' σ' hA' A σ hA Qa hQa (J₁ s) z.1 z.2
        _ = associatedSphereTensorFiberEquiv S E' σ z.1 z.2 0 :=
          congrArg (fun w ↦ associatedSphereTensorFiberEquiv S E' σ z.1 z.2 (w.val z.2))
            (htensor z.1)
        _ = 0 := map_zero _
  have hgreen (s : AU'.smoothSections) : G₀ (Va' s) = s - J₁ s :=
    LinearMap.congr_fun
      (associatedSphereTensorVerticalOperator_comp_eq_id_sub
        S E' A' σ' hA' A σ hA Qa Green J hQa hGreen hJ hGQa) s
  -- Only permute the output of the given R; the source and its simultaneous domain are unchanged.
  let swap := ContinuousLinearEquiv.prodComm ℂ (k₁.L2SectionSpace η) (k₂.L2SectionSpace η)
  let Rs := swap.toLinearMap.compPMap R
  let swapGraph := (ContinuousLinearEquiv.refl ℂ (k₃.L2SectionSpace η)).prodCongr swap
  have hRsmap : Rs.graph = R.graph.map swapGraph.toLinearMap := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, hRu⟩ := Rs.mem_graph_iff.mp hz
      refine ⟨(u.val, R u), R.mem_graph u, ?_⟩
      exact Prod.ext hu hRu
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hRu⟩ := R.mem_graph_iff.mp hz
      exact Rs.mem_graph_iff.mpr ⟨u, hu, congrArg swap hRu⟩
  have hRs : Rs.graph =
      (i₃.prod ((i₂.comp H₁a).prod (i₁.comp Va'))).range.topologicalClosure := by
    rw [hRsmap, hR]
    have hclosure :
        ((i₃.prod ((i₁.comp Va').prod (i₂.comp H₁a))).range.topologicalClosure).map
            swapGraph.toLinearMap =
          ((i₃.prod ((i₁.comp Va').prod (i₂.comp H₁a))).range.map
            swapGraph.toLinearMap).topologicalClosure := by
      ext z
      change z ∈ swapGraph '' closure (↑(i₃.prod
        ((i₁.comp Va').prod (i₂.comp H₁a))).range : Set _) ↔
          z ∈ closure (swapGraph '' (↑(i₃.prod
            ((i₁.comp Va').prod (i₂.comp H₁a))).range : Set _))
      exact Set.ext_iff.mp (swapGraph.toHomeomorph.image_closure _) z
    rw [hclosure]
    congr 1
    rw [← LinearMap.range_comp]
    rfl
  have hRsKer : Rs.ker = R.ker := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hRu⟩ := Rs.mem_ker_iff.mp hx
      exact R.mem_ker_iff.mpr ⟨u, hu, swap.injective (hRu.trans swap.map_zero.symm)⟩
    · intro hx
      obtain ⟨u, hu, hRu⟩ := R.mem_ker_iff.mp hx
      exact Rs.mem_ker_iff.mpr ⟨u, hu, (congrArg swap hRu).trans swap.map_zero⟩
  let L := Pa.metricL2ClosedRealization kC₁ kC₀
  have hL := Pa.metricL2ClosedRealization_realization kC₁ kC₀
  have hsmoothGraph (u : smoothSections (n := n) (r := NC₁.rank) NC₁.Fiber) :
      (kC₁.smoothToL2 μ u, kC₀.smoothToL2 μ (Pa.toLinearMap u)) ∈ L.graph := by
    rw [hL.1]
    apply (Pa.metricL2SmoothCore kC₁ kC₀).graph.le_topologicalClosure
    let f := LinearEquiv.ofInjective (kC₁.smoothToL2 μ) (kC₁.smoothToL2_injective μ)
    exact (Pa.metricL2SmoothCore kC₁ kC₀).mem_graph_iff.mpr
      ⟨f u, rfl, congrArg (fun w ↦ kC₀.smoothToL2 μ (Pa.toLinearMap w))
        (f.symm_apply_apply u)⟩
  have hH (u : AC'.smoothSections) : H₁a (Ψ u).val =
      (Φ (S₀.symm (Pa.toLinearMap (S₁ u)))).val := by
    calc
      _ = H₁a (Ψ (S₁.symm (S₁ u))).val :=
        congrArg (fun w : AC'.smoothSections ↦ H₁a (Ψ w).val) (S₁.symm_apply_apply u).symm
      _ = _ := hreverse (S₁ u)
  -- The projection identifies the closed graph of the coefficient adjoint.
  have hproject (s : AU'.smoothSections) : (P₀ (i₃ s), P₁ (i₂ (H₁a s))) ∈
      L.graph.map (e₁.toLinearMap.prodMap e₀.toLinearMap) := by
    let c := Ψ.symm ⟨J₁ s, hJker s⟩
    have hvalue : (Ψ c).val = J₁ s := congrArg Subtype.val (Ψ.apply_symm_apply _)
    refine ⟨(kC₁.smoothToL2 μ (S₁ c), kC₀.smoothToL2 μ (Pa.toLinearMap (S₁ c))),
      hsmoothGraph (S₁ c), ?_⟩
    apply Prod.ext
    · change e₁ (kC₁.smoothToL2 μ (S₁ c)) = P₀ (i₃ s)
      rw [he₁, hvalue, hP₀]
    · change e₀ (kC₀.smoothToL2 μ (Pa.toLinearMap (S₁ c))) = P₁ (i₂ (H₁a s))
      have heval : e₀ (kC₀.smoothToL2 μ (Pa.toLinearMap (S₁ c))) =
          i₂ (Φ (S₀.symm (Pa.toLinearMap (S₁ c)))).val :=
        (congrArg (fun w ↦ e₀ (kC₀.smoothToL2 μ w))
          (S₀.apply_symm_apply (Pa.toLinearMap (S₁ c))).symm).trans
            (he₀ (S₀.symm (Pa.toLinearMap (S₁ c))))
      rw [heval, ← hH, hvalue, hP₁, hcommute]
  have hsplit (s : AU'.smoothSections) : P₀ (i₃ s) = i₃ s - G₁ (i₁ (Va' s)) := by
    rw [hP₀, hG₁, hgreen, map_sub]
    abel
  have hreduce : Rs.ker ≤ L.ker.map e₁.toLinearMap :=
    ker_le_map_of_closedJointGreenSplitting i₃ (i₂.comp H₁a) (i₁.comp Va') Rs hRs L hL.2.1
      e₁ e₀ P₀ P₁ G₁ hsplit hproject
  obtain ⟨ec, _, hec, _⟩ := Pa.exists_metricL2ClosedRealization_kernel_cokernel_equiv
    kC₁ kC₀ hPaEll
  let f₀ : Pa.toLinearMap.ker →ₗ[ℂ] k₃.L2SectionSpace η :=
    i₃.comp ((H₁a.ker ⊓ Va'.ker).subtype.comp κs.toLinearMap)
  have hf₀ (u : Pa.toLinearMap.ker) : f₀ u ∈ Rs.ker := by
    have hzH : H₁a (κs u).val = 0 := (κs u).property.1
    have hzV : Va' (κs u).val = 0 := (κs u).property.2
    have hg : (f₀ u, (0, 0)) ∈ Rs.graph := by
      rw [hRs]
      apply Submodule.le_topologicalClosure
      refine ⟨(κs u).val, Prod.ext rfl ?_⟩
      exact Prod.ext ((congrArg i₂ hzH).trans i₂.map_zero)
        ((congrArg i₁ hzV).trans i₁.map_zero)
    obtain ⟨v, hv, hzero⟩ := Rs.mem_graph_iff.mp hg
    exact Rs.mem_ker_iff.mpr ⟨v, hv.symm, hzero⟩
  let fk := f₀.codRestrict Rs.ker hf₀
  have hfbij : Function.Bijective fk := by
    constructor
    · intro u v huv
      apply κs.injective
      apply Subtype.ext
      apply T₃.injective
      apply k₃.smoothToL2_injective η
      exact congrArg Subtype.val huv
    · intro x
      obtain ⟨c, hc, hcx⟩ := hreduce x.property
      obtain ⟨u, hu⟩ := ec.surjective ⟨c, hc⟩
      have huc : kC₁.smoothToL2 μ u.val = c :=
        (hec u).symm.trans (congrArg Subtype.val hu)
      have heval : e₁ (kC₁.smoothToL2 μ u.val) = i₃ (Ψ (S₁.symm u.val)).val :=
        (congrArg (fun w ↦ e₁ (kC₁.smoothToL2 μ w))
          (S₁.apply_symm_apply u.val).symm).trans (he₁ (S₁.symm u.val))
      refine ⟨u, Subtype.ext ?_⟩
      change i₃ (κs u).val = x.val
      rw [hκs]
      exact heval.symm.trans ((congrArg e₁ huc).trans hcx)
  let κr := LinearEquiv.ofBijective fk hfbij
  have hκr (u : Pa.toLinearMap.ker) : (κr u).val = i₃ (Ψ (S₁.symm u.val)).val :=
    congrArg i₃ (hκs u)
  have hkernel : L.ker.map e₁.toLinearMap ≤ Rs.ker := by
    rintro x ⟨c, hc, rfl⟩
    obtain ⟨u, hu⟩ := ec.surjective ⟨c, hc⟩
    have huc : kC₁.smoothToL2 μ u.val = c :=
      (hec u).symm.trans (congrArg Subtype.val hu)
    have heval : e₁ (kC₁.smoothToL2 μ u.val) = i₃ (Ψ (S₁.symm u.val)).val :=
      (congrArg (fun w ↦ e₁ (kC₁.smoothToL2 μ w))
        (S₁.apply_symm_apply u.val).symm).trans (he₁ (S₁.symm u.val))
    have heq : e₁ c = (κr u).val :=
      (congrArg e₁ huc.symm).trans (heval.trans (hκr u).symm)
    change e₁ c ∈ Rs.ker
    rw [heq]
    exact (κr u).property
  have hFred := Pa.closed_range_finite_metricL2ClosedRealization kC₁ kC₀ hPaEll
  let : FiniteDimensional ℂ L.ker := hFred.2.1
  obtain ⟨cBound, hcBound, hbound, hclosed, hfinite⟩ :=
    exists_closedJointGreenBound i₃ (i₂.comp H₁a) (i₁.comp Va') Rs hRs L hL.2.1 hL.2.2
      hFred.1 e₁ e₀ P₀ P₁ G₁ hsplit hproject hkernel
  -- Return to the original output order, retaining its exact kernel and unchanged max norm.
  let κ := κr.trans (LinearEquiv.ofEq _ _ hRsKer)
  refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pn, hPn, hEll, κ, hκr, cBound, hcBound, ?_, ?_, ?_⟩
  · intro u hu
    have hn := hbound u (hRsKer.symm ▸ hu)
    change ‖(u : k₃.L2SectionSpace η)‖ ≤ cBound * max ‖(R u).2‖ ‖(R u).1‖ at hn
    exact hn.trans_eq (congrArg (fun t : ℝ ↦ cBound * t)
      (max_comm ‖(R u).2‖ ‖(R u).1‖))
  · have hrange : Rs.toFun.range = R.toFun.range.map swap.toLinearMap :=
      LinearMap.range_comp _ _
    have himage := swap.symm.toHomeomorph.isClosedMap _ hclosed
    have heq : swap.symm '' (Rs.toFun.range : Set _) = R.toFun.range := by
      rw [hrange]
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        change swap.symm (swap w) ∈ (R.toFun.range : Set _)
        exact (swap.symm_apply_apply w).symm ▸ hw
      · intro hy
        exact ⟨swap y, ⟨y, hy, rfl⟩, swap.symm_apply_apply y⟩
    exact heq ▸ himage
  · exact hRsKer ▸ hfinite

end AtiyahSinger
