/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCutoffFactorsHomogeneous
public import AtiyahSinger.Analysis.AssociatedExactAdjointLocalization
public import AtiyahSinger.Analysis.AssociatedJointReverseBound
public import AtiyahSinger.Analysis.AssociatedSphereCommonBasePartition
public import AtiyahSinger.Analysis.AssociatedSphereCutoffSymbolIndex
public import AtiyahSinger.Analysis.AssociatedSphereGradedIndexCore
public import AtiyahSinger.Analysis.AssociatedSphereIndexInputs
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalDualApproximation
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalFamilyRegularization
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalCutoffFactor
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalNativeRegularization
public import AtiyahSinger.Analysis.AssociatedTensorResidualSmoothing
public import AtiyahSinger.Analysis.AssociatedTensorVerticalSobolevExtension
public import AtiyahSinger.Analysis.AssociatedVerticalCutoffFactor
public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.AtlasMetricL2Equivalence
public import AtiyahSinger.Analysis.AtlasNativePairedLimit
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.EquivariantFullSymbolCovariance
public import AtiyahSinger.Analysis.EquivariantPseudodifferentialOperator
public import AtiyahSinger.Analysis.FiniteRegularizationNormBounds
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint
public import AtiyahSinger.Analysis.HermitianMetricSymbol
public import AtiyahSinger.Analysis.LinearModelAnalyticIndex
public import AtiyahSinger.Analysis.NativeGradedApproximationIndex
public import AtiyahSinger.Analysis.NativeGradedSobolevCoordinates
public import AtiyahSinger.Analysis.NativeGradedTensorFamily
public import AtiyahSinger.Analysis.SobolevAdjointCoordinateIndex
public import AtiyahSinger.Geometry.SmoothBundlePresentationFrame
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Auxiliary interfaces for the associated-sphere index proof

Public module ID: M0119.

This module defines the common representative and Green witness records,
the generic native sum interface, and the conditional index comparisons.
It also constructs atlas and native vertical approximations with their shared
residuals, tensor symbols and two Sobolev error bounds. Geometric threshold
and coordinate comparison lemmas retain the supplied objects and certificates.

Concrete witness selections and the final associated-sphere index equalities
are made in their respective construction and comparison modules.
-/

@[expose] public noncomputable section

set_option Elab.async false

section AuxiliarySeedTypes

set_option Elab.async false

namespace AtiyahSinger

open Bundle ComplexBundle Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent
  lieGroup_orthogonalGroup associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  tensorTopology sumTopology isFiniteRank_tensor isFiniteRank_sum
  isFiniteRank_pullback isFiniteRank_associatedEquivariant

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Sphere" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Sphere
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := Sphere)

variable (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := B)))
  (v : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
    (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))

set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option genInjectivity false in
-- This implementation record never uses automatically generated constructor-injectivity lemmas.
open scoped Classical in
/-- Common original inputs and partitions, fixed before any positive-index analytic stage. -/
structure AssociatedSpherePositiveSeed where
  /-- The specified native source bundle on the base. -/
  baseSource : SmoothFiniteComplexBundle (n := n) B
  /-- The specified native target bundle on the base. -/
  baseTarget : SmoothFiniteComplexBundle (n := n) B
  /-- The original homogeneous base symbol. -/
  baseSymbol : homogeneousGlobalSymbolSpace (n := n)
    (r := baseSource.rank) (q := baseTarget.rank) baseSource.Fiber baseTarget.Fiber 1
  /-- Ellipticity of that homogeneous representative. -/
  baseSymbol_elliptic : IsEllipticGlobalSymbol baseSource.Fiber baseTarget.Fiber baseSymbol.val
  /-- Identification with the original supported base class. -/
  baseClass_eq : homogeneousSymbolKClass 1 baseSymbol baseSymbol_elliptic = u
  /-- The original base cotangent metric. -/
  baseCotangentMetric : SmoothCotangentMetric (n := n) (M := B)
  /-- The original source Hermitian metric. -/
  baseSourceMetric : SmoothHermitianMetric (n := n) (r := baseSource.rank) baseSource.Fiber
  /-- The original target Hermitian metric. -/
  baseTargetMetric : SmoothHermitianMetric (n := n) (r := baseTarget.rank) baseTarget.Fiber
  /-- The full symbol extending the specified homogeneous representative. -/
  baseFullSymbol : globalSymbolSpace (n := n) (r := baseSource.rank) (q := baseTarget.rank)
    baseSource.Fiber baseTarget.Fiber 1
  /-- The original quantization presentation, before localization. -/
  baseQuantization : QuantizationPresentation (n := n)
    (r := baseSource.rank) (q := baseTarget.rank) baseSource.Fiber baseTarget.Fiber
  /-- The actual finite localized operator used in every horizontal corner. -/
  localization : PrincipalPseudodifferentialLocalization
    (a := baseSource.rank) (a' := baseTarget.rank) S baseSource.Fiber baseTarget.Fiber μ 1
  /-- Ellipticity of the specified localized base operator. -/
  localization_elliptic : localization.baseOperator.IsElliptic
  /-- Its pieces sum to this exact full symbol. -/
  localization_symbol_sum : ∑ i, (localization.piece i).globalSymbol = baseFullSymbol
  /-- The full and homogeneous representatives agree on the unit-radius tail. -/
  baseSymbol_tail : ∀ x ξ, 1 ≤ baseCotangentMetric.length x ξ →
    baseFullSymbol.val x ξ = baseSymbol.val x ξ
  /-- The original patch index of each localized piece. -/
  patchIndex : Fin localization.size → Fin baseQuantization.size
  /-- The input spatial cutoff of each actual localized piece. -/
  inputCutoff : Fin localization.size → En → ℝ
  /-- The output spatial cutoff of each actual localized piece. -/
  outputCutoff : Fin localization.size → En → ℝ
  /-- Smoothness of the retained input cutoff. -/
  inputCutoff_smooth : ∀ i, ContDiff ℝ ∞ (inputCutoff i)
  /-- Smoothness of the retained output cutoff. -/
  outputCutoff_smooth : ∀ i, ContDiff ℝ ∞ (outputCutoff i)
  /-- Exact quantization and spatial-cutoff provenance of every piece. -/
  piece_origin : ∀ i, localization.piece i =
    ((baseQuantization.patch (patchIndex i)).toPiece baseFullSymbol).coordinateCutoff
      (inputCutoff i) (outputCutoff i) (inputCutoff_smooth i) (outputCutoff_smooth i)
  /-- The atlas principal-class certificate for the original homogeneous base symbol. -/
  base_atlas_principal :
    letI := modelTopology (EuclideanSpace ℂ (Fin baseSource.rank)) baseSource.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin baseTarget.rank)) baseTarget.Fiber
    let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := baseSource.rank) baseSource.Fiber
    let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := baseTarget.rank) baseTarget.Fiber
    let props := nativeAtlasSymbolFunction_homogeneous_properties 1 baseSymbol.val
      baseSymbol.property.1 baseSymbol.property.2 baseSymbol_elliptic
    localization.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
      atlasGlobalPrincipalSymbolClass A₀ A₁ 1
        (atlasRegularizedSymbol A₀ A₁ baseCotangentMetric 1
          (nativeAtlasSymbolFunction baseSymbol.val) props.1 props.2.1)
  /-- The original native fiber source bundle. -/
  fiberSource : SmoothFiniteComplexBundle (n := r) Sphere
  /-- The original native fiber target bundle. -/
  fiberTarget : SmoothFiniteComplexBundle (n := r) Sphere
  /-- The original action on the source fiber bundle. -/
  fiberAction :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    EquivariantStructure G fiberSource.Fiber
  /-- The original action on the target fiber bundle. -/
  fiberTargetAction :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    EquivariantStructure G fiberTarget.Fiber
  /-- Smoothness of the source action in its native manifold model. -/
  fiberAction_smooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    fiberAction.IsSmooth (n := r) (r := fiberSource.rank) IG
  /-- Smoothness of the target action in its native manifold model. -/
  fiberTargetAction_smooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    fiberTargetAction.IsSmooth (n := r) (r := fiberTarget.rank) IG
  /-- The original homogeneous equivariant fiber symbol. -/
  fiberSymbol : homogeneousGlobalSymbolSpace (n := r)
    (r := fiberSource.rank) (q := fiberTarget.rank) fiberSource.Fiber fiberTarget.Fiber 1
  /-- Ellipticity of the homogeneous fiber symbol. -/
  fiberSymbol_elliptic : IsEllipticGlobalSymbol fiberSource.Fiber fiberTarget.Fiber fiberSymbol.val
  /-- Equivariance of the same homogeneous symbol away from zero. -/
  fiberSymbol_equivariant :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG fiberAction fiberTargetAction γ fiberSymbol.val x ξ =
        fiberSymbol.val x ξ
  /-- Identification with the original equivariant supported class. -/
  fiberClass_eq :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    equivariantHomogeneousSymbolKClass IG fiberAction fiberTargetAction 1 fiberSymbol
      fiberSymbol_elliptic fiberSymbol_equivariant = v
  /-- The original invariant cotangent metric on the fiber sphere. -/
  fiberCotangentMetric : SmoothCotangentMetric (n := r) (M := Sphere)
  /-- The original invariant source Hermitian metric. -/
  fiberSourceMetric : SmoothHermitianMetric (n := r) (r := fiberSource.rank) fiberSource.Fiber
  /-- The original invariant target Hermitian metric. -/
  fiberTargetMetric : SmoothHermitianMetric (n := r) (r := fiberTarget.rank) fiberTarget.Fiber
  /-- Invariance of the source metric for the original action. -/
  fiberSourceMetric_invariant :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    ∀ (γ : G) (x : Sphere) (s t : fiberSource.Fiber x),
      fiberSourceMetric.pairing (γ • x) (fiberAction.linearMap γ x s)
        (fiberAction.linearMap γ x t) = fiberSourceMetric.pairing x s t
  /-- Invariance of the target metric for the original action. -/
  fiberTargetMetric_invariant :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    ∀ (γ : G) (x : Sphere) (s t : fiberTarget.Fiber x),
      fiberTargetMetric.pairing (γ • x) (fiberTargetAction.linearMap γ x s)
        (fiberTargetAction.linearMap γ x t) = fiberTargetMetric.pairing x s t
  /-- Invariance of the original cotangent length. -/
  fiberLength_invariant : ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x),
    fiberCotangentMetric.length (γ • x) (γ • (⟨x, ξ⟩ : SphereCot)).snd =
      fiberCotangentMetric.length x ξ
  /-- The original full invariant fiber symbol. -/
  fiberFullSymbol : globalSymbolSpace (n := r) (r := fiberSource.rank) (q := fiberTarget.rank)
    fiberSource.Fiber fiberTarget.Fiber 1
  /-- Exact invariance of that full symbol. -/
  fiberFullSymbol_invariant :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    ∀ γ : G, equivariantGlobalSymbolLinearMap IG fiberAction fiberTargetAction γ
      fiberFullSymbol.val = fiberFullSymbol.val
  /-- Agreement with the original homogeneous fiber symbol on the unit-radius tail. -/
  fiberSymbol_tail : ∀ x ξ, 1 ≤ fiberCotangentMetric.length x ξ →
    fiberFullSymbol.val x ξ = fiberSymbol.val x ξ
  /-- Full-symbol ellipticity for the same fiber representative. -/
  fiberFullSymbol_elliptic : IsEllipticFullGlobalSymbol (r := fiberSource.rank)
    (q := fiberTarget.rank) fiberSource.Fiber fiberTarget.Fiber 1 fiberFullSymbol.val
  /-- The original smooth positive measure for the specified fiber operator. -/
  fiberMeasure : Measure Sphere
  /-- Its original smooth positive density certificate. -/
  fiberMeasure_smooth : IsSmoothPositiveMeasure (n := r) fiberMeasure
  /-- The original density is invariant under the specified orthogonal action. -/
  fiberMeasure_invariant : ∀ γ : G, Measure.map (fun y : Sphere ↦ γ • y) fiberMeasure = fiberMeasure
  /-- The actual equivariant fiber PDO used in the Green coefficient formula. -/
  fiberOperator :
    letI := fiberMeasure_smooth
    PseudodifferentialOperator (n := r) (r := fiberSource.rank) (q := fiberTarget.rank)
      fiberSource.Fiber fiberTarget.Fiber fiberMeasure 1
  /-- Equivariance of the specified operator for the specified actions. -/
  fiberOperator_equivariant :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    letI := fiberMeasure_smooth
    fiberOperator.IsEquivariant IG fiberAction fiberTargetAction
      fiberAction_smooth fiberTargetAction_smooth
  /-- Ellipticity of that same operator. -/
  fiberOperator_elliptic :
    letI := fiberMeasure_smooth
    fiberOperator.IsElliptic
  /-- Its principal class is represented by the original full fiber symbol. -/
  fiberOperator_principal :
    letI := fiberMeasure_smooth
    fiberOperator.principalSymbol =
      globalPrincipalSymbolClass fiberSource.Fiber fiberTarget.Fiber 1 fiberFullSymbol
  /-- Its representation index is the index of the original fiber class. -/
  fiberOperator_index :
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberSource.rank)) fiberSource.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber
    letI := fiberMeasure_smooth
    fiberOperator.smoothEquivariantAnalyticIndex IG fiberAction fiberTargetAction
      fiberAction_smooth fiberTargetAction_smooth fiberOperator_equivariant
      fiberOperator_elliptic = orthogonalSphereAnalyticIndex r v
  /-- The source sphere presentation shared by Green and horizontal regularization. -/
  sphereSourcePresentation : SmoothBundlePresentation (n := r)
    (r := fiberSource.rank) fiberSource.Fiber
  /-- Target sphere frames over this same finite index set and scalar partition. -/
  sphereTargetFrame : Fin sphereSourcePresentation.size →
    Trivialization (EuclideanSpace ℂ (Fin fiberTarget.rank))
      (π (EuclideanSpace ℂ (Fin fiberTarget.rank)) fiberTarget.Fiber)
  /-- These target frames belong to the original native bundle atlas. -/
  sphereTargetFrame_mem : ∀ j, MemTrivializationAtlas (sphereTargetFrame j)
  /-- The shared sphere cutoffs are supported in those target frames. -/
  sphereTargetFrame_support : ∀ j,
    tsupport (sphereSourcePresentation.cutoff j) ⊆ (sphereTargetFrame j).baseSet
  /-- The common base source presentation, subordinate to the principal atlas. -/
  baseSourcePresentation : SmoothBundlePresentation (n := n)
    (r := baseSource.rank) baseSource.Fiber
  /-- Target base frames over the same base cutoffs. -/
  baseTargetFrame : Fin baseSourcePresentation.size →
    Trivialization (EuclideanSpace ℂ (Fin baseTarget.rank))
      (π (EuclideanSpace ℂ (Fin baseTarget.rank)) baseTarget.Fiber)
  /-- These target base frames belong to the original native bundle atlas. -/
  baseTargetFrame_mem : ∀ j, MemTrivializationAtlas (baseTargetFrame j)
  /-- The shared base cutoffs are supported in those target frames. -/
  baseTargetFrame_support : ∀ j,
    tsupport (baseSourcePresentation.cutoff j) ⊆ (baseTargetFrame j).baseSet
  /-- The principal-chart center chosen for each base cutoff. -/
  basePartitionCenter : Fin baseSourcePresentation.size → B
  /-- Each original base cutoff lies in its specified principal trivialization. -/
  basePartition_subordinate : ∀ j, tsupport (baseSourcePresentation.cutoff j) ⊆
    (S.trivialization (basePartitionCenter j)).baseSet
  /-- The lifted weights from this same base partition sum to one. -/
  basePartition_sum :
    letI := S.toIsPrincipalBundle
    ∀ z : Z, (∑ j, if z ∈ (associatedSphereTrivialization S (basePartitionCenter j)).source ∧
      (associatedSphereTrivialization S (basePartitionCenter j) z).1 ∈
        (baseSourcePresentation.chart j).source then
      (baseSourcePresentation.chartCutoff baseSource.Fiber j).cutoff
        (baseSourcePresentation.chart j
          (associatedSphereTrivialization S (basePartitionCenter j) z).1) else 0) = 1

namespace AssociatedSpherePositiveSeed

variable {S μ u v} (s : AssociatedSpherePositiveSeed S μ u v)

/-- The target sphere presentation retains the source's exact scalar partition. -/
def sphereTargetPresentation : SmoothBundlePresentation (n := r)
    (r := s.fiberTarget.rank) s.fiberTarget.Fiber :=
  s.sphereSourcePresentation.withFrame s.sphereTargetFrame
    s.sphereTargetFrame_mem s.sphereTargetFrame_support

/-- The target base presentation retains the source's exact scalar partition. -/
def baseTargetPresentation : SmoothBundlePresentation (n := n)
    (r := s.baseTarget.rank) s.baseTarget.Fiber :=
  s.baseSourcePresentation.withFrame s.baseTargetFrame
    s.baseTargetFrame_mem s.baseTargetFrame_support

end AssociatedSpherePositiveSeed

end AtiyahSinger

end AuxiliarySeedTypes


section AuxiliaryGreenTypes

set_option Elab.async false
set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate
attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology continuousSMul_orthogonalSphere continuousSMul_orthogonalSphereCotangent
  lieGroup_orthogonalGroup
  t2Space_cotangent locallyCompactSpace_cotangent
variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} {S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection}
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Enr" => EuclideanSpace ℝ (Fin (n + r))
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "πS" => associatedBundleProjection («F» := Y) S.toIsPrincipalBundle
variable
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  {u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := B))}
  {v : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
    (CotangentTotalSpace (n := r) (M := OrthogonalSphere r))}
  (s : AssociatedSpherePositiveSeed S μ u v)
local notation "E" => s.baseSource
local notation "E'" => s.baseTarget
local notation "F" => s.fiberSource
local notation "F'" => s.fiberTarget
local notation "σ" => s.fiberAction
local notation "σ'" => s.fiberTargetAction
local notation "h" => s.baseSourceMetric
local notation "h'" => s.baseTargetMetric
local notation "k" => s.fiberSourceMetric
local notation "k'" => s.fiberTargetMetric
local notation "ν" => s.fiberMeasure
local notation "C" => s.localization
local notation "Q" => s.fiberOperator
local notation "hσ" => s.fiberAction_smooth
local notation "hσ'" => s.fiberTargetAction_smooth
local notation "hQ" => s.fiberOperator_equivariant
local notation "hQell" => s.fiberOperator_elliptic
/-! The local instances are the same canonical models used in the original core call. -/
local instance : IsSmoothPositiveMeasure (n := r) ν := s.fiberMeasure_smooth
local instance : IsFiniteMeasure ν := isFiniteMeasure_of_smoothPositiveMeasure (n := r) ν
local instance : TopologicalSpace (TotalSpace Unit (E).Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
local instance : TopologicalSpace (TotalSpace Unit (E').Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
local instance : TopologicalSpace (TotalSpace Unit (F).Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
local instance : TopologicalSpace (TotalSpace Unit (F').Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
local instance : IsFiniteRank (E).Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
local instance : IsFiniteRank (E').Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
local instance : IsFiniteRank (F).Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
local instance : IsFiniteRank (F').Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
local instance (x : B) : FiniteDimensional ℂ ((E).Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber x
local instance (x : B) : FiniteDimensional ℂ ((E').Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber x
local instance (x : Y) : FiniteDimensional ℂ ((F).Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber x
local instance (x : Y) : FiniteDimensional ℂ ((F').Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber x
set_option quotPrecheck false in
local notation "A" => nativeSmoothComplexBundleAtlas (n := r) (r := (F).rank) (F).Fiber
set_option quotPrecheck false in
local notation "A'" => nativeSmoothComplexBundleAtlas (n := r) (r := (F').rank) (F').Fiber
set_option quotPrecheck false in
local notation "hA" => (σ).isSmoothAtlas_native IG hσ
set_option quotPrecheck false in
local notation "hA'" => (σ').isSmoothAtlas_native IG hσ'
set_option quotPrecheck false in
local notation "QA" => (Q).toAtlasPseudodifferentialOperator
set_option quotPrecheck false in
local notation "JA" => ((Q).metricFormalAdjoint k k').toAtlasPseudodifferentialOperator
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
set_option quotPrecheck false in
local notation "T" => fun z : Z ↦ (E).Fiber (πS z) ⊗[ℂ] D z
set_option quotPrecheck false in
local notation "U" => fun z : Z ↦ (E').Fiber (πS z) ⊗[ℂ] D z
set_option quotPrecheck false in
local notation "T'" => fun z : Z ↦ (E).Fiber (πS z) ⊗[ℂ] D' z
set_option quotPrecheck false in
local notation "U'" => fun z : Z ↦ (E').Fiber (πS z) ⊗[ℂ] D' z
local instance : TopologicalSpace (TotalSpace Unit T) :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D)
local instance : TopologicalSpace (TotalSpace Unit U) :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D)
local instance : TopologicalSpace (TotalSpace Unit T') :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D')
local instance : TopologicalSpace (TotalSpace Unit U') :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D')
set_option quotPrecheck false in
local notation "η" =>
  (letI : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
   associatedProductMeasure S.toIsPrincipalBundle μ ν s.fiberMeasure_invariant)
set_option quotPrecheck false in
local notation "A₀₀" => associatedSphereTensorBundleAtlas (a := (E).rank) S (E).Fiber A σ hA
set_option quotPrecheck false in
local notation "A₁₀" => associatedSphereTensorBundleAtlas (a := (E').rank) S (E').Fiber A σ hA
set_option quotPrecheck false in
local notation "A₀₁" => associatedSphereTensorBundleAtlas (a := (E).rank) S (E).Fiber A' σ' hA'
set_option quotPrecheck false in
local notation "A₁₁" => associatedSphereTensorBundleAtlas (a := (E').rank) S (E').Fiber A' σ' hA'
set_option quotPrecheck false in
local notation "H₀" => (C).horizontalLift S (E).Fiber A σ (E').Fiber hA
set_option quotPrecheck false in
local notation "H₁" => (C).horizontalLift S (E).Fiber A' σ' (E').Fiber hA'

/-! This local syntax only inserts the canonical instance telescope. It neither chooses a
new model nor adds a parameter. The same transparent instances scope every dependent
field and computed map; theorem proofs establish this context explicitly. -/
set_option quotPrecheck false in
local notation "sphereContext%[" t "]" =>
  (letI : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
   letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
   letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
   letI : ChartedSpace Enr Z :=
     linearModelChartedSpace (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
   letI : IsManifold (𝓡 (n + r)) ∞ Z :=
     isManifold_linearModelChartedSpace
       (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
   letI : IsSmoothPositiveMeasure (n := n + r) η :=
     isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
   t)

set_option genInjectivity false in
-- This implementation record uses constructors and projections, not injectivity lemmas.
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended instance budget resolves the dependent projections of one common Green witness.
/-- The raw Green witnesses over one seed, with the four fixed atlas domains. -/
structure AssociatedSphereGreenSelection where
  /-- Equivariance of the original forward atlas operator. -/
  fiberAtlasOperator_equivariant : sphereContext%[(QA).IsEquivariant IG σ σ' hA hA']
  /-- Equivariance of the literal fiber metric adjoint. -/
  fiberAtlasAdjoint_equivariant : sphereContext%[(JA).IsEquivariant IG σ' σ hA' hA]
  /-- The original tensor metric in corner ₀₀. -/
  atlasMetric₀₀ : sphereContext%[ContinuousHermitianMetric T]
  /-- The original tensor metric in corner ₁₀. -/
  atlasMetric₁₀ : sphereContext%[ContinuousHermitianMetric U]
  /-- The original tensor metric in corner ₀₁. -/
  atlasMetric₀₁ : sphereContext%[ContinuousHermitianMetric T']
  /-- The original tensor metric in corner ₁₁. -/
  atlasMetric₁₁ : sphereContext%[ContinuousHermitianMetric U']
  /-- The original native bundle in corner ₀₀. -/
  native₀₀ : sphereContext%[SmoothFiniteComplexBundle (n := n + r) Z]
  /-- The original native bundle in corner ₁₀. -/
  native₁₀ : sphereContext%[SmoothFiniteComplexBundle (n := n + r) Z]
  /-- The original native bundle in corner ₀₁. -/
  native₀₁ : sphereContext%[SmoothFiniteComplexBundle (n := n + r) Z]
  /-- The original native bundle in corner ₁₁. -/
  native₁₁ : sphereContext%[SmoothFiniteComplexBundle (n := n + r) Z]
  /-- The metric on that same native corner. -/
  nativeMetric₀₀ :
    sphereContext%[
      letI : TopologicalSpace (TotalSpace Unit native₀₀.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
      SmoothHermitianMetric (n := n + r) (r := native₀₀.rank) native₀₀.Fiber]
  /-- The metric on that same native corner. -/
  nativeMetric₁₀ :
    sphereContext%[
      letI : TopologicalSpace (TotalSpace Unit native₁₀.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
      SmoothHermitianMetric (n := n + r) (r := native₁₀.rank) native₁₀.Fiber]
  /-- The metric on that same native corner. -/
  nativeMetric₀₁ :
    sphereContext%[
      letI : TopologicalSpace (TotalSpace Unit native₀₁.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
      SmoothHermitianMetric (n := n + r) (r := native₀₁.rank) native₀₁.Fiber]
  /-- The metric on that same native corner. -/
  nativeMetric₁₁ :
    sphereContext%[
      letI : TopologicalSpace (TotalSpace Unit native₁₁.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
      SmoothHermitianMetric (n := n + r) (r := native₁₁.rank) native₁₁.Fiber]
  /-- The selected isomorphism from the original quotient tensor fiber. -/
  nativeIso₀₀ : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₀₀.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
    Iso T native₀₀.Fiber]
  /-- The selected isomorphism from the original quotient tensor fiber. -/
  nativeIso₁₀ : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₁₀.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
    Iso U native₁₀.Fiber]
  /-- The selected isomorphism from the original quotient tensor fiber. -/
  nativeIso₀₁ : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₀₁.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
    Iso T' native₀₁.Fiber]
  /-- The selected isomorphism from the original quotient tensor fiber. -/
  nativeIso₁₁ : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₁₁.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
    Iso U' native₁₁.Fiber]
  /-- Smoothness of that same forward isomorphism. -/
  nativeIso₀₀_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
      IsSmoothAtlasBundleMap A₀₀
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₀₀.rank) native₀₀.Fiber)
        nativeIso₀₀.toHom.linearMap]
  /-- Smoothness of its actual inverse. -/
  nativeIso₀₀_symm_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank))
        native₀₀.Fiber
      IsSmoothAtlasBundleMap
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₀₀.rank) native₀₀.Fiber)
        A₀₀ nativeIso₀₀.symm.toHom.linearMap]
  /-- Smoothness of that same forward isomorphism. -/
  nativeIso₁₀_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
      IsSmoothAtlasBundleMap A₁₀
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₁₀.rank) native₁₀.Fiber)
        nativeIso₁₀.toHom.linearMap]
  /-- Smoothness of its actual inverse. -/
  nativeIso₁₀_symm_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank))
        native₁₀.Fiber
      IsSmoothAtlasBundleMap
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₁₀.rank) native₁₀.Fiber)
        A₁₀ nativeIso₁₀.symm.toHom.linearMap]
  /-- Smoothness of that same forward isomorphism. -/
  nativeIso₀₁_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
      IsSmoothAtlasBundleMap A₀₁
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₀₁.rank) native₀₁.Fiber)
        nativeIso₀₁.toHom.linearMap]
  /-- Smoothness of its actual inverse. -/
  nativeIso₀₁_symm_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank))
        native₀₁.Fiber
      IsSmoothAtlasBundleMap
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₀₁.rank) native₀₁.Fiber)
        A₀₁ nativeIso₀₁.symm.toHom.linearMap]
  /-- Smoothness of that same forward isomorphism. -/
  nativeIso₁₁_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
      IsSmoothAtlasBundleMap A₁₁
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₁₁.rank) native₁₁.Fiber)
        nativeIso₁₁.toHom.linearMap]
  /-- Smoothness of its actual inverse. -/
  nativeIso₁₁_symm_smooth :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank))
        native₁₁.Fiber
      IsSmoothAtlasBundleMap
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₁₁.rank) native₁₁.Fiber)
        A₁₁ nativeIso₁₁.symm.toHom.linearMap]
  /-- Smoothness of the original atlas metric. -/
  atlasMetric₀₀_smooth : sphereContext%[(A₀₀).IsSmoothHermitianMetric atlasMetric₀₀]
  /-- Smoothness of the original atlas metric. -/
  atlasMetric₁₀_smooth : sphereContext%[(A₁₀).IsSmoothHermitianMetric atlasMetric₁₀]
  /-- Smoothness of the original atlas metric. -/
  atlasMetric₀₁_smooth : sphereContext%[(A₀₁).IsSmoothHermitianMetric atlasMetric₀₁]
  /-- Smoothness of the original atlas metric. -/
  atlasMetric₁₁_smooth : sphereContext%[(A₁₁).IsSmoothHermitianMetric atlasMetric₁₁]
  /-- The original tensor-model rank, including rank zero. -/
  native₀₀_rank : sphereContext%[native₀₀.rank = (E).rank * (F).rank]
  /-- The original tensor-model rank, including rank zero. -/
  native₁₀_rank : sphereContext%[native₁₀.rank = (E').rank * (F).rank]
  /-- The original tensor-model rank, including rank zero. -/
  native₀₁_rank : sphereContext%[native₀₁.rank = (E).rank * (F').rank]
  /-- The original tensor-model rank, including rank zero. -/
  native₁₁_rank : sphereContext%[native₁₁.rank = (E').rank * (F').rank]
  /-- The original pure-tensor formula over quotient representatives. -/
  atlasMetric₀₀_pure :
    sphereContext%[∀ (p : P) (y : Y) (u v : (E).Fiber (projection p)) (a b : (F).Fiber y),
        (atlasMetric₀₀.toCore (associatedBundleMk G P Y p y)).inner
            (associatedSphereTensorFiberEquiv S (E).Fiber σ p y (u ⊗ₜ[ℂ] a))
            (associatedSphereTensorFiberEquiv S (E).Fiber σ p y (v ⊗ₜ[ℂ] b)) =
          (h).pairing (projection p) u v * (k).pairing y a b]
  /-- The original pure-tensor formula over quotient representatives. -/
  atlasMetric₁₀_pure :
    sphereContext%[∀ (p : P) (y : Y) (u v : (E').Fiber (projection p)) (a b : (F).Fiber y),
        (atlasMetric₁₀.toCore (associatedBundleMk G P Y p y)).inner
            (associatedSphereTensorFiberEquiv S (E').Fiber σ p y (u ⊗ₜ[ℂ] a))
            (associatedSphereTensorFiberEquiv S (E').Fiber σ p y (v ⊗ₜ[ℂ] b)) =
          (h').pairing (projection p) u v * (k).pairing y a b]
  /-- The original pure-tensor formula over quotient representatives. -/
  atlasMetric₀₁_pure :
    sphereContext%[∀ (p : P) (y : Y) (u v : (E).Fiber (projection p)) (a b : (F').Fiber y),
        (atlasMetric₀₁.toCore (associatedBundleMk G P Y p y)).inner
            (associatedSphereTensorFiberEquiv S (E).Fiber σ' p y (u ⊗ₜ[ℂ] a))
            (associatedSphereTensorFiberEquiv S (E).Fiber σ' p y (v ⊗ₜ[ℂ] b)) =
          (h).pairing (projection p) u v * (k').pairing y a b]
  /-- The original pure-tensor formula over quotient representatives. -/
  atlasMetric₁₁_pure :
    sphereContext%[∀ (p : P) (y : Y) (u v : (E').Fiber (projection p)) (a b : (F').Fiber y),
        (atlasMetric₁₁.toCore (associatedBundleMk G P Y p y)).inner
            (associatedSphereTensorFiberEquiv S (E').Fiber σ' p y (u ⊗ₜ[ℂ] a))
            (associatedSphereTensorFiberEquiv S (E').Fiber σ' p y (v ⊗ₜ[ℂ] b)) =
          (h').pairing (projection p) u v * (k').pairing y a b]
  /-- This exact native isomorphism preserves the original tensor metric. -/
  nativeIso₀₀_isometry : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₀₀.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
    ∀ (z : Z) (v w : T z),
      nativeMetric₀₀.pairing z (nativeIso₀₀.linearEquiv z v) (nativeIso₀₀.linearEquiv z w) =
        (atlasMetric₀₀.toCore z).inner v w]
  /-- This exact native isomorphism preserves the original tensor metric. -/
  nativeIso₁₀_isometry : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₁₀.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
    ∀ (z : Z) (v w : U z),
      nativeMetric₁₀.pairing z (nativeIso₁₀.linearEquiv z v) (nativeIso₁₀.linearEquiv z w) =
        (atlasMetric₁₀.toCore z).inner v w]
  /-- This exact native isomorphism preserves the original tensor metric. -/
  nativeIso₀₁_isometry : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₀₁.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
    ∀ (z : Z) (v w : T' z),
      nativeMetric₀₁.pairing z (nativeIso₀₁.linearEquiv z v) (nativeIso₀₁.linearEquiv z w) =
        (atlasMetric₀₁.toCore z).inner v w]
  /-- This exact native isomorphism preserves the original tensor metric. -/
  nativeIso₁₁_isometry : sphereContext%[
    letI : TopologicalSpace (TotalSpace Unit native₁₁.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
    ∀ (z : Z) (v w : U' z),
      nativeMetric₁₁.pairing z (nativeIso₁₁.linearEquiv z v) (nativeIso₁₁.linearEquiv z w) =
        (atlasMetric₁₁.toCore z).inner v w]
  /-- The actual base cutoff used for the exact horizontal adjoint. -/
  baseAdjointCutoff₀ : sphereContext%[Fin (C).size → B → ℝ]
  /-- Smoothness of the selected adjoint cutoff. -/
  baseAdjointCutoff₀_smooth : sphereContext%[∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (baseAdjointCutoff₀ i)]
  /-- Subordination to the same principal trivialization. -/
  baseAdjointCutoff₀_support : sphereContext%[∀ i, tsupport (baseAdjointCutoff₀ i) ⊆
    (S.trivialization ((C).center i)).baseSet]
  /-- The cutoff is one over the chart pullback of both original spatial cutoff supports. -/
  baseAdjointCutoff₀_one : sphereContext%[∀ i, ∀ x ∈ ((C).piece i).chart.symm ''
      (tsupport ((C).piece i).input.cutoff ∪ tsupport ((C).piece i).output.cutoff),
      baseAdjointCutoff₀ i x = 1]
  /-- The original finite family of reverse horizontal pieces. -/
  horizontalPieceAdjoint₀ :
    sphereContext%[Fin (C).size → (A₁₀).smoothSections →ₗ[ℂ] (A₀₀).smoothSections]
  /-- Exact formula, not just existence of an arbitrary formal adjoint. -/
  horizontalPieceAdjoint₀_formula :
    sphereContext%[
      let Pbase (i : Fin (C).size) : PseudodifferentialOperator
          (n := n) (r := (E).rank) (q := (E').rank) (E).Fiber (E').Fiber μ 1 :=
        ⟨((C).piece i).toLinearMap, ((C).piece i).isPseudodifferentialOperator 1⟩
      let Jbase (i : Fin (C).size) := (Pbase i).metricFormalAdjoint h h'
      ∀ i w z, (horizontalPieceAdjoint₀ i w).val z =
        associatedSphereTensorBaseExtension S (E).Fiber σ ((C).center i)
          (fun y x ↦ ((tensorSectionOperator ((F).Fiber y)
            (smoothSections (E').Fiber) (smoothSections (E).Fiber) (Jbase i).toLinearMap)
              (associatedSphereTensorCutoffBaseRestriction (a := (E').rank) S (E').Fiber
                A σ hA ((C).center i) (baseAdjointCutoff₀ i)
                (baseAdjointCutoff₀_smooth i) (baseAdjointCutoff₀_support i) y w)).val x) z]
  /-- The actual base cutoff used for the exact horizontal adjoint. -/
  baseAdjointCutoff₁ : sphereContext%[Fin (C).size → B → ℝ]
  /-- Smoothness of the selected adjoint cutoff. -/
  baseAdjointCutoff₁_smooth : sphereContext%[∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (baseAdjointCutoff₁ i)]
  /-- Subordination to the same principal trivialization. -/
  baseAdjointCutoff₁_support : sphereContext%[∀ i, tsupport (baseAdjointCutoff₁ i) ⊆
    (S.trivialization ((C).center i)).baseSet]
  /-- The cutoff is one over the chart pullback of both original spatial cutoff supports. -/
  baseAdjointCutoff₁_one : sphereContext%[∀ i, ∀ x ∈ ((C).piece i).chart.symm ''
      (tsupport ((C).piece i).input.cutoff ∪ tsupport ((C).piece i).output.cutoff),
      baseAdjointCutoff₁ i x = 1]
  /-- The original finite family of reverse horizontal pieces. -/
  horizontalPieceAdjoint₁ :
    sphereContext%[Fin (C).size → (A₁₁).smoothSections →ₗ[ℂ] (A₀₁).smoothSections]
  /-- Exact formula, not just existence of an arbitrary formal adjoint. -/
  horizontalPieceAdjoint₁_formula :
    sphereContext%[
      let Pbase (i : Fin (C).size) : PseudodifferentialOperator
          (n := n) (r := (E).rank) (q := (E').rank) (E).Fiber (E').Fiber μ 1 :=
        ⟨((C).piece i).toLinearMap, ((C).piece i).isPseudodifferentialOperator 1⟩
      let Jbase (i : Fin (C).size) := (Pbase i).metricFormalAdjoint h h'
      ∀ i w z, (horizontalPieceAdjoint₁ i w).val z =
        associatedSphereTensorBaseExtension S (E).Fiber σ' ((C).center i)
          (fun y x ↦ ((tensorSectionOperator ((F').Fiber y)
            (smoothSections (E').Fiber) (smoothSections (E).Fiber) (Jbase i).toLinearMap)
              (associatedSphereTensorCutoffBaseRestriction (a := (E').rank) S (E').Fiber
                A' σ' hA' ((C).center i) (baseAdjointCutoff₁ i)
                (baseAdjointCutoff₁_smooth i) (baseAdjointCutoff₁_support i) y w)).val x) z]
  /-- The actual full reverse horizontal map. -/
  horizontalAdjoint₀ : sphereContext%[(A₁₀).smoothSections →ₗ[ℂ] (A₀₀).smoothSections]
  /-- The actual full reverse horizontal map. -/
  horizontalAdjoint₁ : sphereContext%[(A₁₁).smoothSections →ₗ[ℂ] (A₀₁).smoothSections]
  /-- The full reverse map is the sum of these same pieces. -/
  horizontalAdjoint₀_sum : sphereContext%[horizontalAdjoint₀ = ∑ i, horizontalPieceAdjoint₀ i]
  /-- The full reverse map is the sum of these same pieces. -/
  horizontalAdjoint₁_sum : sphereContext%[horizontalAdjoint₁ = ∑ i, horizontalPieceAdjoint₁ i]
  /-- Integral adjunction for the actual horizontal corner pair. -/
  horizontal₀_adjoint :
    sphereContext%[∀ u v, (∫ z, (atlasMetric₁₀.toCore z).inner ((H₀ u).val z) (v.val z) ∂η) =
        ∫ z, (atlasMetric₀₀.toCore z).inner (u.val z) ((horizontalAdjoint₀ v).val z) ∂η]
  /-- Integral adjunction for the actual horizontal corner pair. -/
  horizontal₁_adjoint :
    sphereContext%[∀ u v, (∫ z, (atlasMetric₁₁.toCore z).inner ((H₁ u).val z) (v.val z) ∂η) =
        ∫ z, (atlasMetric₀₁.toCore z).inner (u.val z) ((horizontalAdjoint₁ v).val z) ∂η]
  /-- Integral adjunction for the original full vertical operator and literal adjoint. -/
  vertical₀_adjoint : sphereContext%[
    let V := associatedSphereTensorVerticalOperator (a := (E).rank)
      S (E).Fiber A σ hA A' σ' hA' QA fiberAtlasOperator_equivariant
    let Va := associatedSphereTensorVerticalOperator (a := (E).rank)
      S (E).Fiber A' σ' hA' A σ hA JA fiberAtlasAdjoint_equivariant
    ∀ u v, (∫ z, (atlasMetric₀₁.toCore z).inner ((V u).val z) (v.val z) ∂η) =
      ∫ z, (atlasMetric₀₀.toCore z).inner (u.val z) ((Va v).val z) ∂η]
  /-- Integral adjunction for the original full vertical operator and literal adjoint. -/
  vertical₁_adjoint :
    sphereContext%[
      let V := associatedSphereTensorVerticalOperator (a := (E').rank)
        S (E').Fiber A σ hA A' σ' hA' QA fiberAtlasOperator_equivariant
      let Va := associatedSphereTensorVerticalOperator (a := (E').rank)
        S (E').Fiber A' σ' hA' A σ hA JA fiberAtlasAdjoint_equivariant
      ∀ u v, (∫ z, (atlasMetric₁₁.toCore z).inner ((V u).val z) (v.val z) ∂η) =
        ∫ z, (atlasMetric₁₀.toCore z).inner (u.val z) ((Va v).val z) ∂η]
  /-- The selected signed graded Green operator. -/
  graded :
    sphereContext%[
      letI : TopologicalSpace (TotalSpace Unit native₀₀.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
      letI : TopologicalSpace (TotalSpace Unit native₁₀.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
      letI : TopologicalSpace (TotalSpace Unit native₀₁.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
      letI : TopologicalSpace (TotalSpace Unit native₁₁.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
      WithLp 2
        (nativeMetric₀₀.L2SectionSpace η × nativeMetric₁₁.L2SectionSpace η) →ₗ.[ℂ]
        WithLp 2 (nativeMetric₁₀.L2SectionSpace η × nativeMetric₀₁.L2SectionSpace η)]
  /-- Its selected formal adjoint, on the same two Hilbert sums. -/
  gradedAdjoint :
    sphereContext%[
      letI : TopologicalSpace (TotalSpace Unit native₀₀.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
      letI : TopologicalSpace (TotalSpace Unit native₁₀.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
      letI : TopologicalSpace (TotalSpace Unit native₀₁.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
      letI : TopologicalSpace (TotalSpace Unit native₁₁.Fiber) :=
        modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
      WithLp 2
        (nativeMetric₁₀.L2SectionSpace η × nativeMetric₀₁.L2SectionSpace η) →ₗ.[ℂ]
        WithLp 2 (nativeMetric₀₀.L2SectionSpace η × nativeMetric₁₁.L2SectionSpace η)]
  /-- The original graphs, crossing identities, finite kernels and general coefficient formula. -/
  graded_spec :
    sphereContext%[
      letI := modelTopology (EuclideanSpace ℂ (Fin native₀₀.rank)) native₀₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin native₁₀.rank)) native₁₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin native₀₁.rank)) native₀₁.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin native₁₁.rank)) native₁₁.Fiber
      let V₀ := associatedSphereTensorVerticalOperator (a := (E).rank)
        S (E).Fiber A σ hA A' σ' hA' QA fiberAtlasOperator_equivariant
      let V₀a := associatedSphereTensorVerticalOperator (a := (E).rank)
        S (E).Fiber A' σ' hA' A σ hA JA fiberAtlasAdjoint_equivariant
      let V₁ := associatedSphereTensorVerticalOperator (a := (E').rank)
        S (E').Fiber A σ hA A' σ' hA' QA fiberAtlasOperator_equivariant
      let V₁a := associatedSphereTensorVerticalOperator (a := (E').rank)
        S (E').Fiber A' σ' hA' A σ hA JA fiberAtlasAdjoint_equivariant
      let S₀₀ := (atlasSmoothSectionEquiv A₀₀
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₀₀.rank) native₀₀.Fiber)
        nativeIso₀₀ nativeIso₀₀_smooth nativeIso₀₀_symm_smooth).trans
          (nativeSmoothSectionLinearEquiv (n := n + r) (r := native₀₀.rank) native₀₀.Fiber)
      let i₀₀ := (nativeMetric₀₀.smoothToL2 η).comp S₀₀.toLinearMap
      let S₁₀ := (atlasSmoothSectionEquiv A₁₀
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₁₀.rank) native₁₀.Fiber)
        nativeIso₁₀ nativeIso₁₀_smooth nativeIso₁₀_symm_smooth).trans
          (nativeSmoothSectionLinearEquiv (n := n + r) (r := native₁₀.rank) native₁₀.Fiber)
      let i₁₀ := (nativeMetric₁₀.smoothToL2 η).comp S₁₀.toLinearMap
      let S₀₁ := (atlasSmoothSectionEquiv A₀₁
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₀₁.rank) native₀₁.Fiber)
        nativeIso₀₁ nativeIso₀₁_smooth nativeIso₀₁_symm_smooth).trans
          (nativeSmoothSectionLinearEquiv (n := n + r) (r := native₀₁.rank) native₀₁.Fiber)
      let i₀₁ := (nativeMetric₀₁.smoothToL2 η).comp S₀₁.toLinearMap
      let S₁₁ := (atlasSmoothSectionEquiv A₁₁
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := native₁₁.rank) native₁₁.Fiber)
        nativeIso₁₁ nativeIso₁₁_smooth nativeIso₁₁_symm_smooth).trans
          (nativeSmoothSectionLinearEquiv (n := n + r) (r := native₁₁.rank) native₁₁.Fiber)
      let i₁₁ := (nativeMetric₁₁.smoothToL2 η).comp S₁₁.toLinearMap
      let X₀ := nativeMetric₀₀.L2SectionSpace η
      let X₁ := nativeMetric₁₁.L2SectionSpace η
      let Y₀ := nativeMetric₁₀.L2SectionSpace η
      let Y₁ := nativeMetric₀₁.L2SectionSpace η
      let Even := WithLp 2 (X₀ × X₁)
      let Odd := WithLp 2 (Y₀ × Y₁)
      let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ
        (X₀) (X₁)
      let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ
        (Y₀) (Y₁)
      let iEven : ((A₀₀).smoothSections × (A₁₁).smoothSections) →ₗ[ℂ] Even :=
        cEven.symm.toLinearMap.comp (i₀₀.prodMap i₁₁)
      let dSmooth : ((A₀₀).smoothSections × (A₁₁).smoothSections) →ₗ[ℂ] Odd :=
        cOdd.symm.toLinearMap.comp
        (((i₁₀.comp H₀).coprod (-(i₁₀.comp V₁a))).prod
          ((i₀₁.comp V₀).coprod (i₀₁.comp horizontalAdjoint₁)))
      let jOdd := cOdd.symm.toLinearMap.comp (i₁₀.prodMap i₀₁)
      let aSmooth := cEven.symm.toLinearMap.comp
        (((i₀₀.comp horizontalAdjoint₀).coprod (i₀₀.comp V₀a)).prod
          ((-(i₁₁.comp V₁)).coprod (i₁₁.comp H₁)))
      graded.IsClosed ∧ gradedAdjoint.IsClosed ∧
      graded.graph = (iEven.prod dSmooth).range.topologicalClosure ∧
      gradedAdjoint.graph = (jOdd.prod aSmooth).range.topologicalClosure ∧
      graded.IsFormalAdjoint gradedAdjoint ∧
      (∀ (s : (A₀₀).smoothSections) (t : (A₁₁).smoothSections),
        inner ℂ ((i₁₀.comp H₀) s) ((i₁₀.comp V₁a) t) =
          inner ℂ ((i₀₁.comp V₀) s) ((i₀₁.comp horizontalAdjoint₁) t)) ∧
      (∀ (s : (A₁₀).smoothSections) (t : (A₀₁).smoothSections),
        inner ℂ ((i₀₀.comp horizontalAdjoint₀) s) ((i₀₀.comp V₀a) t) =
          inner ℂ ((i₁₁.comp V₁) s) ((i₁₁.comp H₁) t)) ∧
      IsClosed (graded.toFun.range : Set Odd) ∧
      FiniteDimensional ℂ graded.ker ∧
      IsClosed (gradedAdjoint.toFun.range : Set Even) ∧
      FiniteDimensional ℂ gradedAdjoint.ker ∧
      ∀ (g : SmoothCotangentMetric (n := n) (M := B))
        (p : AtlasSymbolFunction (n := n) (E).Fiber (E').Fiber),
        let B₀ := nativeSmoothComplexBundleAtlas (n := n) (r := (E).rank) (E).Fiber
        let B₁ := nativeSmoothComplexBundleAtlas (n := n) (r := (E').rank) (E').Fiber
        ∀ (hs : IsSmoothOffZeroAtlasSymbol B₀ B₁ p)
          (hh : IsHomogeneousAtlasSymbol 1 p) (hi : IsEllipticAtlasSymbol p),
          (C).baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
            atlasGlobalPrincipalSymbolClass B₀ B₁ 1
              (atlasRegularizedSymbol B₀ B₁ g 1 p hs hh) →
          analyticIndexOfComponents μ
            (complexKZeroCompactSupportAction
              (cotangentProjection (n := n) (M := B))
              (associatedRepresentationKZero S.toIsPrincipalBundle
                ((Q).smoothEquivariantAnalyticIndex IG σ σ' hσ hσ' hQ hQell))
              (atlasSymbolKClass B₀ B₁ p hs hi)) =
            (Module.finrank ℂ graded.ker : ℤ) - Module.finrank ℂ gradedAdjoint.ker]
  /-- The atlas domain selected once for all later row and approximation constructions. -/
  presentation₀₀ : sphereContext%[AtlasBundlePresentation A₀₀]
  /-- The atlas domain selected once for all later row and approximation constructions. -/
  presentation₁₀ : sphereContext%[AtlasBundlePresentation A₁₀]
  /-- The atlas domain selected once for all later row and approximation constructions. -/
  presentation₀₁ : sphereContext%[AtlasBundlePresentation A₀₁]
  /-- The atlas domain selected once for all later row and approximation constructions. -/
  presentation₁₁ : sphereContext%[AtlasBundlePresentation A₁₁]

variable {s} (g : AssociatedSphereGreenSelection s)

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit g.native₀₀.Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin g.native₀₀.rank)) g.native₀₀.Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit g.native₁₀.Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin g.native₁₀.rank)) g.native₁₀.Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit g.native₀₁.Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin g.native₀₁.rank)) g.native₀₁.Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit g.native₁₁.Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin g.native₁₁.rank)) g.native₁₁.Fiber]

/-- The original smooth-section equivalence for the selected corner ₀₀. -/
def AssociatedSphereGreenSelection.sectionEquiv₀₀ :
    sphereContext%[(A₀₀).smoothSections ≃ₗ[ℂ]
      smoothSections (n := n + r) (r := g.native₀₀.rank) g.native₀₀.Fiber] :=
  sphereContext%[(atlasSmoothSectionEquiv A₀₀
    (nativeSmoothComplexBundleAtlas (n := n + r) (r := g.native₀₀.rank) g.native₀₀.Fiber)
    g.nativeIso₀₀ g.nativeIso₀₀_smooth g.nativeIso₀₀_symm_smooth).trans
      (nativeSmoothSectionLinearEquiv (n := n + r) (r := g.native₀₀.rank) g.native₀₀.Fiber)]

/-- The same metric inclusion of the original smooth sections in corner ₀₀. -/
def AssociatedSphereGreenSelection.inclusion₀₀ :
    sphereContext%[(A₀₀).smoothSections →ₗ[ℂ] g.nativeMetric₀₀.L2SectionSpace η] :=
  sphereContext%[(g.nativeMetric₀₀.smoothToL2 η).comp g.sectionEquiv₀₀.toLinearMap]

/-- The original smooth-section equivalence for the selected corner ₁₀. -/
def AssociatedSphereGreenSelection.sectionEquiv₁₀ :
    sphereContext%[(A₁₀).smoothSections ≃ₗ[ℂ]
      smoothSections (n := n + r) (r := g.native₁₀.rank) g.native₁₀.Fiber] :=
  sphereContext%[(atlasSmoothSectionEquiv A₁₀
    (nativeSmoothComplexBundleAtlas (n := n + r) (r := g.native₁₀.rank) g.native₁₀.Fiber)
    g.nativeIso₁₀ g.nativeIso₁₀_smooth g.nativeIso₁₀_symm_smooth).trans
      (nativeSmoothSectionLinearEquiv (n := n + r) (r := g.native₁₀.rank) g.native₁₀.Fiber)]

/-- The same metric inclusion of the original smooth sections in corner ₁₀. -/
def AssociatedSphereGreenSelection.inclusion₁₀ :
    sphereContext%[(A₁₀).smoothSections →ₗ[ℂ] g.nativeMetric₁₀.L2SectionSpace η] :=
  sphereContext%[(g.nativeMetric₁₀.smoothToL2 η).comp g.sectionEquiv₁₀.toLinearMap]

/-- The original smooth-section equivalence for the selected corner ₀₁. -/
def AssociatedSphereGreenSelection.sectionEquiv₀₁ :
    sphereContext%[(A₀₁).smoothSections ≃ₗ[ℂ]
      smoothSections (n := n + r) (r := g.native₀₁.rank) g.native₀₁.Fiber] :=
  sphereContext%[(atlasSmoothSectionEquiv A₀₁
    (nativeSmoothComplexBundleAtlas (n := n + r) (r := g.native₀₁.rank) g.native₀₁.Fiber)
    g.nativeIso₀₁ g.nativeIso₀₁_smooth g.nativeIso₀₁_symm_smooth).trans
      (nativeSmoothSectionLinearEquiv (n := n + r) (r := g.native₀₁.rank) g.native₀₁.Fiber)]

/-- The same metric inclusion of the original smooth sections in corner ₀₁. -/
def AssociatedSphereGreenSelection.inclusion₀₁ :
    sphereContext%[(A₀₁).smoothSections →ₗ[ℂ] g.nativeMetric₀₁.L2SectionSpace η] :=
  sphereContext%[(g.nativeMetric₀₁.smoothToL2 η).comp g.sectionEquiv₀₁.toLinearMap]

/-- The original smooth-section equivalence for the selected corner ₁₁. -/
def AssociatedSphereGreenSelection.sectionEquiv₁₁ :
    sphereContext%[(A₁₁).smoothSections ≃ₗ[ℂ]
      smoothSections (n := n + r) (r := g.native₁₁.rank) g.native₁₁.Fiber] :=
  sphereContext%[(atlasSmoothSectionEquiv A₁₁
    (nativeSmoothComplexBundleAtlas (n := n + r) (r := g.native₁₁.rank) g.native₁₁.Fiber)
    g.nativeIso₁₁ g.nativeIso₁₁_smooth g.nativeIso₁₁_symm_smooth).trans
      (nativeSmoothSectionLinearEquiv (n := n + r) (r := g.native₁₁.rank) g.native₁₁.Fiber)]

/-- The same metric inclusion of the original smooth sections in corner ₁₁. -/
def AssociatedSphereGreenSelection.inclusion₁₁ :
    sphereContext%[(A₁₁).smoothSections →ₗ[ℂ] g.nativeMetric₁₁.L2SectionSpace η] :=
  sphereContext%[(g.nativeMetric₁₁.smoothToL2 η).comp g.sectionEquiv₁₁.toLinearMap]

/-- The full original vertical operator on the selected corner atlases. -/
def AssociatedSphereGreenSelection.vertical₀ :
    sphereContext%[(A₀₀).smoothSections →ₗ[ℂ] (A₀₁).smoothSections] :=
  sphereContext%[associatedSphereTensorVerticalOperator (a := (E).rank)
    S (E).Fiber A σ hA A' σ' hA' QA g.fiberAtlasOperator_equivariant]

/-- The literal fiber-adjoint vertical operator on those same atlases. -/
def AssociatedSphereGreenSelection.verticalAdjoint₀ :
    sphereContext%[(A₀₁).smoothSections →ₗ[ℂ] (A₀₀).smoothSections] :=
  sphereContext%[associatedSphereTensorVerticalOperator (a := (E).rank)
    S (E).Fiber A' σ' hA' A σ hA JA g.fiberAtlasAdjoint_equivariant]

/-- The full original vertical operator on the selected corner atlases. -/
def AssociatedSphereGreenSelection.vertical₁ :
    sphereContext%[(A₁₀).smoothSections →ₗ[ℂ] (A₁₁).smoothSections] :=
  sphereContext%[associatedSphereTensorVerticalOperator (a := (E').rank)
    S (E').Fiber A σ hA A' σ' hA' QA g.fiberAtlasOperator_equivariant]

/-- The literal fiber-adjoint vertical operator on those same atlases. -/
def AssociatedSphereGreenSelection.verticalAdjoint₁ :
    sphereContext%[(A₁₁).smoothSections →ₗ[ℂ] (A₁₀).smoothSections] :=
  sphereContext%[associatedSphereTensorVerticalOperator (a := (E').rank)
    S (E').Fiber A' σ' hA' A σ hA JA g.fiberAtlasAdjoint_equivariant]

/-- The actual even Hilbert sum of the two selected native corners. -/
abbrev AssociatedSphereGreenSelection.Even : Type _ :=
  sphereContext%[WithLp 2 (g.nativeMetric₀₀.L2SectionSpace η × g.nativeMetric₁₁.L2SectionSpace η)]

/-- The actual odd Hilbert sum of the two selected native corners. -/
abbrev AssociatedSphereGreenSelection.Odd : Type _ :=
  sphereContext%[WithLp 2 (g.nativeMetric₁₀.L2SectionSpace η × g.nativeMetric₀₁.L2SectionSpace η)]

/-! Descend the four representative tensor pairings once for later independent consumers. -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected native isometry preserves the descended pure-tensor pairing. -/
theorem AssociatedSphereGreenSelection.nativeIso₀₀_pairing_tmul
    (z : Z) (u v : (E).Fiber (πS z)) (a b : D z) :
    sphereContext%[g.nativeMetric₀₀.pairing z (g.nativeIso₀₀.linearEquiv z (u ⊗ₜ[ℂ] a))
      (g.nativeIso₀₀.linearEquiv z (v ⊗ₜ[ℂ] b)) =
        ((h).toCore (πS z)).inner u v *
          (associatedEquivariantMetricCore S.toIsPrincipalBundle σ
            (k).toContinuousHermitianMetric z).inner a b] := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z :=
    linearModelChartedSpace (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z :=
    isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  -- The native isometry reduces the assertion to the original quotient tensor metric.
  apply (g.nativeIso₀₀_isometry z (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)).trans
  induction z using Quotient.inductionOn with
  | «h» w =>
    rcases w with ⟨p₀, y⟩
    obtain ⟨a₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p₀ y rfl).surjective a
    obtain ⟨b₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p₀ y rfl).surjective b
    -- Both representatives use the same invariant metric that defines the descended core.
    exact (g.atlasMetric₀₀_pure p₀ y u v a₀ b₀).trans
      (congrArg (fun c : ℂ ↦ (h).pairing (projection p₀) u v * c)
        (associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ
          (k).toContinuousHermitianMetric s.fiberSourceMetric_invariant p₀ y rfl a₀ b₀).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected native isometry preserves the descended pure-tensor pairing. -/
theorem AssociatedSphereGreenSelection.nativeIso₁₀_pairing_tmul
    (z : Z) (u v : (E').Fiber (πS z)) (a b : D z) :
    sphereContext%[g.nativeMetric₁₀.pairing z (g.nativeIso₁₀.linearEquiv z (u ⊗ₜ[ℂ] a))
      (g.nativeIso₁₀.linearEquiv z (v ⊗ₜ[ℂ] b)) =
        ((h').toCore (πS z)).inner u v *
          (associatedEquivariantMetricCore S.toIsPrincipalBundle σ
            (k).toContinuousHermitianMetric z).inner a b] := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z :=
    linearModelChartedSpace (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z :=
    isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  -- The native isometry reduces the assertion to the original quotient tensor metric.
  apply (g.nativeIso₁₀_isometry z (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)).trans
  induction z using Quotient.inductionOn with
  | «h» w =>
    rcases w with ⟨p₀, y⟩
    obtain ⟨a₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p₀ y rfl).surjective a
    obtain ⟨b₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p₀ y rfl).surjective b
    -- Both representatives use the same invariant metric that defines the descended core.
    exact (g.atlasMetric₁₀_pure p₀ y u v a₀ b₀).trans
      (congrArg (fun c : ℂ ↦ (h').pairing (projection p₀) u v * c)
        (associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ
          (k).toContinuousHermitianMetric s.fiberSourceMetric_invariant p₀ y rfl a₀ b₀).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected native isometry preserves the descended pure-tensor pairing. -/
theorem AssociatedSphereGreenSelection.nativeIso₀₁_pairing_tmul
    (z : Z) (u v : (E).Fiber (πS z)) (a b : D' z) :
    sphereContext%[g.nativeMetric₀₁.pairing z (g.nativeIso₀₁.linearEquiv z (u ⊗ₜ[ℂ] a))
      (g.nativeIso₀₁.linearEquiv z (v ⊗ₜ[ℂ] b)) =
        ((h).toCore (πS z)).inner u v *
          (associatedEquivariantMetricCore S.toIsPrincipalBundle σ'
            (k').toContinuousHermitianMetric z).inner a b] := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z :=
    linearModelChartedSpace (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z :=
    isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  -- The native isometry reduces the assertion to the original quotient tensor metric.
  apply (g.nativeIso₀₁_isometry z (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)).trans
  induction z using Quotient.inductionOn with
  | «h» w =>
    rcases w with ⟨p₀, y⟩
    obtain ⟨a₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ' p₀ y rfl).surjective a
    obtain ⟨b₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ' p₀ y rfl).surjective b
    -- Both representatives use the same invariant metric that defines the descended core.
    exact (g.atlasMetric₀₁_pure p₀ y u v a₀ b₀).trans
      (congrArg (fun c : ℂ ↦ (h).pairing (projection p₀) u v * c)
        (associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ'
          (k').toContinuousHermitianMetric s.fiberTargetMetric_invariant p₀ y rfl a₀ b₀).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected native isometry preserves the descended pure-tensor pairing. -/
theorem AssociatedSphereGreenSelection.nativeIso₁₁_pairing_tmul
    (z : Z) (u v : (E').Fiber (πS z)) (a b : D' z) :
    sphereContext%[g.nativeMetric₁₁.pairing z (g.nativeIso₁₁.linearEquiv z (u ⊗ₜ[ℂ] a))
      (g.nativeIso₁₁.linearEquiv z (v ⊗ₜ[ℂ] b)) =
        ((h').toCore (πS z)).inner u v *
          (associatedEquivariantMetricCore S.toIsPrincipalBundle σ'
            (k').toContinuousHermitianMetric z).inner a b] := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z :=
    linearModelChartedSpace (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z :=
    isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  -- The native isometry reduces the assertion to the original quotient tensor metric.
  apply (g.nativeIso₁₁_isometry z (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)).trans
  induction z using Quotient.inductionOn with
  | «h» w =>
    rcases w with ⟨p₀, y⟩
    obtain ⟨a₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ' p₀ y rfl).surjective a
    obtain ⟨b₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ' p₀ y rfl).surjective b
    -- Both representatives use the same invariant metric that defines the descended core.
    exact (g.atlasMetric₁₁_pure p₀ y u v a₀ b₀).trans
      (congrArg (fun c : ℂ ↦ (h').pairing (projection p₀) u v * c)
        (associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ'
          (k').toContinuousHermitianMetric s.fiberTargetMetric_invariant p₀ y rfl a₀ b₀).symm)

end AtiyahSinger

end AuxiliaryGreenTypes


section AuxiliaryNativeSumsGeneric

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct Topology

attribute [local instance] sumTopology

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {n : ℕ} {M ι : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  (N₀₀ N₁₀ N₀₁ N₁₁ : SmoothFiniteComplexBundle (n := n) M)
  (E₀ E₁ F₀ F₁ : M → Type*)
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]
  [∀ x, FiniteDimensional ℂ (E₀ x)] [∀ x, FiniteDimensional ℂ (E₁ x)]
  [∀ x, FiniteDimensional ℂ (F₀ x)] [∀ x, FiniteDimensional ℂ (F₁ x)]

variable
  (e₀₀ : ∀ x, (E₀ x ⊗[ℂ] F₀ x) ≃ₗ[ℂ] N₀₀.Fiber x)
  (e₁₀ : ∀ x, (E₁ x ⊗[ℂ] F₀ x) ≃ₗ[ℂ] N₁₀.Fiber x)
  (e₀₁ : ∀ x, (E₀ x ⊗[ℂ] F₁ x) ≃ₗ[ℂ] N₀₁.Fiber x)
  (e₁₁ : ∀ x, (E₁ x ⊗[ℂ] F₁ x) ≃ₗ[ℂ] N₁₁.Fiber x)
  (k₀₀ : SmoothHermitianMetric (n := n) (r := N₀₀.rank) N₀₀.Fiber)
  (k₁₀ : SmoothHermitianMetric (n := n) (r := N₁₀.rank) N₁₀.Fiber)
  (k₀₁ : SmoothHermitianMetric (n := n) (r := N₀₁.rank) N₀₁.Fiber)
  (k₁₁ : SmoothHermitianMetric (n := n) (r := N₁₁.rank) N₁₁.Fiber)
  (c₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
  (c₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
  (d₀ : ∀ x, InnerProductSpace.Core ℂ (F₀ x))
  (d₁ : ∀ x, InnerProductSpace.Core ℂ (F₁ x))
  (hk₁₀ : ∀ x u v a b, k₁₀.pairing x (e₁₀ x (u ⊗ₜ[ℂ] a))
    (e₁₀ x (v ⊗ₜ[ℂ] b)) = (c₁ x).inner u v * (d₀ x).inner a b)
  (hk₀₁ : ∀ x u v a b, k₀₁.pairing x (e₀₁ x (u ⊗ₜ[ℂ] a))
    (e₀₁ x (v ⊗ₜ[ℂ] b)) = (c₀ x).inner u v * (d₁ x).inner a b)
  (hk₁₁ : ∀ x u v a b, k₁₁.pairing x (e₁₁ x (u ⊗ₜ[ℂ] a))
    (e₁₁ x (v ⊗ₜ[ℂ] b)) = (c₁ x).inner u v * (d₁ x).inner a b)
  (U₀Family : ι → PseudodifferentialOperator (n := n) (r := N₀₀.rank) (q := N₁₀.rank)
    N₀₀.Fiber N₁₀.Fiber μ 1)
  (U₁Family : ι → PseudodifferentialOperator (n := n) (r := N₀₁.rank) (q := N₁₁.rank)
    N₀₁.Fiber N₁₁.Fiber μ 1)
  (V₀Family : ι → PseudodifferentialOperator (n := n) (r := N₀₀.rank) (q := N₀₁.rank)
    N₀₀.Fiber N₀₁.Fiber μ 1)
  (V₁Family : ι → PseudodifferentialOperator (n := n) (r := N₁₀.rank) (q := N₁₁.rank)
    N₁₀.Fiber N₁₁.Fiber μ 1)
  (a₀Family : ι → globalSymbolSpace (n := n) (r := N₀₀.rank) (q := N₁₀.rank)
    N₀₀.Fiber N₁₀.Fiber 1)
  (a₁Family : ι → globalSymbolSpace (n := n) (r := N₀₁.rank) (q := N₁₁.rank)
    N₀₁.Fiber N₁₁.Fiber 1)
  (b₀Family : ι → globalSymbolSpace (n := n) (r := N₀₀.rank) (q := N₀₁.rank)
    N₀₀.Fiber N₀₁.Fiber 1)
  (b₁Family : ι → globalSymbolSpace (n := n) (r := N₁₀.rank) (q := N₁₁.rank)
    N₁₀.Fiber N₁₁.Fiber 1)
  (ha₀ : ∀ t, (U₀Family t).principalSymbol =
    globalPrincipalSymbolClass N₀₀.Fiber N₁₀.Fiber 1 (a₀Family t))
  (ha₁ : ∀ t, (U₁Family t).principalSymbol =
    globalPrincipalSymbolClass N₀₁.Fiber N₁₁.Fiber 1 (a₁Family t))
  (hb₀ : ∀ t, (V₀Family t).principalSymbol =
    globalPrincipalSymbolClass N₀₀.Fiber N₀₁.Fiber 1 (b₀Family t))
  (hb₁ : ∀ t, (V₁Family t).principalSymbol =
    globalPrincipalSymbolClass N₁₀.Fiber N₁₁.Fiber 1 (b₁Family t))
  (pfFamily : ι → ∀ x, CotangentFiber (n := n) x → E₀ x →ₗ[ℂ] E₁ x)
  (qfFamily : ι → ∀ x, CotangentFiber (n := n) x → F₀ x →ₗ[ℂ] F₁ x)
  (ha₀tensor : ∀ t x ξ u v, (a₀Family t).val x ξ (e₀₀ x (u ⊗ₜ[ℂ] v)) =
    e₁₀ x (pfFamily t x ξ u ⊗ₜ[ℂ] v))
  (ha₁tensor : ∀ t x ξ u v, (a₁Family t).val x ξ (e₀₁ x (u ⊗ₜ[ℂ] v)) =
    e₁₁ x (pfFamily t x ξ u ⊗ₜ[ℂ] v))
  (hb₀tensor : ∀ t x ξ u v, (b₀Family t).val x ξ (e₀₀ x (u ⊗ₜ[ℂ] v)) =
    e₀₁ x (u ⊗ₜ[ℂ] qfFamily t x ξ v))
  (hb₁tensor : ∀ t x ξ u v, (b₁Family t).val x ξ (e₁₀ x (u ⊗ₜ[ℂ] v)) =
    e₁₁ x (u ⊗ₜ[ℂ] qfFamily t x ξ v))

set_option genInjectivity false in
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
/-- Raw native sums and the common family, without graph or index certificates. -/
structure NativeGradedFamilySelection where
  /-- The selected even native sum. -/
  nativePlus : SmoothFiniteComplexBundle (n := n) M
  /-- The selected odd native sum. -/
  nativeMinus : SmoothFiniteComplexBundle (n := n) M
  /-- The specified even sum isomorphism. -/
  sumPlus :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    Iso (N₀₀.Fiber ×ᵇ N₁₁.Fiber) nativePlus.Fiber
  /-- The specified odd sum isomorphism. -/
  sumMinus :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    Iso (N₁₀.Fiber ×ᵇ N₀₁.Fiber) nativeMinus.Fiber
  /-- Smoothness of the specified summand inclusion. -/
  plus₀_smooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    IsSmoothBundleMap (n := n) (r := N₀₀.rank) (q := nativePlus.rank)
      (fun z ↦ (sumPlus.linearEquiv z).toLinearMap.comp
        (LinearMap.inl ℂ (N₀₀.Fiber z) (N₁₁.Fiber z)))
  /-- Smoothness of the specified summand inclusion. -/
  plus₁_smooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    IsSmoothBundleMap (n := n) (r := N₁₁.rank) (q := nativePlus.rank)
      (fun z ↦ (sumPlus.linearEquiv z).toLinearMap.comp
        (LinearMap.inr ℂ (N₀₀.Fiber z) (N₁₁.Fiber z)))
  /-- Smoothness of the specified summand inclusion. -/
  minus₀_smooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    IsSmoothBundleMap (n := n) (r := N₁₀.rank) (q := nativeMinus.rank)
      (fun z ↦ (sumMinus.linearEquiv z).toLinearMap.comp
        (LinearMap.inl ℂ (N₁₀.Fiber z) (N₀₁.Fiber z)))
  /-- Smoothness of the specified summand inclusion. -/
  minus₁_smooth :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    IsSmoothBundleMap (n := n) (r := N₀₁.rank) (q := nativeMinus.rank)
      (fun z ↦ (sumMinus.linearEquiv z).toLinearMap.comp
        (LinearMap.inr ℂ (N₁₀.Fiber z) (N₀₁.Fiber z)))
  /-- The metric used by the literal formal adjoint. -/
  metricPlus : SmoothHermitianMetric (n := n) (r := nativePlus.rank) nativePlus.Fiber
  /-- The metric used by the literal formal adjoint. -/
  metricMinus : SmoothHermitianMetric (n := n) (r := nativeMinus.rank) nativeMinus.Fiber
  /-- The selected presentation of this native sum. -/
  presentationPlus : SmoothBundlePresentation (n := n) (r := nativePlus.rank) nativePlus.Fiber
  /-- The selected presentation of this native sum. -/
  presentationMinus : SmoothBundlePresentation (n := n) (r := nativeMinus.rank) nativeMinus.Fiber
  /-- The two fixed native corner presentations. -/
  cornerPresentationsPlus :
    let bundles : Fin 2 → SmoothFiniteComplexBundle (n := n) M := ![N₀₀, N₁₁]
    ∀ i, SmoothBundlePresentation (n := n) (r := (bundles i).rank) (bundles i).Fiber
  /-- The two fixed native corner presentations. -/
  cornerPresentationsMinus :
    let bundles : Fin 2 → SmoothFiniteComplexBundle (n := n) M := ![N₁₀, N₀₁]
    ∀ i, SmoothBundlePresentation (n := n) (r := (bundles i).rank) (bundles i).Fiber
  /-- The single cutoff family used by both adjacent comparisons. -/
  cutoffFamily : ι → PseudodifferentialOperator (n := n)
    (r := nativePlus.rank) (q := nativeMinus.rank) nativePlus.Fiber nativeMinus.Fiber μ 1
  /-- The actual signed blocks of the selected family. -/
  cutoff_blocks :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    let Φ := smoothSectionSumEquiv sumPlus.linearEquiv plus₀_smooth plus₁_smooth
    let Ψ := smoothSectionSumEquiv sumMinus.linearEquiv minus₀_smooth minus₁_smooth
    ∀ t u v, (cutoffFamily t).toLinearMap (Φ (u, v)) =
      Ψ ((U₀Family t).toLinearMap u -
          ((V₁Family t).metricFormalAdjoint k₁₀ k₁₁).toLinearMap v,
        (V₀Family t).toLinearMap u +
          ((U₁Family t).metricFormalAdjoint k₀₁ k₁₁).toLinearMap v)
  /-- The signed blocks of the literal metric adjoint. -/
  adjoint_cutoff_blocks :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    let Φ := smoothSectionSumEquiv sumPlus.linearEquiv plus₀_smooth plus₁_smooth
    let Ψ := smoothSectionSumEquiv sumMinus.linearEquiv minus₀_smooth minus₁_smooth
    ∀ t u v, ((cutoffFamily t).metricFormalAdjoint metricPlus metricMinus).toLinearMap
        (Ψ (u, v)) =
      Φ (((U₀Family t).metricFormalAdjoint k₀₀ k₁₀).toLinearMap u +
          ((V₀Family t).metricFormalAdjoint k₀₀ k₀₁).toLinearMap v,
        -(V₁Family t).toLinearMap u + (U₁Family t).toLinearMap v)
  /-- The reciprocal principal symbol of this same cutoff. -/
  cutoff_symbol :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativePlus.rank)) nativePlus.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin nativeMinus.rank)) nativeMinus.Fiber
    ∀ t,
    ∃ (pi : ∀ z, CotangentFiber (n := n) z → E₁ z →ₗ[ℂ] E₀ z)
      (qi : ∀ z, CotangentFiber (n := n) z → F₁ z →ₗ[ℂ] F₀ z),
      (∀ z ξ u v, (c₁ z).inner (pfFamily t z ξ u) v = (c₀ z).inner u (pi z ξ v)) ∧
      (∀ z ξ u v, (d₁ z).inner (qfFamily t z ξ u) v = (d₀ z).inner u (qi z ξ v)) ∧
      ∃ qK : globalSymbolSpace (n := n)
          (r := nativePlus.rank) (q := nativeMinus.rank) nativePlus.Fiber nativeMinus.Fiber 1,
        (cutoffFamily t).principalSymbol =
          globalPrincipalSymbolClass nativePlus.Fiber nativeMinus.Fiber 1 qK ∧
        ∀ z ξ (u : E₀ z ⊗[ℂ] F₀ z) (v : E₁ z ⊗[ℂ] F₁ z),
          let w := reciprocalTensorSymbol (pfFamily t z ξ) (pi z ξ) (qfFamily t z ξ) (qi z ξ) (u, v)
          qK.val z ξ (sumPlus.linearEquiv z
            (e₀₀ z u, e₁₁ z v)) =
              sumMinus.linearEquiv z (e₁₀ z w.1, e₀₁ z w.2)

set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
include hk₁₀ hk₀₁ hk₁₁ ha₀ ha₁ hb₀ hb₁ ha₀tensor ha₁tensor hb₀tensor hb₁tensor in
/-- Select the common sums and family from the existing tensor-family construction. -/
theorem nonempty_nativeGradedFamilySelection :
    Nonempty (NativeGradedFamilySelection (μ := μ)
      («N₀₀» := N₀₀) («N₁₀» := N₁₀) («N₀₁» := N₀₁)
      («N₁₁» := N₁₁) (E₀ := E₀) (E₁ := E₁)
      (F₀ := F₀) (F₁ := F₁) («e₀₀» := e₀₀)
      («e₁₀» := e₁₀) («e₀₁» := e₀₁) («e₁₁» := e₁₁)
      («k₀₀» := k₀₀) («k₁₀» := k₁₀) («k₀₁» := k₀₁)
      («k₁₁» := k₁₁) («c₀» := c₀) («c₁» := c₁)
      («d₀» := d₀) («d₁» := d₁) (U₀Family := U₀Family)
      (U₁Family := U₁Family) (V₀Family := V₀Family) (V₁Family := V₁Family)
      («pfFamily» := pfFamily) («qfFamily» := qfFamily)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  have hFamily := exists_native_graded_family_of_tensor_symbols
    N₀₀ N₁₀ N₀₁ N₁₁ E₀ E₁ F₀ F₁ e₀₀ e₁₀ e₀₁ e₁₁
    k₀₀ k₁₀ k₀₁ k₁₁ c₀ c₁ d₀ d₁ hk₁₀ hk₀₁ hk₁₁
    U₀Family U₁Family V₀Family V₁Family a₀Family a₁Family b₀Family b₁Family
    ha₀ ha₁ hb₀ hb₁ pfFamily qfFamily ha₀tensor ha₁tensor hb₀tensor hb₁tensor
  obtain ⟨Nplus, Nminus, _hNplus, _hNminus, hSums⟩ := hFamily
  let := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
  obtain ⟨ePlus, eMinus, hPlus₀, hPlus₁, hMinus₀, hMinus₁, kPlus, kMinus,
    _hkPlus, _hkMinus, hFixed⟩ := hSums
  let AA : Fin 2 → SmoothFiniteComplexBundle (n := n) M := ![N₀₀, N₁₁]
  let BB : Fin 2 → SmoothFiniteComplexBundle (n := n) M := ![N₁₀, N₀₁]
  let DD (i : Fin 2) : SmoothBundlePresentation (n := n)
      (r := (AA i).rank) (AA i).Fiber :=
    Classical.choice (nonempty_smoothBundlePresentation (AA i).Fiber)
  let HH (i : Fin 2) : SmoothBundlePresentation (n := n)
      (r := (BB i).rank) (BB i).Fiber :=
    Classical.choice (nonempty_smoothBundlePresentation (BB i).Fiber)
  obtain ⟨Dplus⟩ := nonempty_smoothBundlePresentation (n := n) (r := Nplus.rank) Nplus.Fiber
  obtain ⟨Dminus⟩ := nonempty_smoothBundlePresentation (n := n) (r := Nminus.rank) Nminus.Fiber
  -- Presentations are fixed before the family is selected, for every parameter together.
  have hAt (t : ι) := hFixed DD HH Dplus Dminus t
  let family (t : ι) : PseudodifferentialOperator (n := n)
      (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber μ 1 := (hAt t).choose
  exact ⟨{
    nativePlus := Nplus
    nativeMinus := Nminus
    sumPlus := ePlus
    sumMinus := eMinus
    plus₀_smooth := hPlus₀
    plus₁_smooth := hPlus₁
    minus₀_smooth := hMinus₀
    minus₁_smooth := hMinus₁
    metricPlus := kPlus
    metricMinus := kMinus
    presentationPlus := Dplus
    presentationMinus := Dminus
    cornerPresentationsPlus := DD
    cornerPresentationsMinus := HH
    cutoffFamily := family
    cutoff_blocks := fun t ↦ (hAt t).choose_spec.1
    adjoint_cutoff_blocks := fun t ↦ (hAt t).choose_spec.2.1
    cutoff_symbol := fun t ↦ (hAt t).choose_spec.2.2.2 }⟩

end AtiyahSinger

end AuxiliaryNativeSumsGeneric


section AuxiliaryCutoffSequence

namespace AtiyahSinger

section AssociatedSphereCutoffSequence

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open Filter
open scoped Topology

/-- The positive reciprocal cutoff sequence used to choose the shared comparison parameter. -/
def associatedSphereCutoffSequence (m : ℕ) : {ε : ℝ // 0 < ε ∧ ε ≤ 1} :=
  ⟨1 / ((m : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg m)⟩

/-- The fixed reciprocal cutoff parameters tend to zero. -/
theorem associatedSphereCutoffSequence_tendsto :
    Tendsto (fun m ↦ (associatedSphereCutoffSequence m).val) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

end AssociatedSphereCutoffSequence

end AtiyahSinger

end AuxiliaryCutoffSequence


section AuxiliaryVerticalApproximation

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
  [T2Space B]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection («F» := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [MeasurableSpace Z] [BorelSpace Z] in
/-- A fixed vertical family has atlas principal symbols and two uniform residual error bounds.
The residual retains its support and fiber formula for the native L² realization. -/
theorem exists_associatedSphereTensorVertical_atlas_approximation
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ j, tsupport (J.cutoff j) ⊆ (S.trivialization (b j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    ∀ (Q : AtlasPseudodifferentialOperator A A' 1)
      (hQ : Q.IsEquivariant IG σ σ' hA hA')
      (Npiece : ℕ) (Lq : Fin Npiece → AtlasPseudodifferentialPiece A A' 1),
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D')
      letI := associatedSphereChartedSpace S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI := isManifold_linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI (x : B) : FiniteDimensional ℂ (E x) :=
        VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT'),
        let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
        let Eps := {ε : ℝ // 0 < ε ∧ ε ≤ 1}
        ∃ (Cp Cn : ℝ) (Pat : Eps → AtlasPseudodifferentialOperator AT AT' 1)
          (pAt : Eps → atlasGlobalSymbolSpace AT AT' 1)
          (Wj : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections),
          0 ≤ Cp ∧ 0 ≤ Cn ∧
          (∀ j (u : AT.smoothSections) z,
            πS z ∉ tsupport (J.cutoff j) → (Wj j u).val z = 0) ∧
          (∀ j (u : AT.smoothSections) x, x ∈ (J.chart j).source →
            x ∈ (S.trivialization (b j)).baseSet → x ∈ (J.frame j).baseSet →
            ∀ y : OrthogonalSphere r,
              let q := (S.trivialization (b j)).toOpenPartialHomeomorph.symm (x, 1)
              (Wj j u).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
                (J.cutoff j x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                  ((tensorSectionOperator (E (projection q)) A.smoothSections
                    A'.smoothSections (Q.toLinearMap - ∑ j, (Lq j).toLinearMap)
                    (associatedSphereTensorFiberRestriction (a := a)
                      S E A σ hA q u)).val y)) ∧
          (∀ ε, (Pat ε).principalSymbol = atlasGlobalPrincipalSymbolClass AT AT' 1 (pAt ε)) ∧
          (∀ ε z ξ, (pAt ε).val z ξ =
            TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS z)))
              (verticalCutoffFactor S E A σ A' σ' hA hA' J b Npiece Lq ε.val z ξ)) ∧
          (∀ ε u, ‖Lo.smoothToSobolev 0
              ((Pat ε).toLinearMap u - V u + (∑ j, Wj j) u)‖ ≤
            Cp * ε.val * ‖Li.smoothToSobolev 1 u‖) ∧
          (∀ ε u, ‖Lo.smoothToSobolev (-1)
              ((Pat ε).toLinearMap u - V u + (∑ j, Wj j) u)‖ ≤
            Cn * ε.val * ‖Li.smoothToSobolev 0 u‖) := by
  as_aux_lemma =>
    classical
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    intro A A' hA hA' Q hQ Npiece Lq
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D)
    let : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D')
    let := associatedSphereChartedSpace S
    let := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let (x : B) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
    intro AT AT' Li Lo V Eps
    -- Obtain the fixed atlas family and its common residual estimates.
    have hreg0 := exists_associatedSphereTensorVerticalGlobalFamily_regularization
      (a := a) S E A σ A' σ' hA hA' Q hQ Npiece Lq J b hJ Li Lo
    -- Retain the regularization cutoffs and estimates from one positive family certificate.
    let γ0 := hreg0.choose
    have γ0Rest := hreg0.choose_spec
    have hγ0 := γ0Rest.choose
    have hγ0Rest := γ0Rest.choose_spec
    have hcγ0 := hγ0Rest.choose
    have hcγ0Rest := hγ0Rest.choose_spec
    have hsγ0 := hcγ0Rest.choose
    have hsγ0Rest := hcγ0Rest.choose_spec
    have hbγ0 := hsγ0Rest.choose
    have hbγ0Rest := hsγ0Rest.choose_spec
    let κ0 := hbγ0Rest.choose
    have κ0Rest := hbγ0Rest.choose_spec
    have hκ0 := κ0Rest.choose
    have hκ0Rest := κ0Rest.choose_spec
    have hcκ0 := hκ0Rest.choose
    have hcκ0Rest := hκ0Rest.choose_spec
    have hsκ0 := hcκ0Rest.choose
    have hsκ0Rest := hcκ0Rest.choose_spec
    have hγone0 := hsκ0Rest.1
    have hκone0 := hsκ0Rest.2.1
    have hκin0 := hsκ0Rest.2.2.1
    have hIO0 := hsκ0Rest.2.2.2
    let I0 := hIO0.choose
    let O0 := hIO0.choose_spec.choose
    have hIOData0 := hIO0.choose_spec.choose_spec
    have hI0 := hIOData0.1
    have hO0 := hIOData0.2.1
    have hTR0 := hIOData0.2.2
    let Tj0 := hTR0.choose
    let Rb0 := hTR0.choose_spec.choose
    have hTRData0 := hTR0.choose_spec.choose_spec
    have hTj0 := hTRData0.1
    have hRb0 := hTRData0.2.1
    have hW0 := hTRData0.2.2
    let W0 := hW0.choose
    have hWData0 := hW0.choose_spec
    have hWV₀ := hWData0.1
    have hWs0 := hWData0.2.1
    have hWr0 := hWData0.2.2.1
    have hBound0 := hWData0.2.2.2
    let K0 := hBound0.choose
    have hK0 := hBound0.choose_spec.1
    have hpos0 := hBound0.choose_spec.2
    let Co0 (k : Fin J.size) (j : Fin Npiece) : BundleChartCutoff E (J.chart k) := {
      J.chartCutoff E k with
        cutoff := γ0 k j
        smooth_cutoff := hγ0 k j
        compact_support := hcγ0 k j
        support_subset := hsγ0 k j }
    have hneg0 := associatedSphereTensorVerticalGlobal_error_sobolev_neg_one_bound
      (a := a) S E A σ A' σ' hA hA' Q hQ Npiece Lq J b hJ
      Co0 hbγ0 κ0 hκ0 hcκ0 hsκ0 I0 O0 hI0 hO0 Li Lo Tj0
      (fun k j w ↦ ⟨(hTj0 k j w).choose, (hTj0 k j w).choose_spec.1,
        (hTj0 k j w).choose_spec.2.2.1⟩) W0 hWV₀
    -- Keep the negative constant and its uniform estimate from one original certificate.
    let Kn0 : ℝ := hneg0.choose
    have hKn0 : 0 ≤ Kn0 := hneg0.choose_spec.1
    have hnegBound0 := hneg0.choose_spec.2
    -- All three families and their certificates use the same original choices.
    have hcutV₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := hpos0 ε hε hε1
    let QV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hcutV₀ ε hε hε1).choose
    let UVloc₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hcutV₀ ε hε hε1).choose_spec.choose
    let RVε₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hcutV₀ ε hε hε1).choose_spec.choose_spec.choose
    have hDataV₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hcutV₀ ε hε hε1).choose_spec.choose_spec.choose_spec
    have hprincipalV₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      exists_associatedSphereTensorVerticalGlobal_principalSymbol
        (a := a) S E A σ A' σ' hA hA' J b hJ
        (fun _ ↦ Npiece) (fun _ ↦ Lq)
        γ0 hγ0 hcγ0 hsγ0 hbγ0 κ0 hκ0 hcκ0 hsκ0 hκin0
        I0 O0 hI0 hO0 ε hε (QV₀Family ε hε hε1) (UVloc₀Family ε hε hε1)
        (hDataV₀ ε hε hε1).1 (hDataV₀ ε hε hε1).2.1
    -- The symbol and atlas operator are selected from one parameterized certificate.
    let gV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hprincipalV₀ ε hε hε1).choose
    have hgV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hprincipalV₀ ε hε hε1).choose_spec.1
    let Vat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hprincipalV₀ ε hε hε1).choose_spec.2.choose
    have hVat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hprincipalV₀ ε hε hε1).choose_spec.2.choose_spec.1
    have hsVat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
      (hprincipalV₀ ε hε hε1).choose_spec.2.choose_spec.2
    let sV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
        atlasGlobalSymbolSpace AT AT' 1 := ∑ i, ∑ j, (gV₀Family ε hε hε1) i j
    have hsV₀factor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
        (z : Z) (ξ : CotangentFiber (n := n + r) z) :
        (sV₀Family ε hε hε1).val z ξ =
          TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS z)))
            (verticalCutoffFactor S E A σ A' σ' hA hA' J b Npiece Lq ε z ξ) := by
      let ev : atlasGlobalSymbolSpace AT AT' 1 →ₗ[ℂ] (T z →ₗ[ℂ] T' z) :=
        (LinearMap.proj ξ).comp ((LinearMap.proj z).comp
          (atlasGlobalSymbolSpace AT AT' 1).subtype)
      have heval := (map_sum ev
        (fun i : Fin J.size ↦ ∑ j : Fin Npiece, (gV₀Family ε hε hε1) i j)
          Finset.univ).trans
            (Finset.sum_congr rfl (fun i _ ↦ map_sum ev
              (fun j : Fin Npiece ↦ (gV₀Family ε hε hε1) i j) Finset.univ))
      refine heval.trans ?_
      have hj (j : Fin J.size) := associatedSphereTensorVerticalSymbol_eq_finiteTensorFactor
        (a := a) S E A σ A' σ' hA hA' (b j) (J.chart j)
        (J.chartCutoff E j)
        (fun _ hx ↦ hJ j (J.chartCutoff_support_subset E j hx)) Npiece Lq
        (γ0 j) (hγ0 j) (hcγ0 j) (hsγ0 j) (hbγ0 j) (hγone0 j)
        (κ0 j) (hκ0 j) (hcκ0 j) (hsκ0 j) (hκone0 j)
        ε (fun k ↦ ((gV₀Family ε hε hε1) j k).val)
        ((hgV₀Family ε hε hε1) j) z ξ
      change (∑ j : Fin J.size, ∑ k, ((gV₀Family ε hε hε1) j k).val z ξ) = _
      rw [Finset.sum_congr rfl (fun j _ ↦ hj j)]
      change (∑ j : Fin J.size, (LinearMap.lTensorHom (R := ℂ) (E (πS z))) _) =
        (LinearMap.lTensorHom (R := ℂ) (E (πS z))) _
      exact (map_sum (LinearMap.lTensorHom (R := ℂ) (E (πS z))) _ Finset.univ).symm
    have hPairedV₀ (ε : Eps) (u : AT.smoothSections) :
        (‖Lo.smoothToSobolev 0
            ((Vat₀Family ε.val ε.property.1 ε.property.2).toLinearMap u - V u + (∑ k, W0 k) u)‖ ≤
              K0 * ε.val * ‖Li.smoothToSobolev 1 u‖) ∧
        (‖Lo.smoothToSobolev (-1)
            ((Vat₀Family ε.val ε.property.1 ε.property.2).toLinearMap u - V u + (∑ k, W0 k) u)‖ ≤
              Kn0 * ε.val * ‖Li.smoothToSobolev 0 u‖) := by
      exact finite_regularization_paired_norm_bounds
        (κ₀ := Fin J.size) (κ₁ := Fin Npiece)
        (Li.smoothToSobolev 1) (Li.smoothToSobolev 0)
        (Lo.smoothToSobolev 0) (Lo.smoothToSobolev (-1))
        V (∑ k, ∑ j, Tj0 k j) (∑ k, W0 k)
        (fun t : Eps ↦ (Vat₀Family t.val t.property.1 t.property.2).toLinearMap)
        (fun t k j ↦ (QV₀Family t.val t.property.1 t.property.2 k j).toLinearMap)
        (fun t k j v ↦ O0 k j (UVloc₀Family t.val t.property.1 t.property.2 k j (I0 k j v)))
        Rb0 (fun t ↦ RVε₀Family t.val t.property.1 t.property.2)
        K0 Kn0 (fun t : Eps ↦ t.val)
        hWV₀
        (fun v ↦ by
          -- Evaluate the original map-valued base sum in its original coordinates.
          have hfinite : (∑ k, ∑ j, Tj0 k j) v = ∑ k, ∑ j, Tj0 k j v := by
            calc
              (∑ k, ∑ j, Tj0 k j) v = ∑ k, (∑ j, Tj0 k j) v :=
                LinearMap.sum_apply Finset.univ (fun k ↦ ∑ j, Tj0 k j) v
              _ = ∑ k, ∑ j, Tj0 k j v :=
                Finset.sum_congr rfl fun k _ ↦ LinearMap.sum_apply Finset.univ (Tj0 k) v
          exact (hRb0 v).trans (congrArg (Lo.smoothToSobolev 0) hfinite.symm))
        (fun t k j v ↦
          congrArg (fun R : AT.smoothSections →ₗ[ℂ] AT'.smoothSections ↦ R v)
            ((hDataV₀ t.val t.property.1 t.property.2).1 k j))
        (fun t ↦ hVat₀Family t.val t.property.1 t.property.2)
        (fun t v ↦ (hDataV₀ t.val t.property.1 t.property.2).2.2.1 v)
        (fun t ↦ (hDataV₀ t.val t.property.1 t.property.2).2.2.2)
        (fun t v ↦ by
          -- This is the stored negative-order bound for the same selected local family.
          have hb := hnegBound0 t.val t.property.1 t.property.2
            (UVloc₀Family t.val t.property.1 t.property.2)
            (hDataV₀ t.val t.property.1 t.property.2).2.1 v
          -- Evaluate the same residual family once, then transport the stored norm bound.
          have hsum : (∑ k, W0 k) v = ∑ k, W0 k v :=
            LinearMap.sum_apply Finset.univ W0 v
          exact (congrArg
            (fun w : AT'.smoothSections ↦
              ‖Lo.smoothToSobolev (-1)
                (V v - ((∑ k, ∑ j,
                  O0 k j (UVloc₀Family t.val t.property.1 t.property.2 k j (I0 k j v))) +
                    w))‖)
            hsum).le.trans hb)
        ε u
    -- The residual support and fiber formula accompany this same atlas family.
    refine ⟨K0, Kn0,
      (fun ε : Eps ↦ Vat₀Family ε.val ε.property.1 ε.property.2),
      (fun ε : Eps ↦ sV₀Family ε.val ε.property.1 ε.property.2), W0,
      hK0, hKn0, hWs0, hWr0, ?_, ?_, ?_, ?_⟩
    · intro ε
      exact hsVat₀Family ε.val ε.property.1 ε.property.2
    · intro ε z ξ
      exact hsV₀factor ε.val ε.property.1 ε.property.2 z ξ
    · intro ε u
      exact (hPairedV₀ ε u).1
    · intro ε u
      exact (hPairedV₀ ε u).2

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include k k' in
/-- One native vertical regularization retains its actual tensor symbol and both error bounds. -/
theorem exists_associatedSphereTensorVertical_native_approximation
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ j, tsupport (J.cutoff j) ⊆ (S.trivialization (b j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    ∀ (Q : AtlasPseudodifferentialOperator A A' 1)
      (hQ : Q.IsEquivariant IG σ σ' hA hA')
      (Npiece : ℕ) (Lq : Fin Npiece → AtlasPseudodifferentialPiece A A' 1)
      (Rres : L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        L'.toAtlasBundlePresentation.SobolevSpace 0),
      (∀ u, Rres (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
        L'.toAtlasBundlePresentation.smoothToSobolev 0
          ((Q.toLinearMap - ∑ j, (Lq j).toLinearMap) u)) →
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D')
      letI := associatedSphereChartedSpace S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI := isManifold_linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI (x : B) : FiniteDimensional ℂ (E x) :=
        VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT')
        (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
        (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
        (N N' : SmoothFiniteComplexBundle (n := n + r) Z)
        (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
        (kGlobal' : SmoothHermitianMetric (n := n + r) (r := N'.rank) N'.Fiber)
        (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
        letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
        ∀ (e : Iso T N.Fiber)
          (he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
            e.toHom.linearMap)
          (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
            e.symm.toHom.linearMap)
          (e' : Iso T' N'.Fiber)
          (he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
            e'.toHom.linearMap)
          (hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N'.Fiber) AT'
            e'.symm.toHom.linearMap),
          (∀ z (v w : T z), kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
            (l.toCore z).inner v w) →
          (∀ z (v w : T' z), kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
            (l'.toCore z).inner v w) →
          let Si := (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber)
            e he hi).trans (nativeSmoothSectionLinearEquiv N.Fiber)
          let So := (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
            e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
          let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
          ∃ (Cp Cn : ℝ)
            (K : {ε : ℝ // 0 < ε ∧ ε ≤ 1} →
              PseudodifferentialOperator N.Fiber N'.Fiber η 1)
            (p : {ε : ℝ // 0 < ε ∧ ε ≤ 1} → globalSymbolSpace N.Fiber N'.Fiber 1)
            (W : AT.smoothSections →ₗ[ℂ] AT'.smoothSections)
            (WR : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η),
            0 ≤ Cp ∧ 0 ≤ Cn ∧
            (∀ ε, (K ε).principalSymbol =
              globalPrincipalSymbolClass N.Fiber N'.Fiber 1 (p ε)) ∧
            (∀ ε z ξ (u : E (πS z)) (v : D z),
              (p ε).val z ξ (e.linearEquiv z (u ⊗ₜ[ℂ] v)) =
                e'.linearEquiv z (u ⊗ₜ[ℂ]
                  verticalCutoffFactor S E A σ A' σ' hA hA' J b Npiece Lq ε.val z ξ v)) ∧
            (∀ u, WR (kGlobal.smoothToL2 η (Si u)) =
              kGlobal'.smoothToL2 η (So (W u))) ∧
            (∀ ε u, ‖Lo.smoothToSobolev 0
                (So.symm ((K ε).toLinearMap (Si u)) - V u + W u)‖ ≤
              Cp * ε.val * ‖Li.smoothToSobolev 1 u‖) ∧
            (∀ ε u, ‖Lo.smoothToSobolev (-1)
                (So.symm ((K ε).toLinearMap (Si u)) - V u + W u)‖ ≤
              Cn * ε.val * ‖Li.smoothToSobolev 0 u‖) := by
  as_aux_lemma =>
    classical
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    intro A A' hA hA' Q hQ Npiece Lq Rres hRres
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D)
    let : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D')
    let := associatedSphereChartedSpace S
    let := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let (x : B) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
    intro AT AT' Li Lo l hl l' hl' N N' kGlobal kGlobal' η hη
    let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
    intro e he hi e' he' hi' hpair hpair' Si So V
    let Eps := {ε : ℝ // 0 < ε ∧ ε ≤ 1}
    -- Obtain the atlas family, residual and two Sobolev error bounds.
    have hAtlas := exists_associatedSphereTensorVertical_atlas_approximation
      (a := a) S E F F' σ σ' hσ hσ' J b hJ Q hQ Npiece Lq Li Lo
    obtain ⟨Cp, Cn, Pat, pAt, Wj, hAtlasData⟩ := hAtlas
    -- Conjugate the one selected atlas family in the supplied native models.
    have hNative (ε : Eps) :=
      (Pat ε).exists_native_conjugate_principalSymbol (μ := η)
        (pAt ε) (hAtlasData.2.2.2.2.1 ε) N N' e e' he hi he' hi'
    let p (ε : Eps) : globalSymbolSpace N.Fiber N'.Fiber 1 := (hNative ε).choose
    let K (ε : Eps) : PseudodifferentialOperator N.Fiber N'.Fiber η 1 :=
      (hNative ε).choose_spec.choose
    let W : AT.smoothSections →ₗ[ℂ] AT'.smoothSections := ∑ j, Wj j
    have hPa (ε : Eps) (u : AT.smoothSections) :
        So.symm ((K ε).toLinearMap (Si u)) = (Pat ε).toLinearMap u := by
      have hvalue := LinearMap.congr_fun (hNative ε).choose_spec.choose_spec.2.1 (Si u)
      change (K ε).toLinearMap (Si u) =
        So ((Pat ε).toLinearMap (Si.symm (Si u))) at hvalue
      rw [LinearEquiv.symm_apply_apply] at hvalue
      exact (congrArg So.symm hvalue).trans (So.symm_apply_apply _)
    have hpTensor (ε : Eps) (z : Z) (ξ : CotangentFiber (n := n + r) z)
        (u : E (πS z)) (v : D z) :
        (p ε).val z ξ (e.linearEquiv z (u ⊗ₜ[ℂ] v)) =
          e'.linearEquiv z (u ⊗ₜ[ℂ]
            verticalCutoffFactor S E A σ A' σ' hA hA' J b Npiece Lq ε.val z ξ v) := by
      have hvalue := LinearMap.congr_fun
        ((hNative ε).choose_spec.choose_spec.1 z ξ)
        (e.linearEquiv z (u ⊗ₜ[ℂ] v))
      change (p ε).val z ξ (e.linearEquiv z (u ⊗ₜ[ℂ] v)) =
        e'.linearEquiv z ((pAt ε).val z ξ
          ((e.linearEquiv z).symm (e.linearEquiv z (u ⊗ₜ[ℂ] v)))) at hvalue
      rw [LinearEquiv.symm_apply_apply, hAtlasData.2.2.2.2.2.1 ε z ξ,
        TensorProduct.map_tmul, LinearMap.id_apply] at hvalue
      exact hvalue
    -- The atlas stage retained the actual support and fiber formulas needed for this residual.
    have hResidual := exists_associatedSphereTensorVerticalResidual_paired_smoothing
      (a := a) S E F F' σ σ' hσ hσ' k k' ν L L' J b hJ Q
      (fun _ ↦ Npiece) (fun _ ↦ Lq) (fun _ ↦ Rres) (fun _ ↦ hRres)
      Wj hAtlasData.2.2.1 hAtlasData.2.2.2.1 Li Lo l hl l' hl' N N' kGlobal kGlobal' η
      e he hi e' he' hi' hpair hpair'
    let WR : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η := hResidual.choose
    have hWRsum (u : AT.smoothSections) :
        WR (kGlobal.smoothToL2 η (Si u)) = kGlobal'.smoothToL2 η (So (W u)) := by
      exact (hResidual.choose_spec.1 u).trans
        (congrArg (fun w : AT'.smoothSections ↦ kGlobal'.smoothToL2 η (So w))
          (LinearMap.sum_apply Finset.univ Wj u).symm)
    -- Assemble the conclusion from native conjugation and the completed atlas bounds.
    refine ⟨Cp, Cn, K, p, W, WR, hAtlasData.1, hAtlasData.2.1, ?_,
      hpTensor, hWRsum, ?_, ?_⟩
    · intro ε
      exact (hNative ε).choose_spec.choose_spec.2.2.1
    · intro ε u
      have heq := congrArg
        (fun w : AT'.smoothSections ↦ ‖Lo.smoothToSobolev 0 (w - V u + W u)‖)
        (hPa ε u)
      exact heq.le.trans (hAtlasData.2.2.2.2.2.2.1 ε u)
    · intro ε u
      have heq := congrArg
        (fun w : AT'.smoothSections ↦ ‖Lo.smoothToSobolev (-1) (w - V u + W u)‖)
        (hPa ε u)
      exact heq.le.trans (hAtlasData.2.2.2.2.2.2.2 ε u)

end AtiyahSinger

end AuxiliaryVerticalApproximation


section AuxiliaryCutoffGeneric

set_option Elab.async false

namespace AtiyahSinger

open Bundle ComplexBundle Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology

variable {n r d e : ℕ} {ι P B : Type*} [Fintype ι] [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {F F' : OrthogonalSphere r → Type}
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) F]
  [IsSmoothComplexBundle (n := r) (r := d) F]
  [∀ y, NormedAddCommGroup (F' y)] [∀ y, NormedSpace ℂ (F' y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin e)) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin e)) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin e)) F']
  [IsSmoothComplexBundle (n := r) (r := e) F']
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
variable [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

local notation "H" => EuclideanSpace ℝ (Fin (n + r))

variable [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable {a a' : ℕ} [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  (E : B → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable [CompactSpace
  (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "Sphere" => OrthogonalSphere r
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := Sphere)

attribute [local instance] continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent tensorTopology sumTopology
  isFiniteRank_tensor isFiniteRank_sum isFiniteRank_pullback isFiniteRank_associatedEquivariant

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 48000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- One uniform threshold gives ellipticity and the intrinsic index of a supplied cutoff PDO. -/
theorem associated_sphere_cutoff_intrinsic_index_call
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hCell : C.baseOperator.IsElliptic)
    (ℋ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (p : homogeneousGlobalSymbolSpace (n := n) (r := a) (q := a') E E' 1)
    (hpi : IsEllipticGlobalSymbol E E' p.val)
    (gB : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (pfull : globalSymbolSpace (n := n) (r := a) (q := a') E E' 1)
    (Rp : QuantizationPresentation (n := n) (r := a) (q := a') E E')
    (index : Fin C.size → Fin Rp.size)
    (χ ρ : Fin C.size → En → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (horigin : ∀ i, C.piece i = ((Rp.patch (index i)).toPiece pfull).coordinateCutoff
      (χ i) (ρ i) (hχ i) (hρ i))
    (hCsum : ∑ i, (C.piece i).globalSymbol = pfull)
    (hptail : ∀ x ξ, 1 ≤ gB.length x ξ → pfull.val x ξ = p.val x ξ)
    (q : homogeneousGlobalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hqi : IsEllipticGlobalSymbol F F' q.val)
    (hqe : ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ σ' γ q.val x ξ = q.val x ξ)
    (g : SmoothCotangentMetric (n := r) (M := Sphere))
    (k : SmoothHermitianMetric (n := r) (r := d) F)
    (k' : SmoothHermitianMetric (n := r) (r := e) F')
    (hk : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
      ∀ (γ : G) (x : Sphere) (s t : F x),
        k.pairing (γ • x) (σ.linearMap γ x s) (σ.linearMap γ x t) = k.pairing x s t)
    (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
      ∀ (γ : G) (x : Sphere) (s t : F' x),
        k'.pairing (γ • x) (σ'.linearMap γ x s) (σ'.linearMap γ x t) = k'.pairing x s t)
    (hlength : ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x),
      g.length (γ • x) (γ • (⟨x, ξ⟩ : SphereCot)).snd = g.length x ξ)
    (qfull : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hqfixed : ∀ γ : G, equivariantGlobalSymbolLinearMap IG σ σ' γ qfull.val = qfull.val)
    (hqtail : ∀ x ξ, 1 ≤ g.length x ξ → qfull.val x ξ = q.val x ξ)
    (hqfull : IsEllipticFullGlobalSymbol (r := d) (q := e) F F' 1 qfull.val)
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero G SphereCot)
    (hu : homogeneousSymbolKClass 1 p hpi = u)
    (hv : equivariantHomogeneousSymbolKClass IG σ σ' 1 q hqi hqe = v) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin a)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin a')) E'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := d) F
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := e) F'
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
    ∀ (hA : σ.IsSmoothAtlas IG A) (hA' : σ'.IsSmoothAtlas IG A')
      (JH : AtlasBundlePresentation A) (Rq : AtlasQuantizationPresentation A A')
      (b : ι → B) (c : ι → OpenPartialHomeomorph B En) (_hc : ∀ i, c i ∈ atlas En B)
      (θ : ι → En → ℝ) (_hθK : ∀ i, HasCompactSupport (θ i))
      (_hθchart : ∀ i, tsupport (θ i) ⊆ (c i).target)
      (_hθbase : ∀ i, (c i).symm '' tsupport (θ i) ⊆ (S.trivialization (b i)).baseSet),
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := linearModelChartedSpace split.symm Z
      letI := isManifold_linearModelChartedSpace split.symm Z
      letI := (cotangentLinearModelHomeomorph split.symm Z).symm.t2Space
      letI := (cotangentLinearModelHomeomorph split.symm Z).isOpenEmbedding.locallyCompactSpace
      let πS := associatedBundleProjection («F» := Sphere) S.toIsPrincipalBundle
      let Lq := fun j ↦ (Rq.patch j).toPiece (nativeAtlasGlobalSymbol 1 qfull)
      let CP := fun i j ↦ associatedSphereProductChart S (C.center i) (C.piece i).chart (JH.chart j)
      let pfFamily (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
        ∑ i, ∑ j,
          let cov := split (covectorInChart (CP i j) z ξ)
          ((JH.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
            productFrequencyCutoff ε ‖cov.1‖ ‖cov.2‖ : ℝ) : ℂ) •
              ((C.piece i).globalSymbolFunction (πS z)
                (covectorFromChart (C.piece i).chart (πS z) cov.1)).toLinearMap
      let AD := associatedSphereSmoothBundleAtlas S A σ hA
      let AD' := associatedSphereSmoothBundleAtlas S A' σ' hA'
      let CPv := fun i j ↦ associatedSphereProductChart S (b i) (c i) (Lq j).chart
      let qfFamily (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) : D z →ₗ[ℂ] D' z :=
        ∑ i, ∑ j,
          let y := (associatedSphereTrivialization S (b i) z).2
          let cov := split (covectorInChart (CPv i j) z ξ)
          if hz : z ∈ (CPv i j).source ∩
              (AD.chart (b i, (Lq j).input.frameIndex)).baseSet ∩
              (AD'.chart (b i, (Lq j).output.frameIndex)).baseSet then
            let eIn := (AD.frameLinearEquiv (b i, (Lq j).input.frameIndex) z hz.1.2).trans
              (EuclideanSpace.equiv (Fin (A.rank (Lq j).input.frameIndex)) ℂ).symm.toLinearEquiv
            let eOut := (AD'.frameLinearEquiv (b i, (Lq j).output.frameIndex) z hz.2).trans
              (EuclideanSpace.equiv (Fin (A'.rank (Lq j).output.frameIndex)) ℂ).symm.toLinearEquiv
            ((θ i (c i (πS z)) * (Lq j).input.cutoff ((Lq j).chart y) *
              (Lq j).output.cutoff ((Lq j).chart y) *
              productFrequencyCutoff ε ‖cov.2‖ ‖cov.1‖ : ℝ) : ℂ) •
                (eOut.symm.toLinearMap.comp
                  (((Lq j).symbol ((Lq j).chart y) cov.2).toLinearMap.comp eIn.toLinearMap))
          else (0 : D z →ₗ[ℂ] D' z)
      let c₀ (z : Z) := h.toCore (πS z)
      let c₁ (z : Z) := h'.toCore (πS z)
      let d₀ (z : Z) :=
        associatedEquivariantMetricCore S.toIsPrincipalBundle σ k.toContinuousHermitianMetric z
      let d₁ (z : Z) :=
        associatedEquivariantMetricCore S.toIsPrincipalBundle σ' k'.toContinuousHermitianMetric z
      ∀ (_gZ : SmoothCotangentMetric (n := n + r) (M := Z)),
        (∀ z : Z, (∑ i, if z ∈ (associatedSphereTrivialization S (b i)).source ∧
            (associatedSphereTrivialization S (b i) z).1 ∈ (c i).source then
          θ i (c i (associatedSphereTrivialization S (b i) z).1) else 0) = 1) →
      letI : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E)) :=
        pullbackTopology Unit E πS
      letI : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E')) :=
        pullbackTopology Unit E' πS
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D z)) :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D)
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)) :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E') («F» := D')
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)) :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E') («F» := D)
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)) :=
        tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D')
      letI : TopologicalSpace (TotalSpace Unit
          (fun z : Z ↦ (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z))) :=
        sumTopology («E» := fun z : Z ↦ E (πS z) ⊗[ℂ] D z)
          («F» := fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)
      letI : TopologicalSpace (TotalSpace Unit
          (fun z : Z ↦ (E' (πS z) ⊗[ℂ] D z) × (E (πS z) ⊗[ℂ] D' z))) :=
        sumTopology («E» := fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)
          («F» := fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)
      ∃ εBound : ℝ, 0 < εBound ∧ εBound ≤ 1 ∧
        ∀ (Nplus Nminus : SmoothFiniteComplexBundle (n := n + r) Z),
        letI := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
        ∀ (sumSource : Iso
            (fun z : Z ↦ (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z)) Nplus.Fiber)
          (sumTarget : Iso
            (fun z : Z ↦ (E' (πS z) ⊗[ℂ] D z) × (E (πS z) ⊗[ℂ] D' z)) Nminus.Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η]
          (ε : ℝ) (_hεpos : 0 < ε) (_hεsmall : ε ≤ εBound)
          (K : PseudodifferentialOperator (n := n + r)
            (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber η 1),
          (∃ (pi : ∀ z, CotangentFiber (n := n + r) z → E' (πS z) →ₗ[ℂ] E (πS z))
            (qi : ∀ z, CotangentFiber (n := n + r) z → D' z →ₗ[ℂ] D z),
            (∀ z ξ u v, (c₁ z).inner (pfFamily ε z ξ u) v =
              (c₀ z).inner u (pi z ξ v)) ∧
            (∀ z ξ u v, (d₁ z).inner (qfFamily ε z ξ u) v =
              (d₀ z).inner u (qi z ξ v)) ∧
            ∃ qK : globalSymbolSpace (n := n + r)
                (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber 1,
              K.principalSymbol = globalPrincipalSymbolClass Nplus.Fiber Nminus.Fiber 1 qK ∧
              ∀ z ξ (u : E (πS z) ⊗[ℂ] D z) (v : E' (πS z) ⊗[ℂ] D' z),
                qK.val z ξ (sumSource.linearEquiv z (u, v)) =
                  sumTarget.linearEquiv z (reciprocalTensorSymbol
                    (pfFamily ε z ξ) (pi z ξ) (qfFamily ε z ξ) (qi z ξ) (u, v))) →
          K.IsElliptic ∧
            associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
              K.toLinearMap.index := by
  classical
  -- The intrinsic index uses the canonical Borel structure on this same quotient.
  borelize Z
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin a)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin a')) E'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  intro A A' D D'
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
  let (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
  intro hA hA' JH Rq b c hc θ hθK hθchart hθbase split
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  let := (cotangentLinearModelHomeomorph split.symm Z).symm.t2Space
  let := (cotangentLinearModelHomeomorph split.symm Z).isOpenEmbedding.locallyCompactSpace
  intro πS Lq CP pfFamily AD AD' CPv qfFamily c₀ c₁ d₀ d₁ gZ hpartition
  let : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E)) :=
    pullbackTopology Unit E πS
  let : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E')) :=
    pullbackTopology Unit E' πS
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D z)) :=
    tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D)
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)) :=
    tensorTopology («E» := (πS : Z → B) *ᵖ E') («F» := D')
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)) :=
    tensorTopology («E» := (πS : Z → B) *ᵖ E') («F» := D)
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)) :=
    tensorTopology («E» := (πS : Z → B) *ᵖ E) («F» := D')
  let : TopologicalSpace (TotalSpace Unit
      (fun z : Z ↦ (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z))) :=
    sumTopology («E» := fun z : Z ↦ E (πS z) ⊗[ℂ] D z)
      («F» := fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)
  let : TopologicalSpace (TotalSpace Unit
      (fun z : Z ↦ (E' (πS z) ⊗[ℂ] D z) × (E (πS z) ⊗[ℂ] D' z))) :=
    sumTopology («E» := fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)
      («F» := fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)
  -- Exact homogeneous tails follow from the original representatives on the unit-radius tail.
  have hpFullTail (x : B) (ξ : CotangentFiber (n := n) x) (s : ℝ) (hs : 0 < s)
      (hξ : 1 ≤ gB.length x ξ) (hsξ : 1 ≤ gB.length x (s • ξ)) :
      pfull.val x (s • ξ) = (s : ℂ) • pfull.val x ξ := by
    have hne : ξ ≠ 0 := by
      intro hz
      rw [(gB.length_eq_zero_iff x ξ).mpr hz] at hξ
      norm_num at hξ
    calc
      pfull.val x (s • ξ) = p.val x (s • ξ) := hptail x (s • ξ) hsξ
      _ = (s : ℂ) • p.val x ξ := by
        simpa only [Real.rpow_one] using p.property.2 x ξ hne s hs
      _ = (s : ℂ) • pfull.val x ξ :=
        congrArg (fun a ↦ (s : ℂ) • a) (hptail x ξ hξ).symm
  have hqFullTail (y : Sphere) (ξ : CotangentFiber (n := r) y) (s : ℝ) (hs : 0 < s)
      (hξ : 1 ≤ g.length y ξ) (hsξ : 1 ≤ g.length y (s • ξ)) :
      qfull.val y (s • ξ) = (s : ℂ) • qfull.val y ξ := by
    have hne : ξ ≠ 0 := by
      intro hz
      rw [(g.length_eq_zero_iff y ξ).mpr hz] at hξ
      norm_num at hξ
    calc
      qfull.val y (s • ξ) = q.val y (s • ξ) := hqtail y (s • ξ) hsξ
      _ = (s : ℂ) • q.val y ξ := by
        simpa only [Real.rpow_one] using q.property.2 y ξ hne s hs
      _ = (s : ℂ) • qfull.val y ξ :=
        congrArg (fun a ↦ (s : ℂ) • a) (hqtail y ξ hξ).symm
  -- Both thresholds precede the supplied native sums and the supplied cutoff operator.
  have hFactorTail := associated_actual_cutoff_factors_homogeneous_bijective_call
    (n := n) (r := r) (d := d) (e := e) (ι := ι)
    S σ σ' E E' C hCell Rp pfull index χ ρ hχ hρ horigin
    ℋ gB 1 hpFullTail h h' qfull hqfixed hqfull g 1 hqFullTail k k' hk hk'
    hA hA' JH Rq b c hc θ hθK hθchart hθbase gZ hpartition
  have hSymbolData := associated_sphere_cutoff_symbol_index_call
    (n := n) (r := r) (d := d) (e := e) (ι := ι)
    S σ σ' E E' C hCell ℋ p hpi gB h h' pfull hCsum hptail
    q hqi hqe g k k' hk hk' hlength qfull hqfixed hqtail hqfull
    hA hA' JH Rq b c hc θ hθK hθchart hθbase gZ hpartition
  obtain ⟨ε₀, hε₀, hε₀one, hFactorAt⟩ := hFactorTail
  obtain ⟨εPath, hεPath, _hεPathOne, hSymbolAt⟩ := hSymbolData
  refine ⟨min ε₀ εPath, lt_min hε₀ hεPath, (min_le_left ε₀ εPath).trans hε₀one, ?_⟩
  intro Nplus Nminus
  let := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
  intro sumSource sumTarget η hη ε hεpos hεsmall K hFactors
  -- This presentation only evaluates the supplied K; no new PDO or symbol is chosen here.
  obtain ⟨Rfinal⟩ := nonempty_quantizationPresentation
    (n := n + r) (r := Nplus.rank) (q := Nminus.rank)
    («E» := Nplus.Fiber) («F» := Nminus.Fiber)
  have hresult := hSymbolAt Nplus Nminus sumSource sumTarget η Rfinal ε hεpos K
    (by
      -- Normalize only the horizontal finite sum in the original factor-tail certificate.
      obtain ⟨Rtail, hRtail, hpf, hqf, hbij⟩ :=
        hFactorAt ε hεpos (hεsmall.trans (min_le_left ε₀ εPath))
      refine ⟨Rtail, hRtail, ?_, hqf, ?_⟩
      · simpa only [pfFamily, ContinuousLinearMap.toLinearMap_sum,
          ContinuousLinearMap.toLinearMap_smul] using hpf
      · intro z ξ hξ pi qi hpiAdj hqiAdj
        simpa only [pfFamily, ContinuousLinearMap.toLinearMap_sum,
          ContinuousLinearMap.toLinearMap_smul] using
          hbij z ξ hξ pi qi
            (by
              simpa only [pfFamily, ContinuousLinearMap.toLinearMap_sum,
                ContinuousLinearMap.toLinearMap_smul] using hpiAdj)
            hqiAdj)
    hFactors
  refine ⟨hresult.1, ?_⟩
  -- Evaluate the original cotangent model map at this very same supported product.
  change analyticIndexLinearModel split.symm Z (associatedSphereTwistedProduct S u v) = _
  have hmodel := analyticIndexLinearModel_eq_comp split.symm Z η
    (inferInstance : IsSmoothPositiveMeasure (n := n + r) η)
  have hNativeIndex := hresult.2 (hεsmall.trans (min_le_right ε₀ εPath))
  -- Both representatives evaluate to the original classes; no replacement class is selected.
  have hOriginalIndex : analyticIndexOfComponents η
      (compactSupportKZeroPullback
        ⟨(cotangentLinearModelHomeomorph split.symm Z).symm,
          (cotangentLinearModelHomeomorph split.symm Z).symm.continuous⟩
        (cotangentLinearModelHomeomorph split.symm Z).symm.isProperMap
        (associatedSphereTwistedProduct S u v)) = K.toLinearMap.index := by
    simpa only [hu, hv] using hNativeIndex
  exact (DFunLike.congr_fun hmodel (associatedSphereTwistedProduct S u v)).trans hOriginalIndex

end AtiyahSinger

end AuxiliaryCutoffGeneric


section AuxiliaryCutoffBound

set_option Elab.async false
set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology sumTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} {S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection}
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Enr" => EuclideanSpace ℝ (Fin (n + r))
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "πS" => associatedBundleProjection («F» := Y) S.toIsPrincipalBundle

variable
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  {u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := B))}
  {v : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
    (CotangentTotalSpace (n := r) (M := OrthogonalSphere r))}
  (s : AssociatedSpherePositiveSeed S μ u v)

local notation "E" => s.baseSource
local notation "E'" => s.baseTarget
local notation "F" => s.fiberSource
local notation "F'" => s.fiberTarget
local notation "σ" => s.fiberAction
local notation "σ'" => s.fiberTargetAction
local notation "h" => s.baseSourceMetric
local notation "h'" => s.baseTargetMetric
local notation "k" => s.fiberSourceMetric
local notation "k'" => s.fiberTargetMetric
local notation "C" => s.localization
local notation "hσ" => s.fiberAction_smooth
local notation "hσ'" => s.fiberTargetAction_smooth

/-! The local instances retain the original geometric theorem's canonical models. -/

local instance : TopologicalSpace (TotalSpace Unit (E).Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
local instance : TopologicalSpace (TotalSpace Unit (E').Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
local instance : TopologicalSpace (TotalSpace Unit (F).Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
local instance : TopologicalSpace (TotalSpace Unit (F').Fiber) :=
  modelTopology (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
local instance : IsFiniteRank (E).Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
local instance : IsFiniteRank (E').Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
local instance : IsFiniteRank (F).Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
local instance : IsFiniteRank (F').Fiber :=
  isFiniteRank_model (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
local instance (x : B) : FiniteDimensional ℂ ((E).Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber x
local instance (x : B) : FiniteDimensional ℂ ((E').Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber x
local instance (x : Y) : FiniteDimensional ℂ ((F).Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber x
local instance (x : Y) : FiniteDimensional ℂ ((F').Fiber x) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber x

set_option quotPrecheck false in
local notation "A" => nativeSmoothComplexBundleAtlas (n := r) (r := (F).rank) (F).Fiber
set_option quotPrecheck false in
local notation "A'" => nativeSmoothComplexBundleAtlas (n := r) (r := (F').rank) (F').Fiber
set_option quotPrecheck false in
local notation "hA" => (σ).isSmoothAtlas_native IG hσ
set_option quotPrecheck false in
local notation "hA'" => (σ').isSmoothAtlas_native IG hσ'
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
set_option quotPrecheck false in
local notation "T" => fun z : Z ↦ (E).Fiber (πS z) ⊗[ℂ] D z
set_option quotPrecheck false in
local notation "U" => fun z : Z ↦ (E').Fiber (πS z) ⊗[ℂ] D z
set_option quotPrecheck false in
local notation "T'" => fun z : Z ↦ (E).Fiber (πS z) ⊗[ℂ] D' z
set_option quotPrecheck false in
local notation "U'" => fun z : Z ↦ (E').Fiber (πS z) ⊗[ℂ] D' z

local instance : TopologicalSpace (TotalSpace Unit T) :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D)
local instance : TopologicalSpace (TotalSpace Unit U) :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D)
local instance : TopologicalSpace (TotalSpace Unit T') :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D')
local instance : TopologicalSpace (TotalSpace Unit U') :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D')
local instance : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ T z × U' z)) :=
  sumTopology («E» := T) («F» := U')
local instance : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ U z × T' z)) :=
  sumTopology («E» := U) («F» := T')

variable (Rq : AtlasQuantizationPresentation
    (nativeSmoothComplexBundleAtlas (n := r) (r := s.fiberSource.rank) s.fiberSource.Fiber)
    (nativeSmoothComplexBundleAtlas (n := r) (r := s.fiberTarget.rank) s.fiberTarget.Fiber))

local notation "JH" => s.sphereSourcePresentation.toAtlasBundlePresentation
local notation "JV" => s.baseSourcePresentation
local notation "b" => s.basePartitionCenter
local notation "qa" => nativeAtlasGlobalSymbol 1 s.fiberFullSymbol
set_option quotPrecheck false in
local notation "Lq" => fun j ↦ (Rq.patch j).toPiece qa
set_option quotPrecheck false in
local notation "pfFamily" => (C).horizontalCutoffFactor S (E).Fiber A (E').Fiber JH
set_option quotPrecheck false in
local notation "qfFamily" =>
  verticalCutoffFactor S (E).Fiber A σ A' σ' hA hA' JV b Rq.size Lq
set_option quotPrecheck false in
local notation "c₀" => fun z : Z ↦ (h).toCore (πS z)
set_option quotPrecheck false in
local notation "c₁" => fun z : Z ↦ (h').toCore (πS z)
set_option quotPrecheck false in
local notation "d₀" => fun z : Z ↦
  associatedEquivariantMetricCore S.toIsPrincipalBundle σ (k).toContinuousHermitianMetric z
set_option quotPrecheck false in
local notation "d₁" => fun z : Z ↦
  associatedEquivariantMetricCore S.toIsPrincipalBundle σ' (k').toContinuousHermitianMetric z
local notation "Eps" => {ε : ℝ // 0 < ε ∧ ε ≤ 1}


set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
/-- One geometric threshold works for every supplied native cutoff family with this raw symbol. -/
theorem AssociatedSpherePositiveSeed.exists_cutoff_intrinsic_index_bound :
    letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
    letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
    letI : ChartedSpace Enr Z := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (_gZ : SmoothCotangentMetric (n := n + r) (M := Z)),
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (Nplus Nminus : SmoothFiniteComplexBundle (n := n + r) Z),
      letI := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
      ∀ (sumSource : Iso (fun z : Z ↦ T z × U' z) Nplus.Fiber)
        (sumTarget : Iso (fun z : Z ↦ U z × T' z) Nminus.Fiber)
        (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η]
        (KFamily : Eps → PseudodifferentialOperator (n := n + r)
          (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber η 1),
        (∀ ε : Eps,
          ∃ (pi : ∀ z, CotangentFiber (n := n + r) z → (E').Fiber (πS z) →ₗ[ℂ] (E).Fiber (πS z))
            (qi : ∀ z, CotangentFiber (n := n + r) z → D' z →ₗ[ℂ] D z),
            (∀ z ξ u v, (c₁ z).inner (pfFamily ε.val z ξ u) v =
              (c₀ z).inner u (pi z ξ v)) ∧
            (∀ z ξ u v, (d₁ z).inner (qfFamily ε.val z ξ u) v =
              (d₀ z).inner u (qi z ξ v)) ∧
            ∃ qK : globalSymbolSpace (n := n + r)
                (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber 1,
              (KFamily ε).principalSymbol =
                globalPrincipalSymbolClass Nplus.Fiber Nminus.Fiber 1 qK ∧
              ∀ z ξ (u : T z) (v : U' z),
                qK.val z ξ (sumSource.linearEquiv z (u, v)) =
                  sumTarget.linearEquiv z (reciprocalTensorSymbol
                    (pfFamily ε.val z ξ) (pi z ξ) (qfFamily ε.val z ξ) (qi z ξ) (u, v))) →
        ∀ ε : Eps, ε.val ≤ δ →
          (KFamily ε).IsElliptic ∧
            associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
              (KFamily ε).toLinearMap.index := by
  classical
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro gZ
  -- Choose the threshold using only the original representatives and the fixed scalar partitions.
  have hBound := associated_sphere_cutoff_intrinsic_index_call
    (n := n) (r := r) (d := (F).rank) (e := (F').rank) (ι := Fin (JV).size)
    S σ σ' (E).Fiber (E').Fiber C s.localization_elliptic (associatedSphereHorizontalLift S)
    s.baseSymbol s.baseSymbol_elliptic s.baseCotangentMetric h h' s.baseFullSymbol
    s.baseQuantization s.patchIndex s.inputCutoff s.outputCutoff
    s.inputCutoff_smooth s.outputCutoff_smooth s.piece_origin
    s.localization_symbol_sum s.baseSymbol_tail s.fiberSymbol s.fiberSymbol_elliptic
    s.fiberSymbol_equivariant s.fiberCotangentMetric k k'
    s.fiberSourceMetric_invariant s.fiberTargetMetric_invariant s.fiberLength_invariant
    s.fiberFullSymbol s.fiberFullSymbol_invariant s.fiberSymbol_tail
    s.fiberFullSymbol_elliptic u v s.baseClass_eq s.fiberClass_eq
    hA hA' JH Rq b (JV).chart (JV).chart_mem_atlas
    (fun j ↦ ((JV).chartCutoff (E).Fiber j).cutoff)
    (fun j ↦ ((JV).chartCutoff (E).Fiber j).compact_support)
    (fun j _ hx ↦ (((JV).chartCutoff (E).Fiber j).support_subset hx).1)
    (fun j _ hx ↦ s.basePartition_subordinate j ((JV).chartCutoff_support_subset (E).Fiber j hx))
    gZ s.basePartition_sum
  obtain ⟨δ, hδ, hδone, hAt⟩ := hBound
  refine ⟨δ, hδ, hδone, ?_⟩
  -- Every subsequent object is supplied by the caller after this same geometric threshold.
  intro Nplus Nminus
  let := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
  intro sumSource sumTarget η hη KFamily hsymbol ε hε
  exact hAt Nplus Nminus sumSource sumTarget η ε.val ε.property.1 hε
    (KFamily ε) (hsymbol ε)

end AtiyahSinger

end AuxiliaryCutoffBound


section AuxiliaryCoordinateIndexGeneric

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

namespace PseudodifferentialOperator

/-- The smooth index equals the index of the actual realization in the supplied coordinates. -/
theorem index_eq_sobolevCoordinateRealization
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (Φ : A.SobolevSpace 1 ≃L[ℂ] X) (Ψ : B.SobolevSpace 0 ≃L[ℂ] Y)
    (hP : P.IsElliptic) :
    P.toLinearMap.index = (P.sobolevCoordinateRealization A B Φ Ψ).index := by
  let T : X →L[ℂ] Y := P.sobolevCoordinateRealization A B Φ Ψ
  -- Transport the scalar target order while retaining the two supplied coordinates.
  let CoordinateIndexAt (t : ℝ) : Prop :=
    ∀ (ψ : B.SobolevSpace t ≃L[ℂ] Y) (R : X →L[ℂ] Y),
      (∀ u, R (Φ (A.smoothToSobolev 1 u)) =
        ψ (B.smoothToSobolev t (P.toLinearMap u))) →
      R.IsFredholm ∧ R.index = P.toLinearMap.index
  have hcoord : CoordinateIndexAt (1 - 1) :=
    P.isFredholm_and_index_eq_of_sobolev_coordinates A B hP 1 Φ
  have hcoordZero : CoordinateIndexAt 0 :=
    Eq.mp (congrArg CoordinateIndexAt (sub_self (1 : ℝ))) hcoord
  -- The coordinate round trip identifies T with the same operator on smooth sections.
  have hT : T.IsFredholm ∧ T.index = P.toLinearMap.index := by
    apply hcoordZero Ψ T
    intro u
    have hroundtrip := Φ.symm_apply_apply (A.smoothToSobolev 1 u)
    have hcancel := congrArg (fun w : A.SobolevSpace 1 ↦
      Ψ (P.sobolevRealization A B 1 0 (by norm_num) w)) hroundtrip
    exact hcancel.trans (congrArg Ψ
      (P.sobolevRealization_smoothToSobolev A B 1 0 (by norm_num) u))
  exact hT.2.symm

end PseudodifferentialOperator

end AtiyahSinger

end AuxiliaryCoordinateIndexGeneric


section AuxiliaryKernelIndexGeneric

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E₀₀ : M → Type*} [∀ x, AddCommGroup (E₀₀ x)] [∀ x, Module ℂ (E₀₀ x)]
  [TopologicalSpace (TotalSpace Unit E₀₀)]
  {X₀₀ : Type*} [NormedAddCommGroup X₀₀] [InnerProductSpace ℂ X₀₀]
  [CompleteSpace X₀₀]
  {E₁₀ : M → Type*} [∀ x, AddCommGroup (E₁₀ x)] [∀ x, Module ℂ (E₁₀ x)]
  [TopologicalSpace (TotalSpace Unit E₁₀)]
  {X₁₀ : Type*} [NormedAddCommGroup X₁₀] [InnerProductSpace ℂ X₁₀]
  [CompleteSpace X₁₀]
  {E₀₁ : M → Type*} [∀ x, AddCommGroup (E₀₁ x)] [∀ x, Module ℂ (E₀₁ x)]
  [TopologicalSpace (TotalSpace Unit E₀₁)]
  {X₀₁ : Type*} [NormedAddCommGroup X₀₁] [InnerProductSpace ℂ X₀₁]
  [CompleteSpace X₀₁]
  {E₁₁ : M → Type*} [∀ x, AddCommGroup (E₁₁ x)] [∀ x, Module ℂ (E₁₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁₁)]
  {X₁₁ : Type*} [NormedAddCommGroup X₁₁] [InnerProductSpace ℂ X₁₁]
  [CompleteSpace X₁₁]

variable {S₀₀ S₁₀ S₀₁ S₁₁ Nplus Nminus : Type*}
  [AddCommGroup S₀₀] [Module ℂ S₀₀] [AddCommGroup S₁₀] [Module ℂ S₁₀]
  [AddCommGroup S₀₁] [Module ℂ S₀₁] [AddCommGroup S₁₁] [Module ℂ S₁₁]
  [AddCommGroup Nplus] [Module ℂ Nplus] [AddCommGroup Nminus] [Module ℂ Nminus]
  {Dplus Dminus Xplus Xminus : Type*}
  [NormedAddCommGroup Dplus] [NormedSpace ℂ Dplus]
  [NormedAddCommGroup Dminus] [NormedSpace ℂ Dminus]
  [NormedAddCommGroup Xplus] [NormedSpace ℂ Xplus]
  [NormedAddCommGroup Xminus] [NormedSpace ℂ Xminus]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
omit [CompactSpace M] in
/-- Choose an admissible member whose coordinate index equals the specified kernel difference. -/
theorem exists_parameter_index_eq_of_native_corner_approximation
    (A₀₀ : SmoothComplexBundleAtlas (n := n) E₀₀) (L₀₀ : AtlasBundlePresentation A₀₀)
    (i₀₀ : A₀₀.smoothSections →ₗ[ℂ] X₀₀)
    (Φ₀₀ : L₀₀.SobolevSpace 0 ≃L[ℂ] X₀₀)
    (hΦ₀₀ : ∀ u, Φ₀₀ (L₀₀.smoothToSobolev 0 u) = i₀₀ u)
    (A₁₀ : SmoothComplexBundleAtlas (n := n) E₁₀) (L₁₀ : AtlasBundlePresentation A₁₀)
    (i₁₀ : A₁₀.smoothSections →ₗ[ℂ] X₁₀)
    (Φ₁₀ : L₁₀.SobolevSpace 0 ≃L[ℂ] X₁₀)
    (hΦ₁₀ : ∀ u, Φ₁₀ (L₁₀.smoothToSobolev 0 u) = i₁₀ u)
    (A₀₁ : SmoothComplexBundleAtlas (n := n) E₀₁) (L₀₁ : AtlasBundlePresentation A₀₁)
    (i₀₁ : A₀₁.smoothSections →ₗ[ℂ] X₀₁)
    (Φ₀₁ : L₀₁.SobolevSpace 0 ≃L[ℂ] X₀₁)
    (hΦ₀₁ : ∀ u, Φ₀₁ (L₀₁.smoothToSobolev 0 u) = i₀₁ u)
    (A₁₁ : SmoothComplexBundleAtlas (n := n) E₁₁) (L₁₁ : AtlasBundlePresentation A₁₁)
    (i₁₁ : A₁₁.smoothSections →ₗ[ℂ] X₁₁)
    (Φ₁₁ : L₁₁.SobolevSpace 0 ≃L[ℂ] X₁₁)
    (hΦ₁₁ : ∀ u, Φ₁₁ (L₁₁.smoothToSobolev 0 u) = i₁₁ u)
    (H₀ : A₀₀.smoothSections →ₗ[ℂ] A₁₀.smoothSections)
    (H₀s : L₀₀.SobolevSpace 1 →L[ℂ] L₁₀.SobolevSpace 0)
    (hH₀s : ∀ u, H₀s (L₀₀.smoothToSobolev 1 u) = L₁₀.smoothToSobolev 0 (H₀ u))
    (V₀ : A₀₀.smoothSections →ₗ[ℂ] A₀₁.smoothSections)
    (V₀s : L₀₀.SobolevSpace 1 →L[ℂ] L₀₁.SobolevSpace 0)
    (hV₀s : ∀ u, V₀s (L₀₀.smoothToSobolev 1 u) = L₀₁.smoothToSobolev 0 (V₀ u))
    (V₁a : A₁₁.smoothSections →ₗ[ℂ] A₁₀.smoothSections)
    (V₁as : L₁₁.SobolevSpace 1 →L[ℂ] L₁₀.SobolevSpace 0)
    (hV₁as : ∀ u, V₁as (L₁₁.smoothToSobolev 1 u) = L₁₀.smoothToSobolev 0 (V₁a u))
    (H₁a : A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections)
    (H₁as : L₁₁.SobolevSpace 1 →L[ℂ] L₀₁.SobolevSpace 0)
    (hH₁as : ∀ u, H₁as (L₁₁.smoothToSobolev 1 u) = L₀₁.smoothToSobolev 0 (H₁a u))
    (H₀a : A₁₀.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
    (H₀as : L₁₀.SobolevSpace 1 →L[ℂ] L₀₀.SobolevSpace 0)
    (hH₀as : ∀ u, H₀as (L₁₀.smoothToSobolev 1 u) = L₀₀.smoothToSobolev 0 (H₀a u))
    (V₁ : A₁₀.smoothSections →ₗ[ℂ] A₁₁.smoothSections)
    (V₁s : L₁₀.SobolevSpace 1 →L[ℂ] L₁₁.SobolevSpace 0)
    (hV₁s : ∀ u, V₁s (L₁₀.smoothToSobolev 1 u) = L₁₁.smoothToSobolev 0 (V₁ u))
    (V₀a : A₀₁.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
    (V₀as : L₀₁.SobolevSpace 1 →L[ℂ] L₀₀.SobolevSpace 0)
    (hV₀as : ∀ u, V₀as (L₀₁.smoothToSobolev 1 u) = L₀₀.smoothToSobolev 0 (V₀a u))
    (H₁ : A₀₁.smoothSections →ₗ[ℂ] A₁₁.smoothSections)
    (H₁s : L₀₁.SobolevSpace 1 →L[ℂ] L₁₁.SobolevSpace 0)
    (hH₁s : ∀ u, H₁s (L₀₁.smoothToSobolev 1 u) = L₁₁.smoothToSobolev 0 (H₁ u))
    (C₀₀ : ℝ) (hC₀₀ : 0 ≤ C₀₀)
    (hbound₀₀ : ∀ u, ‖L₀₀.smoothToSobolev 1 u‖ ≤
      C₀₀ * (‖i₀₀ u‖ + ‖i₁₀ (H₀ u)‖ + ‖i₀₁ (V₀ u)‖))
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    (hbound₁₁ : ∀ u, ‖L₁₁.smoothToSobolev 1 u‖ ≤
      C₁₁ * (‖i₁₁ u‖ + ‖i₁₀ (V₁a u)‖ + ‖i₀₁ (H₁a u)‖))
    (C₁₀ : ℝ) (hC₁₀ : 0 ≤ C₁₀)
    (hbound₁₀ : ∀ u, ‖L₁₀.smoothToSobolev 1 u‖ ≤
      C₁₀ * (‖i₁₀ u‖ + ‖i₀₀ (H₀a u)‖ + ‖i₁₁ (V₁ u)‖))
    (C₀₁ : ℝ) (hC₀₁ : 0 ≤ C₀₁)
    (hbound₀₁ : ∀ u, ‖L₀₁.smoothToSobolev 1 u‖ ≤
      C₀₁ * (‖i₀₁ u‖ + ‖i₀₀ (V₀a u)‖ + ‖i₁₁ (H₁ u)‖))
    (hcross : ∀ s t, inner ℂ (i₁₀ (H₀ s)) (i₁₀ (V₁a t)) =
      inner ℂ (i₀₁ (V₀ s)) (i₀₁ (H₁a t)))
    (hcrossa : ∀ s t, inner ℂ (i₀₀ (H₀a s)) (i₀₀ (V₀a t)) =
      inner ℂ (i₁₁ (V₁ s)) (i₁₁ (H₁ t)))
    (s₀₀ : A₀₀.smoothSections ≃ₗ[ℂ] S₀₀) (s₁₀ : A₁₀.smoothSections ≃ₗ[ℂ] S₁₀)
    (s₀₁ : A₀₁.smoothSections ≃ₗ[ℂ] S₀₁) (s₁₁ : A₁₁.smoothSections ≃ₗ[ℂ] S₁₁)
    (out₀₀ : S₀₀ →ₗ[ℂ] X₀₀) (out₁₀ : S₁₀ →ₗ[ℂ] X₁₀)
    (out₀₁ : S₀₁ →ₗ[ℂ] X₀₁) (out₁₁ : S₁₁ →ₗ[ℂ] X₁₁)
    (sumPlus : (S₀₀ × S₁₁) →ₗ[ℂ] Nplus) (sumMinus : (S₁₀ × S₀₁) →ₗ[ℂ] Nminus)
    (nativePlusOne : Nplus →ₗ[ℂ] Dplus) (nativeMinusOne : Nminus →ₗ[ℂ] Dminus)
    (nativePlusZero : Nplus →ₗ[ℂ] Xplus) (nativeMinusZero : Nminus →ₗ[ℂ] Xminus)
    (phiPlus : Dplus ≃L[ℂ] WithLp 2 (L₀₀.SobolevSpace 1 × L₁₁.SobolevSpace 1))
    (phiMinus : Dminus ≃L[ℂ] WithLp 2 (L₁₀.SobolevSpace 1 × L₀₁.SobolevSpace 1))
    (psiPlus : Xplus ≃L[ℂ] WithLp 2 (X₀₀ × X₁₁))
    (psiMinus : Xminus ≃L[ℂ] WithLp 2 (X₁₀ × X₀₁))
    (K : ℕ → Nplus →ₗ[ℂ] Nminus) (Ka : ℕ → Nminus →ₗ[ℂ] Nplus)
    (R : ℕ → Dplus →L[ℂ] Xminus) (Ra : ℕ → Dminus →L[ℂ] Xplus)
    (qH₀ : ℕ → S₀₀ →ₗ[ℂ] S₁₀) (qH₀a : ℕ → S₁₀ →ₗ[ℂ] S₀₀)
    (qH₁ : ℕ → S₀₁ →ₗ[ℂ] S₁₁) (qH₁a : ℕ → S₁₁ →ₗ[ℂ] S₀₁)
    (qV₀ : ℕ → S₀₀ →ₗ[ℂ] S₀₁) (qV₀a : ℕ → S₀₁ →ₗ[ℂ] S₀₀)
    (qV₁ : ℕ → S₁₀ →ₗ[ℂ] S₁₁) (qV₁a : ℕ → S₁₁ →ₗ[ℂ] S₁₀)
    (W₀ : X₀₀ →L[ℂ] X₀₁) (W₁ : X₁₀ →L[ℂ] X₁₁)
    (hH₀ : ∃ (U : ℕ → L₀₀.SobolevSpace 1 →L[ℂ] X₁₀)
      (Ua : ℕ → L₁₀.SobolevSpace 1 →L[ℂ] X₀₀),
      (∀ m u, U m (L₀₀.smoothToSobolev 1 u) = out₁₀ (qH₀ m (s₀₀ u))) ∧
      (∀ m v, Ua m (L₁₀.smoothToSobolev 1 v) = out₀₀ (qH₀a m (s₁₀ v))) ∧
      Tendsto (fun m ↦ U m + (0 : X₀₀ →L[ℂ] X₁₀).comp
        (Φ₀₀.toContinuousLinearMap.comp (L₀₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₀.toContinuousLinearMap.comp H₀s)) ∧
      Tendsto (fun m ↦ Ua m + (0 : X₀₀ →L[ℂ] X₁₀).adjoint.comp
        (Φ₁₀.toContinuousLinearMap.comp (L₁₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₀.toContinuousLinearMap.comp H₀as)))
    (hH₁ : ∃ (U : ℕ → L₀₁.SobolevSpace 1 →L[ℂ] X₁₁)
      (Ua : ℕ → L₁₁.SobolevSpace 1 →L[ℂ] X₀₁),
      (∀ m u, U m (L₀₁.smoothToSobolev 1 u) = out₁₁ (qH₁ m (s₀₁ u))) ∧
      (∀ m v, Ua m (L₁₁.smoothToSobolev 1 v) = out₀₁ (qH₁a m (s₁₁ v))) ∧
      Tendsto (fun m ↦ U m + (0 : X₀₁ →L[ℂ] X₁₁).comp
        (Φ₀₁.toContinuousLinearMap.comp (L₀₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₁.toContinuousLinearMap.comp H₁s)) ∧
      Tendsto (fun m ↦ Ua m + (0 : X₀₁ →L[ℂ] X₁₁).adjoint.comp
        (Φ₁₁.toContinuousLinearMap.comp (L₁₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₁.toContinuousLinearMap.comp H₁as)))
    (hV₀ : ∃ (V : ℕ → L₀₀.SobolevSpace 1 →L[ℂ] X₀₁)
      (Va : ℕ → L₀₁.SobolevSpace 1 →L[ℂ] X₀₀),
      (∀ m u, V m (L₀₀.smoothToSobolev 1 u) = out₀₁ (qV₀ m (s₀₀ u))) ∧
      (∀ m v, Va m (L₀₁.smoothToSobolev 1 v) = out₀₀ (qV₀a m (s₀₁ v))) ∧
      Tendsto (fun m ↦ V m + W₀.comp
        (Φ₀₀.toContinuousLinearMap.comp (L₀₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₁.toContinuousLinearMap.comp V₀s)) ∧
      Tendsto (fun m ↦ Va m + W₀.adjoint.comp
        (Φ₀₁.toContinuousLinearMap.comp (L₀₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₀.toContinuousLinearMap.comp V₀as)))
    (hV₁ : ∃ (V : ℕ → L₁₀.SobolevSpace 1 →L[ℂ] X₁₁)
      (Va : ℕ → L₁₁.SobolevSpace 1 →L[ℂ] X₁₀),
      (∀ m u, V m (L₁₀.smoothToSobolev 1 u) = out₁₁ (qV₁ m (s₁₀ u))) ∧
      (∀ m v, Va m (L₁₁.smoothToSobolev 1 v) = out₁₀ (qV₁a m (s₁₁ v))) ∧
      Tendsto (fun m ↦ V m + W₁.comp
        (Φ₁₀.toContinuousLinearMap.comp (L₁₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₁.toContinuousLinearMap.comp V₁s)) ∧
      Tendsto (fun m ↦ Va m + W₁.adjoint.comp
        (Φ₁₁.toContinuousLinearMap.comp (L₁₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₀.toContinuousLinearMap.comp V₁as))) :
    let cXE := WithLp.prodContinuousLinearEquiv 2 ℂ
      (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)
    let cXO := WithLp.prodContinuousLinearEquiv 2 ℂ
      (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ X₀₀ X₁₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ X₁₀ X₀₁
    (∀ u v, phiPlus (nativePlusOne (sumPlus (s₀₀ u, s₁₁ v))) =
      cXE.symm ((L₀₀.smoothToSobolev 1) u, (L₁₁.smoothToSobolev 1) v)) →
    (∀ u v, phiMinus (nativeMinusOne (sumMinus (s₁₀ u, s₀₁ v))) =
      cXO.symm ((L₁₀.smoothToSobolev 1) u, (L₀₁.smoothToSobolev 1) v)) →
    (∀ u v, psiPlus (nativePlusZero (sumPlus (s₀₀ u, s₁₁ v))) =
      cEven.symm (out₀₀ (s₀₀ u), out₁₁ (s₁₁ v))) →
    (∀ u v, psiMinus (nativeMinusZero (sumMinus (s₁₀ u, s₀₁ v))) =
      cOdd.symm (out₁₀ (s₁₀ u), out₀₁ (s₀₁ v))) →
    (∀ m s, R m (nativePlusOne s) = nativeMinusZero (K m s)) →
    (∀ m s, Ra m (nativeMinusOne s) = nativePlusZero (Ka m s)) →
    (∀ m a b, K m (sumPlus (a, b)) =
      sumMinus (qH₀ m a - qV₁a m b, qV₀ m a + qH₁a m b)) →
    (∀ m a b, Ka m (sumMinus (a, b)) =
      sumPlus (qH₀a m a + qV₀a m b, -qV₁ m a + qH₁ m b)) →
    let T := fun m ↦ psiMinus.toContinuousLinearMap.comp
      ((R m).comp phiPlus.symm.toContinuousLinearMap)
    let S := fun m ↦ psiPlus.toContinuousLinearMap.comp
      ((Ra m).comp phiMinus.symm.toContinuousLinearMap)
    let iEven := cEven.symm.toLinearMap.comp (i₀₀.prodMap i₁₁)
    let iOdd := cOdd.symm.toLinearMap.comp (i₁₀.prodMap i₀₁)
    let dSmooth := cOdd.symm.toLinearMap.comp
      (((i₁₀.comp H₀).coprod (-(i₁₀.comp V₁a))).prod
        ((i₀₁.comp V₀).coprod (i₀₁.comp H₁a)))
    let aSmooth := cEven.symm.toLinearMap.comp
      (((i₀₀.comp H₀a).coprod (i₀₀.comp V₀a)).prod
        ((-(i₁₁.comp V₁)).coprod (i₁₁.comp H₁)))
    ∀ (D : WithLp 2 (X₀₀ × X₁₁) →ₗ.[ℂ] WithLp 2 (X₁₀ × X₀₁))
      (Da : WithLp 2 (X₁₀ × X₀₁) →ₗ.[ℂ] WithLp 2 (X₀₀ × X₁₁)),
      D.IsClosed → Da.IsClosed →
      D.graph = (iEven.prod dSmooth).range.topologicalClosure →
      Da.graph = (iOdd.prod aSmooth).range.topologicalClosure →
      D.IsFormalAdjoint Da →
      IsClosed (D.toFun.range : Set (WithLp 2 (X₁₀ × X₀₁))) →
      IsClosed (Da.toFun.range : Set (WithLp 2 (X₀₀ × X₁₁))) →
      FiniteDimensional ℂ D.ker → FiniteDimensional ℂ Da.ker →
      (∀ᶠ m in atTop, (T m).IsFredholm ∧ (S m).IsFredholm) →
      (∀ᶠ m in atTop, (T m).index + (S m).index = 0) →
      ∀ (Admissible : ℕ → Prop), (∀ᶠ m in atTop, Admissible m) →
        ∃ m, Admissible m ∧
          (T m).index = (Module.finrank ℂ D.ker : ℤ) - Module.finrank ℂ Da.ker := by
  intro cXE cXO cEven cOdd hPhiPlus hPhiMinus hPsiPlus hPsiMinus hR hRa hK hKa
    T S iEven iOdd dSmooth aSmooth D Da hD hDa hgraph hgrapha hformal
    hDrange hDarange hDker hDaker hFredholm hindex Admissible hAdmissible
  -- The complete corner theorem compares this same native family with these same kernels.
  have hIndices := eventually_index_eq_of_native_corner_approximation
    A₀₀ L₀₀ i₀₀ Φ₀₀ hΦ₀₀ A₁₀ L₁₀ i₁₀ Φ₁₀ hΦ₁₀
    A₀₁ L₀₁ i₀₁ Φ₀₁ hΦ₀₁ A₁₁ L₁₁ i₁₁ Φ₁₁ hΦ₁₁
    H₀ H₀s hH₀s V₀ V₀s hV₀s V₁a V₁as hV₁as H₁a H₁as hH₁as
    H₀a H₀as hH₀as V₁ V₁s hV₁s V₀a V₀as hV₀as H₁ H₁s hH₁s
    C₀₀ hC₀₀ hbound₀₀ C₁₁ hC₁₁ hbound₁₁
    C₁₀ hC₁₀ hbound₁₀ C₀₁ hC₀₁ hbound₀₁ hcross hcrossa
    s₀₀ s₁₀ s₀₁ s₁₁ out₀₀ out₁₀ out₀₁ out₁₁ sumPlus sumMinus
    nativePlusOne nativeMinusOne nativePlusZero nativeMinusZero
    phiPlus phiMinus psiPlus psiMinus K Ka R Ra
    qH₀ qH₀a qH₁ qH₁a qV₀ qV₀a qV₁ qV₁a W₀ W₁ hH₀ hH₁ hV₀ hV₁
    hPhiPlus hPhiMinus hPsiPlus hPsiMinus hR hRa hK hKa
    D Da hD hDa hgraph hgrapha hformal hDrange hDarange hDker hDaker
    hFredholm hindex
  -- Use one intersection of the original admissibility and approximation events.
  exact (hAdmissible.and hIndices).exists

end AtiyahSinger

end AuxiliaryKernelIndexGeneric


section AuxiliaryCoefficientIndexGeneric

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The extended limit accommodates the common dependent family, regularization and Green witness
-- data.
/-- Specialize a coefficient-action certificate to the original represented base
and sphere classes. -/
theorem finrank_ker_sub_finrank_ker_eq_associatedSphere_coefficientIndex
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero G SphereCot)
    (E E' : SmoothFiniteComplexBundle (n := n) B)
    (p : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := E'.rank)
      E.Fiber E'.Fiber 1)
    (hpi : IsEllipticGlobalSymbol E.Fiber E'.Fiber p.val)
    (hu : homogeneousSymbolKClass 1 p hpi = u)
    (ρ : RepresentationGrothendieckGroup G)
    (hρ : ρ = orthogonalSphereAnalyticIndex r v)
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (L : X →ₗ.[ℂ] Y) (La : Y →ₗ.[ℂ] X)
    (gB : SmoothCotangentMetric (n := n) (M := B))
    (C : PrincipalPseudodifferentialLocalization (a := E.rank) (a' := E'.rank)
      S E.Fiber E'.Fiber μ 1) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
    let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
    let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := E'.rank) E'.Fiber
    let props := nativeAtlasSymbolFunction_homogeneous_properties 1 p.val
      p.property.1 p.property.2 hpi
    C.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
        atlasGlobalPrincipalSymbolClass A₀ A₁ 1
          (atlasRegularizedSymbol A₀ A₁ gB 1 (nativeAtlasSymbolFunction p.val)
            props.1 props.2.1) →
    (∀ (g : SmoothCotangentMetric (n := n) (M := B))
      (pA : AtlasSymbolFunction (n := n) E.Fiber E'.Fiber)
      (hs : IsSmoothOffZeroAtlasSymbol A₀ A₁ pA)
      (hh : IsHomogeneousAtlasSymbol 1 pA) (hi : IsEllipticAtlasSymbol pA),
      C.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
          atlasGlobalPrincipalSymbolClass A₀ A₁ 1
            (atlasRegularizedSymbol A₀ A₁ g 1 pA hs hh) →
      analyticIndexOfComponents μ
          (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
            (associatedRepresentationKZero S.toIsPrincipalBundle ρ)
            (atlasSymbolKClass A₀ A₁ pA hs hi)) =
        (Module.finrank ℂ L.ker : ℤ) - Module.finrank ℂ La.ker) →
    (Module.finrank ℂ L.ker : ℤ) - Module.finrank ℂ La.ker =
      analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex r v)) u) := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  intro A₀ A₁ props hCA hcoefficientAction
  -- The Green formula is applied to this actual homogeneous representative and localization.
  have haction := hcoefficientAction gB (nativeAtlasSymbolFunction p.val)
    props.1 props.2.1 props.2.2 hCA
  -- Native and atlas K classes use the same bundles and symbol; hu identifies the original class.
  have hpClass : atlasSymbolKClass A₀ A₁ (nativeAtlasSymbolFunction p.val)
      props.1 props.2.2 = u :=
    (atlasSymbolKClass_native 1 p.val p.property.1 p.property.2 hpi).trans hu
  -- Normalize both original classes without selecting a new representation or graded operator.
  simpa only [hpClass, hρ] using haction.symm


end AtiyahSinger

end AuxiliaryCoefficientIndexGeneric
