/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereCoordinateWitness

/-!
# Native-corner witnesses for the associated-sphere kernel comparison

Public module ID: M0126.

The common seed, Green pair, native families and sums are fixed inputs.
This module constructs four completions of the Green inclusions, six full
Sobolev realizations, the reverse coordinates, paired operator-norm limits
and four reverse graph-norm bounds. The forward coordinates are supplied
by `AssociatedSphereCoordinateWitness`. Smooth-section identities bind
the completion maps to the prescribed Green inclusions.
-/
@[expose] public noncomputable section

set_option Elab.async false
set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AtiyahSinger

open Bundle ComplexBundle Filter MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate Topology

set_option genInjectivity false in
/-- Implementation data for the specified completions, realizations and analytic certificates.
Geometric carriers and the predicates binding their witnesses enter at specialization. -/
structure AssociatedSphereKernelData
    {Zero₀₀ : Type*}
    {Zero₁₀ : Type*}
    {Zero₀₁ : Type*}
    {Zero₁₁ : Type*}
    {PhiMinus : Type*}
    {PsiPlus : Type*}
    {Vertical₀ : Type*}
    {Vertical₁ : Type*}
    {HorizontalAdjoint₀ : Type*}
    {HorizontalAdjoint₁ : Type*}
    {VerticalAdjoint₀ : Type*}
    {VerticalAdjoint₁ : Type*}
    (ZeroSmooth₀₀ : Zero₀₀ → Prop)
    (ZeroSmooth₁₀ : Zero₁₀ → Prop)
    (ZeroSmooth₀₁ : Zero₀₁ → Prop)
    (ZeroSmooth₁₁ : Zero₁₁ → Prop)
    (PhiMinusSmooth : PhiMinus → Prop)
    (PsiPlusSmooth : PsiPlus → Prop)
    (VerticalSmooth₀ : Vertical₀ → Prop)
    (VerticalSmooth₁ : Vertical₁ → Prop)
    (HorizontalAdjointSmooth₀ : HorizontalAdjoint₀ → Prop)
    (HorizontalAdjointSmooth₁ : HorizontalAdjoint₁ → Prop)
    (VerticalAdjointSmooth₀ : VerticalAdjoint₀ → Prop)
    (VerticalAdjointSmooth₁ : VerticalAdjoint₁ → Prop)
    (HorizontalPaired₀ : Zero₀₀ → Zero₁₀ → Zero₀₁ → Zero₁₁ → HorizontalAdjoint₀ → Prop)
    (HorizontalPaired₁ : Zero₀₀ → Zero₁₀ → Zero₀₁ → Zero₁₁ → HorizontalAdjoint₁ → Prop)
    (VerticalPaired₀ : Zero₀₀ → Zero₁₀ → Zero₀₁ → Zero₁₁ → Vertical₀ → VerticalAdjoint₀ → Prop)
    (VerticalPaired₁ : Zero₀₀ → Zero₁₀ → Zero₀₁ → Zero₁₁ → Vertical₁ → VerticalAdjoint₁ → Prop)
    (ReverseEstimate₀₀ : ℝ → Prop)
    (ReverseEstimate₁₀ : ℝ → Prop)
    (ReverseEstimate₀₁ : ℝ → Prop)
    (ReverseEstimate₁₁ : ℝ → Prop) where
  /-- The completion of the fixed Green corner inclusion. -/
  sobolevZero₀₀ : Zero₀₀
  /-- The completion agrees with the original smooth inclusion. -/
  sobolevZero₀₀_smooth : ZeroSmooth₀₀ sobolevZero₀₀
  /-- The completion of the fixed Green corner inclusion. -/
  sobolevZero₁₀ : Zero₁₀
  /-- The completion agrees with the original smooth inclusion. -/
  sobolevZero₁₀_smooth : ZeroSmooth₁₀ sobolevZero₁₀
  /-- The completion of the fixed Green corner inclusion. -/
  sobolevZero₀₁ : Zero₀₁
  /-- The completion agrees with the original smooth inclusion. -/
  sobolevZero₀₁_smooth : ZeroSmooth₀₁ sobolevZero₀₁
  /-- The completion of the fixed Green corner inclusion. -/
  sobolevZero₁₁ : Zero₁₁
  /-- The completion agrees with the original smooth inclusion. -/
  sobolevZero₁₁_smooth : ZeroSmooth₁₁ sobolevZero₁₁
  /-- Order-one coordinates for the literal adjoint on the fixed negative native sum. -/
  phiMinus : PhiMinus
  /-- Order-zero adjoint target coordinates in the original even L² space. -/
  psiPlus : PsiPlus
  /-- The adjoint domain coordinate preserves the specified smooth sum. -/
  phiMinus_smooth : PhiMinusSmooth phiMinus
  /-- The adjoint target coordinate preserves the original native inclusions. -/
  psiPlus_smooth : PsiPlusSmooth psiPlus
  /-- A bounded realization of the fixed full corner operator. -/
  verticalRealization₀ : Vertical₀
  /-- The realization agrees with the fixed full operator on smooth sections. -/
  verticalRealization₀_smooth : VerticalSmooth₀ verticalRealization₀
  /-- A bounded realization of the fixed full corner operator. -/
  verticalRealization₁ : Vertical₁
  /-- The realization agrees with the fixed full operator on smooth sections. -/
  verticalRealization₁_smooth : VerticalSmooth₁ verticalRealization₁
  /-- A bounded realization of the fixed full corner operator. -/
  horizontalAdjointRealization₀ : HorizontalAdjoint₀
  /-- The realization agrees with the fixed full operator on smooth sections. -/
  horizontalAdjointRealization₀_smooth : HorizontalAdjointSmooth₀ horizontalAdjointRealization₀
  /-- A bounded realization of the fixed full corner operator. -/
  horizontalAdjointRealization₁ : HorizontalAdjoint₁
  /-- The realization agrees with the fixed full operator on smooth sections. -/
  horizontalAdjointRealization₁_smooth : HorizontalAdjointSmooth₁ horizontalAdjointRealization₁
  /-- A bounded realization of the fixed full corner operator. -/
  verticalAdjointRealization₀ : VerticalAdjoint₀
  /-- The realization agrees with the fixed full operator on smooth sections. -/
  verticalAdjointRealization₀_smooth : VerticalAdjointSmooth₀ verticalAdjointRealization₀
  /-- A bounded realization of the fixed full corner operator. -/
  verticalAdjointRealization₁ : VerticalAdjoint₁
  /-- The realization agrees with the fixed full operator on smooth sections. -/
  verticalAdjointRealization₁_smooth : VerticalAdjointSmooth₁ verticalAdjointRealization₁
  /-- The fixed native row and its literal adjoint converge with the same residual. -/
  horizontal₀_paired_limit : HorizontalPaired₀ sobolevZero₀₀ sobolevZero₁₀ sobolevZero₀₁
    sobolevZero₁₁ horizontalAdjointRealization₀
  /-- The fixed native row and its literal adjoint converge with the same residual. -/
  horizontal₁_paired_limit : HorizontalPaired₁ sobolevZero₀₀ sobolevZero₁₀ sobolevZero₀₁
    sobolevZero₁₁ horizontalAdjointRealization₁
  /-- The fixed native row and its literal adjoint converge with the same residual. -/
  vertical₀_paired_limit : VerticalPaired₀ sobolevZero₀₀ sobolevZero₁₀ sobolevZero₀₁ sobolevZero₁₁
    verticalRealization₀ verticalAdjointRealization₀
  /-- The fixed native row and its literal adjoint converge with the same residual. -/
  vertical₁_paired_limit : VerticalPaired₁ sobolevZero₀₀ sobolevZero₁₀ sobolevZero₀₁ sobolevZero₁₁
    verticalRealization₁ verticalAdjointRealization₁
  /-- A reverse estimate constant for the original corner domain. -/
  reverseBound₀₀ : ℝ
  /-- The reverse estimate constant is nonnegative. -/
  reverseBound₀₀_nonneg : 0 ≤ reverseBound₀₀
  /-- The original first-order norm is controlled by the fixed Green corner graph. -/
  reverseBound₀₀_estimate : ReverseEstimate₀₀ reverseBound₀₀
  /-- A reverse estimate constant for the original corner domain. -/
  reverseBound₁₀ : ℝ
  /-- The reverse estimate constant is nonnegative. -/
  reverseBound₁₀_nonneg : 0 ≤ reverseBound₁₀
  /-- The original first-order norm is controlled by the fixed Green corner graph. -/
  reverseBound₁₀_estimate : ReverseEstimate₁₀ reverseBound₁₀
  /-- A reverse estimate constant for the original corner domain. -/
  reverseBound₀₁ : ℝ
  /-- The reverse estimate constant is nonnegative. -/
  reverseBound₀₁_nonneg : 0 ≤ reverseBound₀₁
  /-- The original first-order norm is controlled by the fixed Green corner graph. -/
  reverseBound₀₁_estimate : ReverseEstimate₀₁ reverseBound₀₁
  /-- A reverse estimate constant for the original corner domain. -/
  reverseBound₁₁ : ℝ
  /-- The reverse estimate constant is nonnegative. -/
  reverseBound₁₁_nonneg : 0 ≤ reverseBound₁₁
  /-- The original first-order norm is controlled by the fixed Green corner graph. -/
  reverseBound₁₁_estimate : ReverseEstimate₁₁ reverseBound₁₁

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology sumTopology continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent lieGroup_orthogonalGroup
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
local notation "ν" => s.fiberMeasure
local notation "C" => s.localization
local notation "Q" => s.fiberOperator
local notation "hσ" => s.fiberAction_smooth
local notation "hσ'" => s.fiberTargetAction_smooth
local notation "hQ" => s.fiberOperator_equivariant
local notation "hQell" => s.fiberOperator_elliptic

/-! ## Canonical models for the native corner data -/


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

variable (g : AssociatedSphereGreenSelection s)

local notation "L₀" => s.sphereSourcePresentation
local notation "L₁" => s.sphereTargetPresentation
set_option quotPrecheck false in
local notation "JH" => (L₀).toAtlasBundlePresentation
set_option quotPrecheck false in
local notation "JH'" => (L₁).toAtlasBundlePresentation
local notation "JV" => s.baseSourcePresentation
local notation "JV'" => s.baseTargetPresentation
local notation "b" => s.basePartitionCenter
local notation "hJV" => s.basePartition_subordinate
local notation "hQA" => g.fiberAtlasOperator_equivariant
local notation "qa" => nativeAtlasGlobalSymbol 1 s.fiberFullSymbol
local notation "Eps" => {ε : ℝ // 0 < ε ∧ ε ≤ 1}
set_option quotPrecheck false in
local notation "pfFamily" => (C).horizontalCutoffFactor S (E).Fiber A (E').Fiber JH

local notation "N₀₀" => g.native₀₀
local notation "k₀₀" => g.nativeMetric₀₀
local notation "l₀₀" => g.atlasMetric₀₀
local notation "e₀₀" => g.nativeIso₀₀
local notation "he₀₀" => g.nativeIso₀₀_smooth
local notation "hi₀₀" => g.nativeIso₀₀_symm_smooth
local notation "hk₀₀" => g.nativeIso₀₀_isometry
local notation "hl₀₀" => g.atlasMetric₀₀_smooth
set_option quotPrecheck false in
local notation "S₀₀" => (atlasSmoothSectionEquiv A₀₀
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₀₀).rank) (N₀₀).Fiber)
  e₀₀ he₀₀ hi₀₀).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₀₀).rank) (N₀₀).Fiber)

local notation "N₁₀" => g.native₁₀
local notation "k₁₀" => g.nativeMetric₁₀
local notation "l₁₀" => g.atlasMetric₁₀
local notation "e₁₀" => g.nativeIso₁₀
local notation "he₁₀" => g.nativeIso₁₀_smooth
local notation "hi₁₀" => g.nativeIso₁₀_symm_smooth
local notation "hk₁₀" => g.nativeIso₁₀_isometry
local notation "hl₁₀" => g.atlasMetric₁₀_smooth
set_option quotPrecheck false in
local notation "S₁₀" => (atlasSmoothSectionEquiv A₁₀
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₁₀).rank) (N₁₀).Fiber)
  e₁₀ he₁₀ hi₁₀).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₁₀).rank) (N₁₀).Fiber)

local notation "N₀₁" => g.native₀₁
local notation "k₀₁" => g.nativeMetric₀₁
local notation "l₀₁" => g.atlasMetric₀₁
local notation "e₀₁" => g.nativeIso₀₁
local notation "he₀₁" => g.nativeIso₀₁_smooth
local notation "hi₀₁" => g.nativeIso₀₁_symm_smooth
local notation "hk₀₁" => g.nativeIso₀₁_isometry
local notation "hl₀₁" => g.atlasMetric₀₁_smooth
set_option quotPrecheck false in
local notation "S₀₁" => (atlasSmoothSectionEquiv A₀₁
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₀₁).rank) (N₀₁).Fiber)
  e₀₁ he₀₁ hi₀₁).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₀₁).rank) (N₀₁).Fiber)

local notation "N₁₁" => g.native₁₁
local notation "k₁₁" => g.nativeMetric₁₁
local notation "l₁₁" => g.atlasMetric₁₁
local notation "e₁₁" => g.nativeIso₁₁
local notation "he₁₁" => g.nativeIso₁₁_smooth
local notation "hi₁₁" => g.nativeIso₁₁_symm_smooth
local notation "hk₁₁" => g.nativeIso₁₁_isometry
local notation "hl₁₁" => g.atlasMetric₁₁_smooth
set_option quotPrecheck false in
local notation "S₁₁" => (atlasSmoothSectionEquiv A₁₁
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₁₁).rank) (N₁₁).Fiber)
  e₁₁ he₁₁ hi₁₁).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₁₁).rank) (N₁₁).Fiber)

local notation "Li" => g.presentation₀₀
local notation "Lo" => g.presentation₁₀
local notation "Li₁" => g.presentation₀₁
local notation "Lo₁" => g.presentation₁₁
set_option quotPrecheck false in
local notation "V₀" => associatedSphereTensorVerticalOperator (a := (E).rank)
  S (E).Fiber A σ hA A' σ' hA' QA hQA
set_option quotPrecheck false in
local notation "V₁" => associatedSphereTensorVerticalOperator (a := (E').rank)
  S (E').Fiber A σ hA A' σ' hA' QA hQA

variable (sums : AssociatedSphereNativeSums s g)

local notation "qfull" => s.fiberFullSymbol
local notation "hqfixed" => s.fiberFullSymbol_invariant
local notation "hqfull" => s.fiberFullSymbol_elliptic
local notation "hQpr" => s.fiberOperator_principal
local notation "hk" => s.fiberSourceMetric_invariant
local notation "hk'" => s.fiberTargetMetric_invariant
local notation "hνinv" => s.fiberMeasure_invariant
local notation "hCell" => s.localization_elliptic
local notation "hJA" => g.fiberAtlasAdjoint_equivariant
local notation "hJV'" => s.basePartition_subordinate
local notation "split" => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
local notation "L" => g.graded
local notation "La" => g.gradedAdjoint
local notation "Even" => g.Even
local notation "Odd" => g.Odd
local notation "β₀" => g.baseAdjointCutoff₀
local notation "hβ₀" => g.baseAdjointCutoff₀_smooth
local notation "hsβ₀" => g.baseAdjointCutoff₀_support
local notation "hβ₀one" => g.baseAdjointCutoff₀_one
local notation "H₀'" => g.horizontalPieceAdjoint₀
local notation "hH₀formula" => g.horizontalPieceAdjoint₀_formula
local notation "H₀a" => g.horizontalAdjoint₀
local notation "hH₀sum" => g.horizontalAdjoint₀_sum
local notation "hH₀" => g.horizontal₀_adjoint
local notation "hV₀" => g.vertical₀_adjoint
local notation "V₀a" => g.verticalAdjoint₀
local notation "β₁" => g.baseAdjointCutoff₁
local notation "hβ₁" => g.baseAdjointCutoff₁_smooth
local notation "hsβ₁" => g.baseAdjointCutoff₁_support
local notation "hβ₁one" => g.baseAdjointCutoff₁_one
local notation "H₁'" => g.horizontalPieceAdjoint₁
local notation "hH₁formula" => g.horizontalPieceAdjoint₁_formula
local notation "H₁a" => g.horizontalAdjoint₁
local notation "hH₁sum" => g.horizontalAdjoint₁_sum
local notation "hH₁" => g.horizontal₁_adjoint
local notation "hV₁" => g.vertical₁_adjoint
local notation "V₁a" => g.verticalAdjoint₁
local notation "i₀₀" => g.inclusion₀₀
local notation "hkPure₀₀" => g.nativeIso₀₀_pairing_tmul
local notation "i₁₀" => g.inclusion₁₀
local notation "hkPure₁₀" => g.nativeIso₁₀_pairing_tmul
local notation "i₀₁" => g.inclusion₀₁
local notation "hkPure₀₁" => g.nativeIso₀₁_pairing_tmul
local notation "i₁₁" => g.inclusion₁₁
local notation "hkPure₁₁" => g.nativeIso₁₁_pairing_tmul
/- The selected data are shared with the cutoff and equality files. -/
set_option quotPrecheck false in
local notation "Rq" => associatedSphereFiberQuantization s
set_option quotPrecheck false in
local notation "nativeU₀" => associatedSphereHorizontalFamily₀ s g
set_option quotPrecheck false in
local notation "nativeU₁" => associatedSphereHorizontalFamily₁ s g
set_option quotPrecheck false in
local notation "RH₀" => associatedSphereHorizontalRealization₀ s g
set_option quotPrecheck false in
local notation "RH₁" => associatedSphereHorizontalRealization₁ s g
set_option quotPrecheck false in
local notation "nativeV₀" => associatedSphereVerticalFamily₀ s g
set_option quotPrecheck false in
local notation "nativeV₁" => associatedSphereVerticalFamily₁ s g
set_option quotPrecheck false in
local notation "WR₀" => associatedSphereVerticalResidualRealization₀ s g
set_option quotPrecheck false in
local notation "WR₁" => associatedSphereVerticalResidualRealization₁ s g
local notation "Nplus" => sums.nativePlus
local notation "Nminus" => sums.nativeMinus
local notation "ePlus" => sums.sumPlus
local notation "eMinus" => sums.sumMinus
local notation "hPlus₀" => sums.plus₀_smooth
local notation "hPlus₁" => sums.plus₁_smooth
local notation "hMinus₀" => sums.minus₀_smooth
local notation "hMinus₁" => sums.minus₁_smooth
local notation "kPlus" => sums.metricPlus
local notation "kMinus" => sums.metricMinus
local notation "Dplus" => sums.presentationPlus
local notation "Dminus" => sums.presentationMinus
local notation "DD" => sums.cornerPresentationsPlus
local notation "HH" => sums.cornerPresentationsMinus
local notation "KFamily" => sums.cutoffFamily
local notation "hKmodel" => sums.cutoff_blocks
local notation "hKadjmodel" => sums.adjoint_cutoff_blocks
set_option quotPrecheck false in
local notation "Φplus" => smoothSectionSumEquiv (ePlus).linearEquiv hPlus₀ hPlus₁
set_option quotPrecheck false in
local notation "Φminus" => smoothSectionSumEquiv (eMinus).linearEquiv hMinus₀ hMinus₁

set_option quotPrecheck false in
local notation "X₀₀" => (k₀₀).L2SectionSpace η
set_option quotPrecheck false in
local notation "X₁₀" => (k₁₀).L2SectionSpace η
set_option quotPrecheck false in
local notation "X₀₁" => (k₀₁).L2SectionSpace η
set_option quotPrecheck false in
local notation "X₁₁" => (k₁₁).L2SectionSpace η
local notation "epsSeq" => associatedSphereCutoffSequence

section KernelWitnessTypes

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

local instance : TopologicalSpace (TotalSpace Unit T) :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D)

local instance : TopologicalSpace (TotalSpace Unit U) :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D)

local instance : TopologicalSpace (TotalSpace Unit T') :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D')

local instance : TopologicalSpace (TotalSpace Unit U') :=
  tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D')

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₀₀).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₀₀).rank)) (N₀₀).Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₁₀).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₁₀).rank)) (N₁₀).Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₀₁).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₀₁).rank)) (N₀₁).Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₁₁).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₁₁).rank)) (N₁₁).Fiber]

local instance (z : Z) : FiniteDimensional ℂ ((E).Fiber (πS z)) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber (πS z)

local instance (z : Z) : FiniteDimensional ℂ ((E').Fiber (πS z)) :=
  VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber (πS z)

local instance : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ

local instance : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'

local instance (z : Z) : FiniteDimensional ℂ (D z) := finite_fiber («E» := D) z

local instance (z : Z) : FiniteDimensional ℂ (D' z) := finite_fiber («E» := D') z

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (Nplus).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (Nplus).rank)) (Nplus).Fiber]

local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (Nminus).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (Nminus).rank)) (Nminus).Fiber]

set_option maxHeartbeats 8000000 in
-- Specialize the analytic predicates at the same Green inclusions and native families.
/-- Raw analytic certificates needed by the native-corner index theorem.
The forward coordinates, Green pair, selected native families and sums stay fixed. -/
abbrev AssociatedSphereKernelWitness : Type _ :=
  sphereContext%[AssociatedSphereKernelData
    (Zero₀₀ := (Li).SobolevSpace 0 ≃L[ℂ] X₀₀)
    (Zero₁₀ := (Lo).SobolevSpace 0 ≃L[ℂ] X₁₀)
    (Zero₀₁ := (Li₁).SobolevSpace 0 ≃L[ℂ] X₀₁)
    (Zero₁₁ := (Lo₁).SobolevSpace 0 ≃L[ℂ] X₁₁)
    (PhiMinus := (Dminus).SobolevSpace 1 ≃L[ℂ]
      WithLp 2 ((Lo).SobolevSpace 1 × (Li₁).SobolevSpace 1))
    (PsiPlus := (Dplus).SobolevSpace 0 ≃L[ℂ] Even)
    (Vertical₀ := (Li).SobolevSpace 1 →L[ℂ] (Li₁).SobolevSpace 0)
    (Vertical₁ := (Lo).SobolevSpace 1 →L[ℂ] (Lo₁).SobolevSpace 0)
    (HorizontalAdjoint₀ := (Lo).SobolevSpace 1 →L[ℂ] (Li).SobolevSpace 0)
    (HorizontalAdjoint₁ := (Lo₁).SobolevSpace 1 →L[ℂ] (Li₁).SobolevSpace 0)
    (VerticalAdjoint₀ := (Li₁).SobolevSpace 1 →L[ℂ] (Li).SobolevSpace 0)
    (VerticalAdjoint₁ := (Lo₁).SobolevSpace 1 →L[ℂ] (Lo).SobolevSpace 0)
    (ZeroSmooth₀₀ := fun sobolevZero₀₀ ↦
      ∀ a : (A₀₀).smoothSections,
      sobolevZero₀₀ ((Li).smoothToSobolev 0 a) = i₀₀ a)
    (ZeroSmooth₁₀ := fun sobolevZero₁₀ ↦
      ∀ a : (A₁₀).smoothSections,
      sobolevZero₁₀ ((Lo).smoothToSobolev 0 a) = i₁₀ a)
    (ZeroSmooth₀₁ := fun sobolevZero₀₁ ↦
      ∀ a : (A₀₁).smoothSections,
      sobolevZero₀₁ ((Li₁).smoothToSobolev 0 a) = i₀₁ a)
    (ZeroSmooth₁₁ := fun sobolevZero₁₁ ↦
      ∀ a : (A₁₁).smoothSections,
      sobolevZero₁₁ ((Lo₁).smoothToSobolev 0 a) = i₁₁ a)
    (PhiMinusSmooth := fun phiMinus ↦
      ∀ (a : (A₁₀).smoothSections) (w : (A₀₁).smoothSections),
      phiMinus ((Dminus).smoothToSobolev 1 (Φminus (S₁₀ a, S₀₁ w))) =
        WithLp.toLp 2 ((Lo).smoothToSobolev 1 a, (Li₁).smoothToSobolev 1 w))
    (PsiPlusSmooth := fun psiPlus ↦
      ∀ (a : (A₀₀).smoothSections) (w : (A₁₁).smoothSections),
      psiPlus ((Dplus).smoothToSobolev 0 (Φplus (S₀₀ a, S₁₁ w))) =
        WithLp.toLp 2 (i₀₀ a, i₁₁ w))
    (VerticalSmooth₀ := fun verticalRealization₀ ↦
      ∀ a : (A₀₀).smoothSections,
      verticalRealization₀ ((Li).smoothToSobolev 1 a) = (Li₁).smoothToSobolev 0 (V₀ a))
    (VerticalSmooth₁ := fun verticalRealization₁ ↦
      ∀ a : (A₁₀).smoothSections,
      verticalRealization₁ ((Lo).smoothToSobolev 1 a) = (Lo₁).smoothToSobolev 0 (V₁ a))
    (HorizontalAdjointSmooth₀ := fun horizontalAdjointRealization₀ ↦
      ∀ a : (A₁₀).smoothSections,
      horizontalAdjointRealization₀ ((Lo).smoothToSobolev 1 a) = (Li).smoothToSobolev 0 (H₀a a))
    (HorizontalAdjointSmooth₁ := fun horizontalAdjointRealization₁ ↦
      ∀ a : (A₁₁).smoothSections,
      horizontalAdjointRealization₁ ((Lo₁).smoothToSobolev 1 a) = (Li₁).smoothToSobolev 0 (H₁a a))
    (VerticalAdjointSmooth₀ := fun verticalAdjointRealization₀ ↦
      ∀ a : (A₀₁).smoothSections,
      verticalAdjointRealization₀ ((Li₁).smoothToSobolev 1 a) = (Li).smoothToSobolev 0 (V₀a a))
    (VerticalAdjointSmooth₁ := fun verticalAdjointRealization₁ ↦
      ∀ a : (A₁₁).smoothSections,
      verticalAdjointRealization₁ ((Lo₁).smoothToSobolev 1 a) = (Lo).smoothToSobolev 0 (V₁a a))
    (HorizontalPaired₀ := fun sobolevZero₀₀ sobolevZero₁₀ _sobolevZero₀₁ _sobolevZero₁₁
        horizontalAdjointRealization₀ ↦
      ∃ (R : ℕ → (Li).SobolevSpace 1 →L[ℂ] X₁₀)
        (Ra : ℕ → (Lo).SobolevSpace 1 →L[ℂ] X₀₀),
      (∀ m a, R m ((Li).smoothToSobolev 1 a) =
        (k₁₀).smoothToL2 η ((nativeU₀ (epsSeq m)).toLinearMap (S₀₀ a))) ∧
      (∀ m a, Ra m ((Lo).smoothToSobolev 1 a) =
        (k₀₀).smoothToL2 η
          (((nativeU₀ (epsSeq m)).metricFormalAdjoint k₀₀ k₁₀).toLinearMap (S₁₀ a))) ∧
      Tendsto (fun m ↦ R m + (0 : X₀₀ →L[ℂ] X₁₀).comp
        (sobolevZero₀₀.toContinuousLinearMap.comp
          ((Li).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₁₀.toContinuousLinearMap.comp RH₀)) ∧
      Tendsto (fun m ↦ Ra m + (0 : X₀₀ →L[ℂ] X₁₀).adjoint.comp
        (sobolevZero₁₀.toContinuousLinearMap.comp
          ((Lo).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₀₀.toContinuousLinearMap.comp horizontalAdjointRealization₀)))
    (HorizontalPaired₁ := fun _sobolevZero₀₀ _sobolevZero₁₀ sobolevZero₀₁ sobolevZero₁₁
        horizontalAdjointRealization₁ ↦
      ∃ (R : ℕ → (Li₁).SobolevSpace 1 →L[ℂ] X₁₁)
        (Ra : ℕ → (Lo₁).SobolevSpace 1 →L[ℂ] X₀₁),
      (∀ m a, R m ((Li₁).smoothToSobolev 1 a) =
        (k₁₁).smoothToL2 η ((nativeU₁ (epsSeq m)).toLinearMap (S₀₁ a))) ∧
      (∀ m a, Ra m ((Lo₁).smoothToSobolev 1 a) =
        (k₀₁).smoothToL2 η
          (((nativeU₁ (epsSeq m)).metricFormalAdjoint k₀₁ k₁₁).toLinearMap (S₁₁ a))) ∧
      Tendsto (fun m ↦ R m + (0 : X₀₁ →L[ℂ] X₁₁).comp
        (sobolevZero₀₁.toContinuousLinearMap.comp
          ((Li₁).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₁₁.toContinuousLinearMap.comp RH₁)) ∧
      Tendsto (fun m ↦ Ra m + (0 : X₀₁ →L[ℂ] X₁₁).adjoint.comp
        (sobolevZero₁₁.toContinuousLinearMap.comp
          ((Lo₁).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₀₁.toContinuousLinearMap.comp horizontalAdjointRealization₁)))
    (VerticalPaired₀ := fun sobolevZero₀₀ _sobolevZero₁₀ sobolevZero₀₁ _sobolevZero₁₁
        verticalRealization₀ verticalAdjointRealization₀ ↦
      ∃ (R : ℕ → (Li).SobolevSpace 1 →L[ℂ] X₀₁)
        (Ra : ℕ → (Li₁).SobolevSpace 1 →L[ℂ] X₀₀),
      (∀ m a, R m ((Li).smoothToSobolev 1 a) =
        (k₀₁).smoothToL2 η ((nativeV₀ (epsSeq m)).toLinearMap (S₀₀ a))) ∧
      (∀ m a, Ra m ((Li₁).smoothToSobolev 1 a) =
        (k₀₀).smoothToL2 η
          (((nativeV₀ (epsSeq m)).metricFormalAdjoint k₀₀ k₀₁).toLinearMap (S₀₁ a))) ∧
      Tendsto (fun m ↦ R m + (WR₀).comp
        (sobolevZero₀₀.toContinuousLinearMap.comp
          ((Li).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₀₁.toContinuousLinearMap.comp verticalRealization₀)) ∧
      Tendsto (fun m ↦ Ra m + (WR₀).adjoint.comp
        (sobolevZero₀₁.toContinuousLinearMap.comp
          ((Li₁).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₀₀.toContinuousLinearMap.comp verticalAdjointRealization₀)))
    (VerticalPaired₁ := fun _sobolevZero₀₀ sobolevZero₁₀ _sobolevZero₀₁ sobolevZero₁₁
        verticalRealization₁ verticalAdjointRealization₁ ↦
      ∃ (R : ℕ → (Lo).SobolevSpace 1 →L[ℂ] X₁₁)
        (Ra : ℕ → (Lo₁).SobolevSpace 1 →L[ℂ] X₁₀),
      (∀ m a, R m ((Lo).smoothToSobolev 1 a) =
        (k₁₁).smoothToL2 η ((nativeV₁ (epsSeq m)).toLinearMap (S₁₀ a))) ∧
      (∀ m a, Ra m ((Lo₁).smoothToSobolev 1 a) =
        (k₁₀).smoothToL2 η
          (((nativeV₁ (epsSeq m)).metricFormalAdjoint k₁₀ k₁₁).toLinearMap (S₁₁ a))) ∧
      Tendsto (fun m ↦ R m + (WR₁).comp
        (sobolevZero₁₀.toContinuousLinearMap.comp
          ((Lo).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₁₁.toContinuousLinearMap.comp verticalRealization₁)) ∧
      Tendsto (fun m ↦ Ra m + (WR₁).adjoint.comp
        (sobolevZero₁₁.toContinuousLinearMap.comp
          ((Lo₁).sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (sobolevZero₁₀.toContinuousLinearMap.comp verticalAdjointRealization₁)))
    (ReverseEstimate₀₀ := fun reverseBound₀₀ ↦
      ∀ a : (A₀₀).smoothSections,
      ‖(Li).smoothToSobolev 1 a‖ ≤
        reverseBound₀₀ * (‖i₀₀ a‖ + ‖i₁₀ (H₀ a)‖ + ‖i₀₁ (V₀ a)‖))
    (ReverseEstimate₁₀ := fun reverseBound₁₀ ↦
      ∀ a : (A₁₀).smoothSections,
      ‖(Lo).smoothToSobolev 1 a‖ ≤
        reverseBound₁₀ * (‖i₁₀ a‖ + ‖i₀₀ (H₀a a)‖ + ‖i₁₁ (V₁ a)‖))
    (ReverseEstimate₀₁ := fun reverseBound₀₁ ↦
      ∀ a : (A₀₁).smoothSections,
      ‖(Li₁).smoothToSobolev 1 a‖ ≤
        reverseBound₀₁ * (‖i₀₁ a‖ + ‖i₁₁ (H₁ a)‖ + ‖i₀₀ (V₀a a)‖))
    (ReverseEstimate₁₁ := fun reverseBound₁₁ ↦
      ∀ a : (A₁₁).smoothSections,
      ‖(Lo₁).smoothToSobolev 1 a‖ ≤
        reverseBound₁₁ * (‖i₁₁ a‖ + ‖i₀₁ (H₁a a)‖ + ‖i₁₀ (V₁a a)‖))]

end KernelWitnessTypes

set_option maxHeartbeats 80000000 in
-- The extended limit accommodates the paired limits and reverse bounds over the fixed Green
-- context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the paired limits and reverse bounds over the fixed Green
-- context.
/-- Construct completions, paired limits and reverse bounds for the fixed Green data
and native sums. -/
theorem nonempty_associatedSphereKernelWitness :
    Nonempty (AssociatedSphereKernelWitness s g sums) := by
  classical
  let : IsSmoothPositiveMeasure (n := r) ν := s.fiberMeasure_smooth
  let : IsFiniteMeasure ν := isFiniteMeasure_of_smoothPositiveMeasure (n := r) ν
  let : TopologicalSpace (TotalSpace Unit (E).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
  let : TopologicalSpace (TotalSpace Unit (E').Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
  let : TopologicalSpace (TotalSpace Unit (F).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
  let : TopologicalSpace (TotalSpace Unit (F').Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
  let : IsFiniteRank (E).Fiber :=
    isFiniteRank_model (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
  let : IsFiniteRank (E').Fiber :=
    isFiniteRank_model (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
  let : IsFiniteRank (F).Fiber :=
    isFiniteRank_model (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
  let : IsFiniteRank (F').Fiber :=
    isFiniteRank_model (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
  let : ∀ x : B, FiniteDimensional ℂ ((E).Fiber x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber x
  let : ∀ x : B, FiniteDimensional ℂ ((E').Fiber x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber x
  let : ∀ x : Y, FiniteDimensional ℂ ((F).Fiber x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber x
  let : ∀ x : Y, FiniteDimensional ℂ ((F').Fiber x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber x
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D)
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D')
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D')
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
  let : TopologicalSpace (TotalSpace Unit (N₀₀).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (N₀₀).rank)) (N₀₀).Fiber
  let : TopologicalSpace (TotalSpace Unit (N₁₀).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (N₁₀).rank)) (N₁₀).Fiber
  let : TopologicalSpace (TotalSpace Unit (N₀₁).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (N₀₁).rank)) (N₀₁).Fiber
  let : TopologicalSpace (TotalSpace Unit (N₁₁).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (N₁₁).rank)) (N₁₁).Fiber
  let : ∀ z : Z, FiniteDimensional ℂ ((E).Fiber (πS z)) :=
    fun z ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber (πS z)
  let : ∀ z : Z, FiniteDimensional ℂ ((E').Fiber (πS z)) :=
    fun z ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber (πS z)
  let : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ
  let : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'
  let : ∀ z : Z, FiniteDimensional ℂ (D z) :=
    fun z ↦ finite_fiber («E» := D) z
  let : ∀ z : Z, FiniteDimensional ℂ (D' z) :=
    fun z ↦ finite_fiber («E» := D') z
  let : TopologicalSpace (TotalSpace Unit (Nplus).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (Nplus).rank)) (Nplus).Fiber
  let : TopologicalSpace (TotalSpace Unit (Nminus).Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin (Nminus).rank)) (Nminus).Fiber
  have hQqa : (QA).principalSymbol = atlasGlobalPrincipalSymbolClass A A' 1 qa :=
    (Q).principalSymbol_toAtlasPseudodifferentialOperator qfull hQpr
  -- Recover regularization certificates for the fixed horizontal families and Green domains.
  have hHorizontal₀ := (C).exists_horizontalLift_native_regularization
    S (E).Fiber A σ (E').Fiber hA JH Li Lo η
    N₀₀ N₁₀ e₀₀ e₁₀ he₀₀ hi₀₀ he₁₀ hi₁₀
  let boundH₀ : ℝ := hHorizontal₀.choose_spec.choose
  let boundHneg₀ : ℝ := hHorizontal₀.choose_spec.choose_spec.choose
  -- Project only the analytic certificates; the fixed families already carry their symbols.
  have hHorizontal₀Certificates :=
    hHorizontal₀.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hRH₀ (a : (A₀₀).smoothSections) :
      RH₀ ((Li).smoothToSobolev 1 a) = (Lo).smoothToSobolev 0 (H₀ a) :=
    hHorizontal₀Certificates.1 a
  have hboundH₀ : 0 ≤ boundH₀ := hHorizontal₀Certificates.2.1
  have hboundHneg₀ : 0 ≤ boundHneg₀ := hHorizontal₀Certificates.2.2.1
  have hPosH₀ (ε : Eps) (a : (A₀₀).smoothSections) :
      ‖(Lo).smoothToSobolev 0
        ((S₁₀).symm ((nativeU₀ ε).toLinearMap (S₀₀ a)) - H₀ a)‖ ≤
        boundH₀ * ε.val * ‖(Li).smoothToSobolev 1 a‖ :=
    hHorizontal₀Certificates.2.2.2.2.2.1 ε a
  have hNegH₀ (ε : Eps) (a : (A₀₀).smoothSections) :
      ‖(Lo).smoothToSobolev (-1)
        ((S₁₀).symm ((nativeU₀ ε).toLinearMap (S₀₀ a)) - H₀ a)‖ ≤
        boundHneg₀ * ε.val * ‖(Li).smoothToSobolev 0 a‖ :=
    hHorizontal₀Certificates.2.2.2.2.2.2 ε a
  have hHorizontal₁ := (C).exists_horizontalLift_native_regularization
    S (E).Fiber A' σ' (E').Fiber hA' JH' Li₁ Lo₁ η
    N₀₁ N₁₁ e₀₁ e₁₁ he₀₁ hi₀₁ he₁₁ hi₁₁
  let boundH₁ : ℝ := hHorizontal₁.choose_spec.choose
  let boundHneg₁ : ℝ := hHorizontal₁.choose_spec.choose_spec.choose
  have hHorizontal₁Certificates :=
    hHorizontal₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hRH₁ (a : (A₀₁).smoothSections) :
      RH₁ ((Li₁).smoothToSobolev 1 a) = (Lo₁).smoothToSobolev 0 (H₁ a) :=
    hHorizontal₁Certificates.1 a
  have hboundH₁ : 0 ≤ boundH₁ := hHorizontal₁Certificates.2.1
  have hboundHneg₁ : 0 ≤ boundHneg₁ := hHorizontal₁Certificates.2.2.1
  have hPosH₁ (ε : Eps) (a : (A₀₁).smoothSections) :
      ‖(Lo₁).smoothToSobolev 0
        ((S₁₁).symm ((nativeU₁ ε).toLinearMap (S₀₁ a)) - H₁ a)‖ ≤
        boundH₁ * ε.val * ‖(Li₁).smoothToSobolev 1 a‖ :=
    hHorizontal₁Certificates.2.2.2.2.2.1 ε a
  have hNegH₁ (ε : Eps) (a : (A₀₁).smoothSections) :
      ‖(Lo₁).smoothToSobolev (-1)
        ((S₁₁).symm ((nativeU₁ ε).toLinearMap (S₀₁ a)) - H₁ a)‖ ≤
        boundHneg₁ * ε.val * ‖(Li₁).smoothToSobolev 0 a‖ :=
    hHorizontal₁Certificates.2.2.2.2.2.2 ε a
  -- Retain this vertical row's maps, residual, constants and paired estimates from one certificate.
  let row₀ := associatedSphereVerticalSelection₀ s g
  let CpV₀ : ℝ := row₀.val.1
  let CnV₀ : ℝ := row₀.val.2.1
  let W₀ : (A₀₀).smoothSections →ₗ[ℂ] (A₀₁).smoothSections := row₀.val.2.2.2.2.1
  have hCpV₀ : 0 ≤ CpV₀ := row₀.property.1
  have hCnV₀ : 0 ≤ CnV₀ := row₀.property.2.1
  have hWR₀ (a : (A₀₀).smoothSections) :
      WR₀ ((k₀₀).smoothToL2 η (S₀₀ a)) =
        (k₀₁).smoothToL2 η (S₀₁ (W₀ a)) :=
    row₀.property.2.2.2.2.1 a
  have hPosV₀ (ε : Eps) (a : (A₀₀).smoothSections) :
      ‖(Li₁).smoothToSobolev 0
        ((S₀₁).symm ((nativeV₀ ε).toLinearMap (S₀₀ a)) - V₀ a + W₀ a)‖ ≤
          CpV₀ * ε.val * ‖(Li).smoothToSobolev 1 a‖ :=
    row₀.property.2.2.2.2.2.1 ε a
  have hNegV₀ (ε : Eps) (a : (A₀₀).smoothSections) :
      ‖(Li₁).smoothToSobolev (-1)
        ((S₀₁).symm ((nativeV₀ ε).toLinearMap (S₀₀ a)) - V₀ a + W₀ a)‖ ≤
          CnV₀ * ε.val * ‖(Li).smoothToSobolev 0 a‖ :=
    row₀.property.2.2.2.2.2.2 ε a
  -- Retain this vertical row's maps, residual, constants and paired estimates from one certificate.
  let row₁ := associatedSphereVerticalSelection₁ s g
  let CpV₁ : ℝ := row₁.val.1
  let CnV₁ : ℝ := row₁.val.2.1
  let W₁ : (A₁₀).smoothSections →ₗ[ℂ] (A₁₁).smoothSections := row₁.val.2.2.2.2.1
  have hCpV₁ : 0 ≤ CpV₁ := row₁.property.1
  have hCnV₁ : 0 ≤ CnV₁ := row₁.property.2.1
  have hWR₁ (a : (A₁₀).smoothSections) :
      WR₁ ((k₁₀).smoothToL2 η (S₁₀ a)) =
        (k₁₁).smoothToL2 η (S₁₁ (W₁ a)) :=
    row₁.property.2.2.2.2.1 a
  have hPosV₁ (ε : Eps) (a : (A₁₀).smoothSections) :
      ‖(Lo₁).smoothToSobolev 0
        ((S₁₁).symm ((nativeV₁ ε).toLinearMap (S₁₀ a)) - V₁ a + W₁ a)‖ ≤
          CpV₁ * ε.val * ‖(Lo).smoothToSobolev 1 a‖ :=
    row₁.property.2.2.2.2.2.1 ε a
  have hNegV₁ (ε : Eps) (a : (A₁₀).smoothSections) :
      ‖(Lo₁).smoothToSobolev (-1)
        ((S₁₁).symm ((nativeV₁ ε).toLinearMap (S₁₀ a)) - V₁ a + W₁ a)‖ ≤
          CnV₁ * ε.val * ‖(Lo).smoothToSobolev 0 a‖ :=
    row₁.property.2.2.2.2.2.2 ε a
  -- Atlas rows are the canonical transports of the four fixed native families.
  let Uat₀ (ε : Eps) : (A₀₀).smoothSections →ₗ[ℂ] (A₁₀).smoothSections :=
    (S₁₀).symm.toLinearMap.comp ((nativeU₀ ε).toLinearMap.comp (S₀₀).toLinearMap)
  let Uat₁ (ε : Eps) : (A₀₁).smoothSections →ₗ[ℂ] (A₁₁).smoothSections :=
    (S₁₁).symm.toLinearMap.comp ((nativeU₁ ε).toLinearMap.comp (S₀₁).toLinearMap)
  let Vat₀ (ε : Eps) : (A₀₀).smoothSections →ₗ[ℂ] (A₀₁).smoothSections :=
    (S₀₁).symm.toLinearMap.comp ((nativeV₀ ε).toLinearMap.comp (S₀₀).toLinearMap)
  let Vat₁ (ε : Eps) : (A₁₀).smoothSections →ₗ[ℂ] (A₁₁).smoothSections :=
    (S₁₁).symm.toLinearMap.comp ((nativeV₁ ε).toLinearMap.comp (S₁₀).toLinearMap)
  have hnativeU₀Atlas (ε : Eps) (w : (A₀₀).smoothSections) :
      (nativeU₀ ε).toLinearMap (S₀₀ w) = S₁₀ (Uat₀ ε w) := by
    exact ((S₁₀).apply_symm_apply _).symm
  have hnativeU₁Atlas (ε : Eps) (w : (A₀₁).smoothSections) :
      (nativeU₁ ε).toLinearMap (S₀₁ w) = S₁₁ (Uat₁ ε w) := by
    exact ((S₁₁).apply_symm_apply _).symm
  have hnativeV₀Atlas (ε : Eps) (w : (A₀₀).smoothSections) :
      (nativeV₀ ε).toLinearMap (S₀₀ w) = S₀₁ (Vat₀ ε w) := by
    exact ((S₀₁).apply_symm_apply _).symm
  have hnativeV₁Atlas (ε : Eps) (w : (A₁₀).smoothSections) :
      (nativeV₁ ε).toLinearMap (S₁₀ w) = S₁₁ (Vat₁ ε w) := by
    exact ((S₁₁).apply_symm_apply _).symm
  -- These four completion maps preserve precisely the original Green section inclusions.
  have hΘ₀₀Data := (A₀₀).exists_sobolevZero_equiv_nativeL2
    Li l₀₀ hl₀₀ N₀₀ k₀₀ η e₀₀ he₀₀ hi₀₀ hk₀₀
  obtain ⟨Θ₀₀, hΘ₀₀, _hJ₀₀inj, _hJ₀₀⟩ := hΘ₀₀Data
  have hΘ₁₀Data := (A₁₀).exists_sobolevZero_equiv_nativeL2
    Lo l₁₀ hl₁₀ N₁₀ k₁₀ η e₁₀ he₁₀ hi₁₀ hk₁₀
  obtain ⟨Θ₁₀, hΘ₁₀, _hJ₁₀inj, _hJ₁₀⟩ := hΘ₁₀Data
  have hΘ₀₁Data := (A₀₁).exists_sobolevZero_equiv_nativeL2
    Li₁ l₀₁ hl₀₁ N₀₁ k₀₁ η e₀₁ he₀₁ hi₀₁ hk₀₁
  obtain ⟨Θ₀₁, hΘ₀₁, _hJ₀₁inj, _hJ₀₁⟩ := hΘ₀₁Data
  have hΘ₁₁Data := (A₁₁).exists_sobolevZero_equiv_nativeL2
    Lo₁ l₁₁ hl₁₁ N₁₁ k₁₁ η e₁₁ he₁₁ hi₁₁ hk₁₁
  obtain ⟨Θ₁₁, hΘ₁₁, _hJ₁₁inj, _hJ₁₁⟩ := hΘ₁₁Data
  -- The existing full-extension theorem retains the original Q and fixed atlas domains.
  obtain ⟨RV₀, hRV₀⟩ := exists_associatedSphereTensorVertical_sobolevExtension
    (a := (E).rank) S (E).Fiber F F' σ σ' hσ hσ' k k' ν L₀ L₁ JV b hJV
    QA hQA qa hQqa Rq Li Li₁ l₀₀ hl₀₀ l₀₁ hl₀₁ N₀₀ N₀₁ k₀₀ k₀₁ η
    e₀₀ he₀₀ hi₀₀ e₀₁ he₀₁ hi₀₁ hk₀₀ hk₀₁
  obtain ⟨RV₁, hRV₁⟩ := exists_associatedSphereTensorVertical_sobolevExtension
    (a := (E').rank) S (E').Fiber F F' σ σ' hσ hσ' k k' ν L₀ L₁ JV' b hJV'
    QA hQA qa hQqa Rq Lo Lo₁ l₁₀ hl₁₀ l₁₁ hl₁₁ N₁₀ N₁₁ k₁₀ k₁₁ η
    e₁₀ he₁₀ hi₁₀ e₁₁ he₁₁ hi₁₁ hk₁₀ hk₁₁
  -- The reverse horizontal maps retain the exact adjoints of the original base pieces.
  have hCAdj₀ := (C).exists_exact_horizontalAdjoint_localization S (E).Fiber A σ (E').Fiber
    h h' hA β₀ hβ₀ hsβ₀ hβ₀one H₀' hH₀formula
  let CAdj₀ := hCAdj₀.choose
  have hCAdj₀base := hCAdj₀.choose_spec.1
  have hCAdj₀lift : CAdj₀.horizontalLift S (E').Fiber A σ (E).Fiber hA = H₀a :=
    hCAdj₀.choose_spec.2.trans (hH₀sum).symm
  have hCAdj₁ := (C).exists_exact_horizontalAdjoint_localization S (E).Fiber A' σ' (E').Fiber
    h h' hA' β₁ hβ₁ hsβ₁ hβ₁one H₁' hH₁formula
  let CAdj₁ := hCAdj₁.choose
  have hCAdj₁base := hCAdj₁.choose_spec.1
  have hCAdj₁lift : CAdj₁.horizontalLift S (E').Fiber A' σ' (E).Fiber hA' = H₁a :=
    hCAdj₁.choose_spec.2.trans (hH₁sum).symm
  obtain ⟨RH₀a, _Cp₀, _Cn₀, _Pn₀, _pn₀, hRH₀aRaw, _⟩ :=
    CAdj₀.exists_horizontalLift_native_regularization
      S (E').Fiber A σ (E).Fiber hA JH Lo Li η
      N₁₀ N₀₀ e₁₀ e₀₀ he₁₀ hi₁₀ he₀₀ hi₀₀
  have hRH₀a (u : (A₁₀).smoothSections) :
      RH₀a ((Lo).smoothToSobolev 1 u) = (Li).smoothToSobolev 0 (H₀a u) := by
    -- First retain the raw extension formula for this exact localization and map.
    have hRaw : RH₀a ((Lo).smoothToSobolev 1 u) =
        (Li).smoothToSobolev 0
          (CAdj₀.horizontalLift S (E').Fiber A σ (E).Fiber hA u) :=
      hRH₀aRaw u
    -- Apply the known operator equality only through the required Sobolev inclusion.
    have hTarget :
        (Li).smoothToSobolev 0
          (CAdj₀.horizontalLift S (E').Fiber A σ (E).Fiber hA u) =
            (Li).smoothToSobolev 0 (H₀a u) :=
      congrArg (fun op : (A₁₀).smoothSections →ₗ[ℂ] (A₀₀).smoothSections ↦
        (Li).smoothToSobolev 0 (op u)) hCAdj₀lift
    exact hRaw.trans hTarget
  obtain ⟨RH₁a, _Cp₁, _Cn₁, _Pn₁, _pn₁, hRH₁aRaw, _⟩ :=
    CAdj₁.exists_horizontalLift_native_regularization
      S (E').Fiber A' σ' (E).Fiber hA' JH' Lo₁ Li₁ η
      N₁₁ N₀₁ e₁₁ e₀₁ he₁₁ hi₁₁ he₀₁ hi₀₁
  have hRH₁a (u : (A₁₁).smoothSections) :
      RH₁a ((Lo₁).smoothToSobolev 1 u) = (Li₁).smoothToSobolev 0 (H₁a u) := by
    -- The second row retains its original atlas and native choices as well.
    have hRaw : RH₁a ((Lo₁).smoothToSobolev 1 u) =
        (Li₁).smoothToSobolev 0
          (CAdj₁.horizontalLift S (E').Fiber A' σ' (E).Fiber hA' u) :=
      hRH₁aRaw u
    have hTarget :
        (Li₁).smoothToSobolev 0
          (CAdj₁.horizontalLift S (E').Fiber A' σ' (E).Fiber hA' u) =
            (Li₁).smoothToSobolev 0 (H₁a u) :=
      congrArg (fun op : (A₁₁).smoothSections →ₗ[ℂ] (A₀₁).smoothSections ↦
        (Li₁).smoothToSobolev 0 (op u)) hCAdj₁lift
    exact hRaw.trans hTarget
  -- A principal representative of the literal fiber adjoint supplies its full extension.
  -- It is used only for boundedness; the approximating family remains the original one.
  have hJARep := (JA).isPseudodifferentialOperator
  let Jsize := hJARep.choose
  let Jpieces := hJARep.choose_spec.choose
  have hJpieces := hJARep.choose_spec.choose_spec
  let ja := ∑ j : Fin Jsize, (Jpieces j).globalSymbol
  have hja : (JA).principalSymbol = atlasGlobalPrincipalSymbolClass A' A 1 ja :=
    (JA).principalSymbol_eq_of_representation Jsize Jpieces hJpieces
  let Rja := Classical.choice (nonempty_atlasQuantizationPresentation A' A)
  have hRV₀aData := exists_associatedSphereTensorVertical_sobolevExtension
    (a := (E).rank) S (E).Fiber F' F σ' σ hσ' hσ k' k ν L₁ L₀ JV b hJV
    JA hJA ja hja Rja Li₁ Li l₀₁ hl₀₁ l₀₀ hl₀₀ N₀₁ N₀₀ k₀₁ k₀₀ η
    e₀₁ he₀₁ hi₀₁ e₀₀ he₀₀ hi₀₀ hk₀₁ hk₀₀
  let RV₀a := hRV₀aData.choose
  have hRV₀a := hRV₀aData.choose_spec
  have hRV₁aData := exists_associatedSphereTensorVertical_sobolevExtension
    (a := (E').rank) S (E').Fiber F' F σ' σ hσ' hσ k' k ν L₁ L₀ JV' b hJV'
    JA hJA ja hja Rja Lo₁ Lo l₁₁ hl₁₁ l₁₀ hl₁₀ N₁₁ N₁₀ k₁₁ k₁₀ η
    e₁₁ he₁₁ hi₁₁ e₁₀ he₁₀ hi₁₀ hk₁₁ hk₁₀
  let RV₁a := hRV₁aData.choose
  have hRV₁a := hRV₁aData.choose_spec
  let := (cotangentLinearModelHomeomorph (split).symm Z).symm.t2Space
  let := (cotangentLinearModelHomeomorph (split).symm Z).isOpenEmbedding.locallyCompactSpace
  -- The reverse coordinates use the supplied native sums and fixed Green completions.
  obtain ⟨_PhiPlus, PsiPlus, _hPhiPlus, hPsiPlus⟩ :=
    exists_sobolev_and_nativeL2_coordinates_of_atlas_native_sum (μ := η)
      A₀₀ Li A₁₁ Lo₁ N₀₀ N₁₁ Nplus (DD 0) (DD 1) Dplus
      Θ₀₀ Θ₁₁ i₀₀ i₁₁ hΘ₀₀ hΘ₁₁
      e₀₀ he₀₀ hi₀₀ e₁₁ he₁₁ hi₁₁ (ePlus).linearEquiv hPlus₀ hPlus₁
  obtain ⟨PhiMinus, hPhiMinus⟩ := exists_sobolevEquiv_of_atlas_native_sum (μ := η)
    A₁₀ Lo A₀₁ Li₁ N₁₀ N₀₁ Nminus (HH 0) (HH 1) Dminus 1
    e₁₀ he₁₀ hi₁₀ e₀₁ he₀₁ hi₀₁ (eMinus).linearEquiv hMinus₀ hMinus₁
  have hepsSeq : Tendsto (fun m ↦ (epsSeq m).val) atTop (𝓝 0) :=
    associatedSphereCutoffSequence_tendsto
  have hSection₀₀ (u v : (A₀₀).smoothSections) :
      (k₀₀).sectionPairing η (S₀₀ u) (S₀₀ v) =
        ∫ z, ((l₀₀).toCore z).inner (u.val z) (v.val z) ∂η := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₀₀ z (u.val z) (v.val z)
  have hSection₁₀ (u v : (A₁₀).smoothSections) :
      (k₁₀).sectionPairing η (S₁₀ u) (S₁₀ v) =
        ∫ z, ((l₁₀).toCore z).inner (u.val z) (v.val z) ∂η := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₁₀ z (u.val z) (v.val z)
  have hSection₀₁ (u v : (A₀₁).smoothSections) :
      (k₀₁).sectionPairing η (S₀₁ u) (S₀₁ v) =
        ∫ z, ((l₀₁).toCore z).inner (u.val z) (v.val z) ∂η := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₀₁ z (u.val z) (v.val z)
  have hSection₁₁ (u v : (A₁₁).smoothSections) :
      (k₁₁).sectionPairing η (S₁₁ u) (S₁₁ v) =
        ∫ z, ((l₁₁).toCore z).inner (u.val z) (v.val z) ∂η := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hk₁₁ z (u.val z) (v.val z)
  -- H₀: retain the actual finite sum and its original metric pairing.
  have hPairH₀ (u : (A₀₀).smoothSections) (v : (A₁₀).smoothSections) :
      (k₁₀).sectionPairing η (S₁₀ (H₀ u)) (S₁₀ v) =
        (k₀₀).sectionPairing η (S₀₀ u) (S₀₀ (H₀a v)) := by
    rw [hSection₁₀, hSection₀₀]
    exact hH₀ u v
  -- Keep the specified finite family and both original Sobolev error bounds.
  have hLimitH₀Data :=
    exists_atlas_native_residual_paired_limit η A₀₀ A₁₀ Li Lo
      N₀₀ N₁₀ k₀₀ k₁₀ (DD 0) (HH 0) e₀₀ e₁₀ he₀₀ hi₀₀ he₁₀ hi₁₀
      Θ₀₀ Θ₁₀ hΘ₀₀ hΘ₁₀ H₀ (0) H₀a RH₀ RH₀a (0)
      hPairH₀
      (fun u ↦ by simp only [_root_.zero_apply, LinearMap.zero_apply, map_zero])
      hRH₀ hRH₀a boundH₀ (boundHneg₀) hboundH₀ (hboundHneg₀)
      atTop (fun m ↦ (epsSeq m).val) (fun m ↦ (epsSeq m).property.1.le) hepsSeq
      (fun m ↦ nativeU₀ (epsSeq m))
      (fun m ↦ Uat₀ (epsSeq m))
      (fun m ↦ hnativeU₀Atlas (epsSeq m))
      (fun m u ↦ by
        simpa only [Uat₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.zero_apply, add_zero] using hPosH₀ (epsSeq m) u)
      (fun m u ↦ by
        simpa only [Uat₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.zero_apply, add_zero] using hNegH₀ (epsSeq m) u)
  -- H₁: retain the actual finite sum and its original metric pairing.
  have hPairH₁ (u : (A₀₁).smoothSections) (v : (A₁₁).smoothSections) :
      (k₁₁).sectionPairing η (S₁₁ (H₁ u)) (S₁₁ v) =
        (k₀₁).sectionPairing η (S₀₁ u) (S₀₁ (H₁a v)) := by
    rw [hSection₁₁, hSection₀₁]
    exact hH₁ u v
  -- Keep the specified finite family and both original Sobolev error bounds.
  have hLimitH₁Data :=
    exists_atlas_native_residual_paired_limit η A₀₁ A₁₁ Li₁ Lo₁
      N₀₁ N₁₁ k₀₁ k₁₁ (HH 1) (DD 1) e₀₁ e₁₁ he₀₁ hi₀₁ he₁₁ hi₁₁
      Θ₀₁ Θ₁₁ hΘ₀₁ hΘ₁₁ H₁ (0) H₁a RH₁ RH₁a (0)
      hPairH₁
      (fun u ↦ by simp only [_root_.zero_apply, LinearMap.zero_apply, map_zero])
      hRH₁ hRH₁a boundH₁ (boundHneg₁) hboundH₁ (hboundHneg₁)
      atTop (fun m ↦ (epsSeq m).val) (fun m ↦ (epsSeq m).property.1.le) hepsSeq
      (fun m ↦ nativeU₁ (epsSeq m))
      (fun m ↦ Uat₁ (epsSeq m))
      (fun m ↦ hnativeU₁Atlas (epsSeq m))
      (fun m u ↦ by
        simpa only [Uat₁, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.zero_apply, add_zero] using hPosH₁ (epsSeq m) u)
      (fun m u ↦ by
        simpa only [Uat₁, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.zero_apply, add_zero] using hNegH₁ (epsSeq m) u)
  -- The vertical limits use the residual and both bounds from the same row provider.
  have hPairV₀ (u : (A₀₀).smoothSections) (v : (A₀₁).smoothSections) :
      (k₀₁).sectionPairing η (S₀₁ (V₀ u)) (S₀₁ v) =
        (k₀₀).sectionPairing η (S₀₀ u) (S₀₀ (V₀a v)) := by
    rw [hSection₀₁, hSection₀₀]
    exact hV₀ u v
  have hLimitV₀Data :=
    exists_atlas_native_residual_paired_limit η A₀₀ A₀₁ Li Li₁
      N₀₀ N₀₁ k₀₀ k₀₁ (DD 0) (HH 1) e₀₀ e₀₁ he₀₀ hi₀₀ he₀₁ hi₀₁
      Θ₀₀ Θ₀₁ hΘ₀₀ hΘ₀₁ V₀ W₀ V₀a RV₀ RV₀a WR₀
      hPairV₀ hWR₀ hRV₀ hRV₀a CpV₀ CnV₀ hCpV₀ hCnV₀
      atTop (fun m ↦ (epsSeq m).val) (fun m ↦ (epsSeq m).property.1.le) hepsSeq
      (fun m ↦ nativeV₀ (epsSeq m)) (fun m ↦ Vat₀ (epsSeq m))
      (fun m ↦ hnativeV₀Atlas (epsSeq m))
      (fun m ↦ hPosV₀ (epsSeq m)) (fun m ↦ hNegV₀ (epsSeq m))
  have hPairV₁ (u : (A₁₀).smoothSections) (v : (A₁₁).smoothSections) :
      (k₁₁).sectionPairing η (S₁₁ (V₁ u)) (S₁₁ v) =
        (k₁₀).sectionPairing η (S₁₀ u) (S₁₀ (V₁a v)) := by
    rw [hSection₁₁, hSection₁₀]
    exact hV₁ u v
  have hLimitV₁Data :=
    exists_atlas_native_residual_paired_limit η A₁₀ A₁₁ Lo Lo₁
      N₁₀ N₁₁ k₁₀ k₁₁ (HH 0) (DD 1) e₁₀ e₁₁ he₁₀ hi₁₀ he₁₁ hi₁₁
      Θ₁₀ Θ₁₁ hΘ₁₀ hΘ₁₁ V₁ W₁ V₁a RV₁ RV₁a WR₁
      hPairV₁ hWR₁ hRV₁ hRV₁a CpV₁ CnV₁ hCpV₁ hCnV₁
      atTop (fun m ↦ (epsSeq m).val) (fun m ↦ (epsSeq m).property.1.le) hepsSeq
      (fun m ↦ nativeV₁ (epsSeq m)) (fun m ↦ Vat₁ (epsSeq m))
      (fun m ↦ hnativeV₁Atlas (epsSeq m))
      (fun m ↦ hPosV₁ (epsSeq m)) (fun m ↦ hNegV₁ (epsSeq m))
  -- The invariant full symbols control the original graph norms in all four orientations.
  let Qadj := (Q).metricFormalAdjoint k k'
  have hQadj := (Q).isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hνinv hQ
  let qAdj := (k).symbolSpaceAdjoint k' qfull
  have hQadjpr : Qadj.principalSymbol =
      globalPrincipalSymbolClass (F').Fiber (F).Fiber 1 qAdj := by
    rw [(Q).principalSymbol_metricFormalAdjoint, hQpr, (k).principalSymbolAdjoint_class]
  have hqAdjfixed := (k).symbolAdjoint_fixed IG σ σ' k' hk hk' (qfull).val hqfixed
  have hqAdjfull := (Qadj.isElliptic_iff_of_principalSymbol_eq qAdj hQadjpr).mp
    (((Q).isElliptic_metricFormalAdjoint_iff k k').mpr hQell)
  have hCAdj₀ell : CAdj₀.baseOperator.IsElliptic := by
    rw [hCAdj₀base]
    exact ((C).baseOperator.isElliptic_metricFormalAdjoint_iff h h').mpr hCell
  have hCAdj₁ell : CAdj₁.baseOperator.IsElliptic := by
    rw [hCAdj₁base]
    exact ((C).baseOperator.isElliptic_metricFormalAdjoint_iff h h').mpr hCell
  -- The ₀₀ orientation uses the original source domain and its original three L2 maps.
  have hReverse₀₀Data := associated_joint_reverse_bound_of_invariant_full_symbol
    S μ E E' F F' σ σ' hσ hσ' ν k k' hk hk'
    Q hQ qfull hQpr hqfixed hqfull C hCell h h'
    Li l₀₀ hl₀₀ l₁₀ hl₁₀ l₀₁ hl₀₁
    N₀₀ N₁₀ N₀₁ N₁₁ k₀₀ k₁₀ k₀₁ k₁₁ η
    e₀₀ he₀₀ hi₀₀ e₁₀ he₁₀ hi₁₀
    e₀₁ he₀₁ hi₀₁ e₁₁ he₁₁ hi₁₁
    hk₀₀ hk₁₀ hk₀₁ hkPure₀₀ hkPure₁₀ hkPure₀₁ hkPure₁₁
  let B₀₀ : ℝ := hReverse₀₀Data.choose
  have hB₀₀ : 0 ≤ B₀₀ := hReverse₀₀Data.choose_spec.1
  have hReverse₀₀ (w : (A₀₀).smoothSections) :
      ‖(Li).smoothToSobolev 1 w‖ ≤ B₀₀ *
        (‖i₀₀ w‖ + ‖i₁₀ (H₀ w)‖ + ‖i₀₁ (V₀ w)‖) := by
    exact hReverse₀₀Data.choose_spec.2 w
  -- The ₁₀ orientation uses the original source domain and its original three L2 maps.
  have hReverse₁₀Data := associated_joint_reverse_bound_of_invariant_full_symbol
    S μ E' E F F' σ σ' hσ hσ' ν k k' hk hk'
    Q hQ qfull hQpr hqfixed hqfull CAdj₀ hCAdj₀ell h' h
    Lo l₁₀ hl₁₀ l₀₀ hl₀₀ l₁₁ hl₁₁
    N₁₀ N₀₀ N₁₁ N₀₁ k₁₀ k₀₀ k₁₁ k₀₁ η
    e₁₀ he₁₀ hi₁₀ e₀₀ he₀₀ hi₀₀
    e₁₁ he₁₁ hi₁₁ e₀₁ he₀₁ hi₀₁
    hk₁₀ hk₀₀ hk₁₁ hkPure₁₀ hkPure₀₀ hkPure₁₁ hkPure₀₁
  let B₁₀ : ℝ := hReverse₁₀Data.choose
  have hB₁₀ : 0 ≤ B₁₀ := hReverse₁₀Data.choose_spec.1
  have hReverse₁₀ (w : (A₁₀).smoothSections) :
      ‖(Lo).smoothToSobolev 1 w‖ ≤ B₁₀ *
        (‖i₁₀ w‖ + ‖i₀₀ (H₀a w)‖ + ‖i₁₁ (V₁ w)‖) := by
    -- Keep the same native estimate and replace only its horizontal operator.
    have hraw : ‖(Lo).smoothToSobolev 1 w‖ ≤ B₁₀ *
        (‖i₁₀ w‖ + ‖i₀₀ (CAdj₀.horizontalLift S (E').Fiber A σ (E).Fiber hA w)‖ + ‖i₁₁ (V₁ w)‖) :=
      hReverse₁₀Data.choose_spec.2 w
    have hright : B₁₀ *
        (‖i₁₀ w‖ + ‖i₀₀ (CAdj₀.horizontalLift S (E').Fiber A σ (E).Fiber hA w)‖ + ‖i₁₁ (V₁ w)‖) =
        B₁₀ * (‖i₁₀ w‖ + ‖i₀₀ (H₀a w)‖ + ‖i₁₁ (V₁ w)‖) :=
      congrArg (fun horiz : (A₁₀).smoothSections →ₗ[ℂ] (A₀₀).smoothSections ↦
        B₁₀ * (‖i₁₀ w‖ + ‖i₀₀ (horiz w)‖ + ‖i₁₁ (V₁ w)‖)) hCAdj₀lift
    exact hraw.trans_eq hright
  -- The ₀₁ orientation uses the original source domain and its original three L2 maps.
  have hReverse₀₁Data := associated_joint_reverse_bound_of_invariant_full_symbol
    S μ E E' F' F σ' σ hσ' hσ ν k' k hk' hk
    Qadj hQadj qAdj hQadjpr hqAdjfixed hqAdjfull C hCell h h'
    Li₁ l₀₁ hl₀₁ l₁₁ hl₁₁ l₀₀ hl₀₀
    N₀₁ N₁₁ N₀₀ N₁₀ k₀₁ k₁₁ k₀₀ k₁₀ η
    e₀₁ he₀₁ hi₀₁ e₁₁ he₁₁ hi₁₁
    e₀₀ he₀₀ hi₀₀ e₁₀ he₁₀ hi₁₀
    hk₀₁ hk₁₁ hk₀₀ hkPure₀₁ hkPure₁₁ hkPure₀₀ hkPure₁₀
  let B₀₁ : ℝ := hReverse₀₁Data.choose
  have hB₀₁ : 0 ≤ B₀₁ := hReverse₀₁Data.choose_spec.1
  have hReverse₀₁ (w : (A₀₁).smoothSections) :
      ‖(Li₁).smoothToSobolev 1 w‖ ≤ B₀₁ *
        (‖i₀₁ w‖ + ‖i₁₁ (H₁ w)‖ + ‖i₀₀ (V₀a w)‖) := by
    exact hReverse₀₁Data.choose_spec.2 w
  -- The ₁₁ orientation uses the original source domain and its original three L2 maps.
  have hReverse₁₁Data := associated_joint_reverse_bound_of_invariant_full_symbol
    S μ E' E F' F σ' σ hσ' hσ ν k' k hk' hk
    Qadj hQadj qAdj hQadjpr hqAdjfixed hqAdjfull CAdj₁ hCAdj₁ell h' h
    Lo₁ l₁₁ hl₁₁ l₀₁ hl₀₁ l₁₀ hl₁₀
    N₁₁ N₀₁ N₁₀ N₀₀ k₁₁ k₀₁ k₁₀ k₀₀ η
    e₁₁ he₁₁ hi₁₁ e₀₁ he₀₁ hi₀₁
    e₁₀ he₁₀ hi₁₀ e₀₀ he₀₀ hi₀₀
    hk₁₁ hk₀₁ hk₁₀ hkPure₁₁ hkPure₀₁ hkPure₁₀ hkPure₀₀
  let B₁₁ : ℝ := hReverse₁₁Data.choose
  have hB₁₁ : 0 ≤ B₁₁ := hReverse₁₁Data.choose_spec.1
  have hReverse₁₁ (w : (A₁₁).smoothSections) :
      ‖(Lo₁).smoothToSobolev 1 w‖ ≤ B₁₁ *
        (‖i₁₁ w‖ + ‖i₀₁ (H₁a w)‖ + ‖i₁₀ (V₁a w)‖) := by
    -- Keep the same native estimate and replace only its horizontal operator.
    have hraw : ‖(Lo₁).smoothToSobolev 1 w‖ ≤ B₁₁ *
        (‖i₁₁ w‖ + ‖i₀₁ (CAdj₁.horizontalLift S (E').Fiber A' σ' (E).Fiber hA' w)‖ +
          ‖i₁₀ (V₁a w)‖) :=
      hReverse₁₁Data.choose_spec.2 w
    have hright : B₁₁ *
        (‖i₁₁ w‖ + ‖i₀₁ (CAdj₁.horizontalLift S (E').Fiber A' σ' (E).Fiber hA' w)‖ +
          ‖i₁₀ (V₁a w)‖) =
        B₁₁ * (‖i₁₁ w‖ + ‖i₀₁ (H₁a w)‖ + ‖i₁₀ (V₁a w)‖) :=
      congrArg (fun horiz : (A₁₁).smoothSections →ₗ[ℂ] (A₀₁).smoothSections ↦
        B₁₁ * (‖i₁₁ w‖ + ‖i₀₁ (horiz w)‖ + ‖i₁₀ (V₁a w)‖)) hCAdj₁lift
    exact hraw.trans_eq hright
  -- Assemble the completions, paired limits and four reverse estimates.
  exact ⟨{
    sobolevZero₀₀ := Θ₀₀
    sobolevZero₀₀_smooth := hΘ₀₀
    sobolevZero₁₀ := Θ₁₀
    sobolevZero₁₀_smooth := hΘ₁₀
    sobolevZero₀₁ := Θ₀₁
    sobolevZero₀₁_smooth := hΘ₀₁
    sobolevZero₁₁ := Θ₁₁
    sobolevZero₁₁_smooth := hΘ₁₁
    phiMinus := PhiMinus
    psiPlus := PsiPlus
    phiMinus_smooth := hPhiMinus
    psiPlus_smooth := hPsiPlus
    verticalRealization₀ := RV₀
    verticalRealization₀_smooth := hRV₀
    verticalRealization₁ := RV₁
    verticalRealization₁_smooth := hRV₁
    horizontalAdjointRealization₀ := RH₀a
    horizontalAdjointRealization₀_smooth := hRH₀a
    horizontalAdjointRealization₁ := RH₁a
    horizontalAdjointRealization₁_smooth := hRH₁a
    verticalAdjointRealization₀ := RV₀a
    verticalAdjointRealization₀_smooth := hRV₀a
    verticalAdjointRealization₁ := RV₁a
    verticalAdjointRealization₁_smooth := hRV₁a
    horizontal₀_paired_limit := hLimitH₀Data
    horizontal₁_paired_limit := hLimitH₁Data
    vertical₀_paired_limit := hLimitV₀Data
    vertical₁_paired_limit := hLimitV₁Data
    reverseBound₀₀ := B₀₀
    reverseBound₀₀_nonneg := hB₀₀
    reverseBound₀₀_estimate := hReverse₀₀
    reverseBound₁₀ := B₁₀
    reverseBound₁₀_nonneg := hB₁₀
    reverseBound₁₀_estimate := hReverse₁₀
    reverseBound₀₁ := B₀₁
    reverseBound₀₁_nonneg := hB₀₁
    reverseBound₀₁_estimate := hReverse₀₁
    reverseBound₁₁ := B₁₁
    reverseBound₁₁_nonneg := hB₁₁
    reverseBound₁₁_estimate := hReverse₁₁ }⟩

/-- The selected kernel witnesses retain the prescribed common data. -/
def associatedSphereKernelWitness : AssociatedSphereKernelWitness s g sums :=
  Classical.choice (nonempty_associatedSphereKernelWitness s g sums)

end AtiyahSinger
