/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereKernelWitness

/-!
# A small cutoff with the original Green kernel index

Public module ID: M0124.

Given a positive threshold below which the supplied cutoff family is elliptic,
the four corner approximations give a parameter within that threshold whose
coordinate index equals the difference of the original Green kernel dimensions.
The original native models, coordinate maps and metric-adjoint pair are retained.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AtiyahSinger

/-! Parenthesized projections and local instance telescopes are checked when the notation
is elaborated at use sites. This Lean version has no quotation prechecker for those
syntax forms, so only the affected notation commands disable that preliminary check. -/

section KernelParameter

open Bundle ComplexBundle Filter MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate Topology

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

/-! The local instances are the same canonical models used in the original core call. -/

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
set_option quotPrecheck false in
local notation "qfFamily" => verticalCutoffFactor S (E).Fiber A σ A' σ' hA hA' JV b
  (associatedSphereFiberQuantization s).size
  (fun j ↦ ((associatedSphereFiberQuantization s).patch j).toPiece qa)

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
local notation "Rq" => associatedSphereFiberQuantization s
local notation "nativeU₀" => associatedSphereHorizontalFamily₀ s g
local notation "RH₀" => associatedSphereHorizontalRealization₀ s g
local notation "nativeU₁" => associatedSphereHorizontalFamily₁ s g
local notation "RH₁" => associatedSphereHorizontalRealization₁ s g
local notation "nativeV₀" => associatedSphereVerticalFamily₀ s g
local notation "WR₀" => associatedSphereVerticalResidualRealization₀ s g
local notation "nativeV₁" => associatedSphereVerticalFamily₁ s g
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

variable (coordinates : AssociatedSphereCoordinateWitness s g sums)
  (kernel : AssociatedSphereKernelWitness s g sums)

local notation "PhiPlus" => coordinates.phiPlus
local notation "PsiMinus" => coordinates.psiMinus
local notation "hPhiPlus" => coordinates.phiPlus_smooth
local notation "hPsiMinus" => coordinates.psiMinus_smooth
local notation "PhiMinus" => kernel.phiMinus
local notation "PsiPlus" => kernel.psiPlus
local notation "hPhiMinus" => kernel.phiMinus_smooth
local notation "hPsiPlus" => kernel.psiPlus_smooth
local notation "Θ₀₀" => kernel.sobolevZero₀₀
local notation "hΘ₀₀" => kernel.sobolevZero₀₀_smooth
local notation "Θ₁₀" => kernel.sobolevZero₁₀
local notation "hΘ₁₀" => kernel.sobolevZero₁₀_smooth
local notation "Θ₀₁" => kernel.sobolevZero₀₁
local notation "hΘ₀₁" => kernel.sobolevZero₀₁_smooth
local notation "Θ₁₁" => kernel.sobolevZero₁₁
local notation "hΘ₁₁" => kernel.sobolevZero₁₁_smooth
local notation "RV₀" => kernel.verticalRealization₀
local notation "hRV₀" => kernel.verticalRealization₀_smooth
local notation "RV₁" => kernel.verticalRealization₁
local notation "hRV₁" => kernel.verticalRealization₁_smooth
local notation "RH₀a" => kernel.horizontalAdjointRealization₀
local notation "hRH₀a" => kernel.horizontalAdjointRealization₀_smooth
local notation "RH₁a" => kernel.horizontalAdjointRealization₁
local notation "hRH₁a" => kernel.horizontalAdjointRealization₁_smooth
local notation "RV₀a" => kernel.verticalAdjointRealization₀
local notation "hRV₀a" => kernel.verticalAdjointRealization₀_smooth
local notation "RV₁a" => kernel.verticalAdjointRealization₁
local notation "hRV₁a" => kernel.verticalAdjointRealization₁_smooth
local notation "hLimitH₀Data" => kernel.horizontal₀_paired_limit
local notation "hLimitH₁Data" => kernel.horizontal₁_paired_limit
local notation "hLimitV₀Data" => kernel.vertical₀_paired_limit
local notation "hLimitV₁Data" => kernel.vertical₁_paired_limit
local notation "B₀₀" => kernel.reverseBound₀₀
local notation "hB₀₀" => kernel.reverseBound₀₀_nonneg
local notation "hReverse₀₀" => kernel.reverseBound₀₀_estimate
local notation "B₁₀" => kernel.reverseBound₁₀
local notation "hB₁₀" => kernel.reverseBound₁₀_nonneg
local notation "hReverse₁₀" => kernel.reverseBound₁₀_estimate
local notation "B₀₁" => kernel.reverseBound₀₁
local notation "hB₀₁" => kernel.reverseBound₀₁_nonneg
local notation "hReverse₀₁" => kernel.reverseBound₀₁_estimate
local notation "B₁₁" => kernel.reverseBound₁₁
local notation "hB₁₁" => kernel.reverseBound₁₁_nonneg
local notation "hReverse₁₁" => kernel.reverseBound₁₁_estimate

set_option quotPrecheck false in
local notation "sphereContext%[" t "]" =>
  (letI : IsSmoothPositiveMeasure (n := r) ν := s.fiberMeasure_smooth
   letI : IsFiniteMeasure ν := isFiniteMeasure_of_smoothPositiveMeasure (n := r) ν
   letI : TopologicalSpace (TotalSpace Unit (E).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
   letI : TopologicalSpace (TotalSpace Unit (E').Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
   letI : TopologicalSpace (TotalSpace Unit (F).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
   letI : TopologicalSpace (TotalSpace Unit (F').Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
   letI : IsFiniteRank (E).Fiber :=
     isFiniteRank_model (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber
   letI : IsFiniteRank (E').Fiber :=
     isFiniteRank_model (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber
   letI : IsFiniteRank (F).Fiber :=
     isFiniteRank_model (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber
   letI : IsFiniteRank (F').Fiber :=
     isFiniteRank_model (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber
   letI : ∀ x : B, FiniteDimensional ℂ ((E).Fiber x) :=
     fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber x
   letI : ∀ x : B, FiniteDimensional ℂ ((E').Fiber x) :=
     fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber x
   letI : ∀ x : Y, FiniteDimensional ℂ ((F).Fiber x) :=
     fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F).rank)) (F).Fiber x
   letI : ∀ x : Y, FiniteDimensional ℂ ((F').Fiber x) :=
     fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (F').rank)) (F').Fiber x
   letI : TopologicalSpace (TotalSpace Unit T) :=
     tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D)
   letI : TopologicalSpace (TotalSpace Unit U) :=
     tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D)
   letI : TopologicalSpace (TotalSpace Unit T') :=
     tensorTopology («E» := (πS : Z → B) *ᵖ (E).Fiber) («F» := D')
   letI : TopologicalSpace (TotalSpace Unit U') :=
     tensorTopology («E» := (πS : Z → B) *ᵖ (E').Fiber) («F» := D')
   letI : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
   letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
   letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
   letI : ChartedSpace Enr Z :=
     linearModelChartedSpace (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
   letI : IsManifold (𝓡 (n + r)) ∞ Z :=
     isManifold_linearModelChartedSpace
       (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
   letI : IsSmoothPositiveMeasure (n := n + r) η :=
     isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
   letI : TopologicalSpace (TotalSpace Unit (N₀₀).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (N₀₀).rank)) (N₀₀).Fiber
   letI : TopologicalSpace (TotalSpace Unit (N₁₀).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (N₁₀).rank)) (N₁₀).Fiber
   letI : TopologicalSpace (TotalSpace Unit (N₀₁).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (N₀₁).rank)) (N₀₁).Fiber
   letI : TopologicalSpace (TotalSpace Unit (N₁₁).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (N₁₁).rank)) (N₁₁).Fiber
   letI : ∀ z : Z, FiniteDimensional ℂ ((E).Fiber (πS z)) :=
     fun z ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E).rank)) (E).Fiber (πS z)
   letI : ∀ z : Z, FiniteDimensional ℂ ((E').Fiber (πS z)) :=
     fun z ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin (E').rank)) (E').Fiber (πS z)
   letI : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ
   letI : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'
   letI : ∀ z : Z, FiniteDimensional ℂ (D z) :=
     fun z ↦ finite_fiber («E» := D) z
   letI : ∀ z : Z, FiniteDimensional ℂ (D' z) :=
     fun z ↦ finite_fiber («E» := D') z
   letI : TopologicalSpace (TotalSpace Unit (Nplus).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (Nplus).rank)) (Nplus).Fiber
   letI : TopologicalSpace (TotalSpace Unit (Nminus).Fiber) :=
     modelTopology (EuclideanSpace ℂ (Fin (Nminus).rank)) (Nminus).Fiber
   t)

include kernel

set_option maxHeartbeats 80000000 in
-- The extended limit accommodates the dependent small-parameter cutoff and kernel-index comparison.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the dependent small-parameter cutoff and kernel-index comparison.
/-- Under the supplied small-parameter ellipticity bound, choose a cutoff whose
coordinate index is the difference of the original Green kernel dimensions. -/
theorem AssociatedSphereKernelWitness.exists_small_parameter_kernel_index :
    sphereContext%[∀ (δ : ℝ) (_hδ : 0 < δ)
      (_hElliptic : ∀ ε : Eps, ε.val ≤ δ → (KFamily ε).IsElliptic),
    ∃ ε : Eps, ε.val ≤ δ ∧
      ((KFamily ε).sobolevCoordinateRealization
        Dplus Dminus PhiPlus PsiMinus).index =
          (Module.finrank ℂ (L).ker : ℤ) - Module.finrank ℂ (La).ker] := by
  as_aux_lemma =>
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
    intro δ hδ hElliptic
    -- Recover only the smooth identities for the two fixed horizontal realizations.
    -- The same provider and choose paths define the shared realization selectors.
    have hHorizontal₀ :=
      (C).exists_horizontalLift_native_regularization S (E).Fiber A σ (E').Fiber hA JH
        Li Lo η N₀₀ N₁₀ e₀₀ e₁₀ he₀₀ hi₀₀ he₁₀ hi₁₀
    have hHorizontal₁ :=
      (C).exists_horizontalLift_native_regularization S (E).Fiber A' σ' (E').Fiber hA' JH'
        Li₁ Lo₁ η N₀₁ N₁₁ e₀₁ e₁₁ he₀₁ hi₀₁ he₁₁ hi₁₁
    have hRH₀ : ∀ w : (A₀₀).smoothSections,
        (RH₀) ((Li).smoothToSobolev 1 w) = (Lo).smoothToSobolev 0 (H₀ w) :=
      hHorizontal₀.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
    have hRH₁ : ∀ w : (A₀₁).smoothSections,
        (RH₁) ((Li₁).smoothToSobolev 1 w) = (Lo₁).smoothToSobolev 0 (H₁ w) :=
      hHorizontal₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
    -- These are the original coordinate realizations of K and its literal metric adjoint.
    let XE := WithLp 2 ((Li).SobolevSpace 1 × (Lo₁).SobolevSpace 1)
    let XO := WithLp 2 ((Lo).SobolevSpace 1 × (Li₁).SobolevSpace 1)
    let Ts (ε : Eps) : XE →L[ℂ] Odd :=
      (KFamily ε).sobolevCoordinateRealization Dplus Dminus PhiPlus PsiMinus
    let Ss (ε : Eps) : XO →L[ℂ] Even :=
      ((KFamily ε).metricFormalAdjoint kPlus kMinus).sobolevCoordinateRealization
        Dminus Dplus PhiMinus PsiPlus
    have hepsSeq : Tendsto (fun m ↦ (epsSeq m).val) atTop (𝓝 0) :=
      associatedSphereCutoffSequence_tendsto
    -- Read the closed graphs and kernel properties from one Green certificate.
    have hGradedSpec := g.graded_spec
    -- Retain the two closed operators and their original smooth graph closures.
    have hLclosed := And.left hGradedSpec
    have hLaclosed := And.left (hGradedSpec.2)
    have hLgraph := And.left (hGradedSpec.2.2)
    have hLagraph := And.left (hGradedSpec.2.2.2)
    -- Retain the formal adjunction and both smooth crossing identities.
    have hformal := And.left (hGradedSpec.2.2.2.2)
    have hcrossSmooth := And.left (hGradedSpec.2.2.2.2.2)
    have hcrossOddSmooth := And.left (hGradedSpec.2.2.2.2.2.2)
    -- Retain the closed ranges and finite kernels on the same graded pair.
    have hLrange := And.left (hGradedSpec.2.2.2.2.2.2.2)
    have hLfinite := And.left (hGradedSpec.2.2.2.2.2.2.2.2)
    have hLarange := And.left (hGradedSpec.2.2.2.2.2.2.2.2.2)
    have hLafinite := And.left (hGradedSpec.2.2.2.2.2.2.2.2.2.2)
    clear hGradedSpec
    -- The parameter sequence eventually lies below the supplied positive threshold δ.
    have hsmall : ∀ᶠ m in atTop, (epsSeq m).val ≤ δ :=
      (hepsSeq.eventually (eventually_lt_nhds hδ)).mono fun _ hm ↦ hm.le
    -- All four supplied coordinates concern the actual K and its literal metric adjoint.
    have hpaired : ∀ᶠ m in atTop,
        ((Ts (epsSeq m)).IsFredholm ∧ (Ss (epsSeq m)).IsFredholm) ∧
          (Ts (epsSeq m)).index + (Ss (epsSeq m)).index = 0 := by
      filter_upwards [hsmall] with m hm
      let P := KFamily (epsSeq m)
      have hcoords := P.isFredholm_and_index_eq_of_sobolev_coordinates_with_metricFormalAdjoint
        Dplus Dminus kPlus kMinus (hElliptic (epsSeq m) hm)
        PhiPlus PsiMinus PhiMinus PsiPlus
      exact ⟨⟨hcoords.1.1, hcoords.2.1.1⟩, hcoords.2.2⟩
    have hFredholm : ∀ᶠ m in atTop,
        (Ts (epsSeq m)).IsFredholm ∧ (Ss (epsSeq m)).IsFredholm :=
      hpaired.mono fun _ hm ↦ hm.1
    have hindex : ∀ᶠ m in atTop,
        (Ts (epsSeq m)).index + (Ss (epsSeq m)).index = 0 :=
      hpaired.mono fun _ hm ↦ hm.2
    -- Apply the existing corner-index theorem to the fixed objects and local smooth certificates.
    have hEq3 : ∃ m : ℕ, (epsSeq m).val ≤ δ ∧
        (Ts (epsSeq m)).index =
          (Module.finrank ℂ (L).ker : ℤ) - Module.finrank ℂ (La).ker := by
      exact exists_parameter_index_eq_of_native_corner_approximation
        A₀₀ Li i₀₀ Θ₀₀ hΘ₀₀ A₁₀ Lo i₁₀ Θ₁₀ hΘ₁₀
        A₀₁ Li₁ i₀₁ Θ₀₁ hΘ₀₁ A₁₁ Lo₁ i₁₁ Θ₁₁ hΘ₁₁
        H₀ RH₀ hRH₀ V₀ RV₀ hRV₀ V₁a RV₁a hRV₁a H₁a RH₁a hRH₁a
        H₀a RH₀a hRH₀a V₁ RV₁ hRV₁ V₀a RV₀a hRV₀a H₁ RH₁ hRH₁
        B₀₀ hB₀₀ hReverse₀₀
        B₁₁ hB₁₁ (fun w ↦ (hReverse₁₁ w).trans_eq
          (congrArg (fun t : ℝ ↦ B₁₁ * t) (add_right_comm _ _ _)))
        B₁₀ hB₁₀ hReverse₁₀
        B₀₁ hB₀₁ (fun w ↦ (hReverse₀₁ w).trans_eq
          (congrArg (fun t : ℝ ↦ B₀₁ * t) (add_right_comm _ _ _)))
        hcrossSmooth hcrossOddSmooth
        S₀₀ S₁₀ S₀₁ S₁₁
        ((k₀₀).smoothToL2 η) ((k₁₀).smoothToL2 η)
        ((k₀₁).smoothToL2 η) ((k₁₁).smoothToL2 η)
        (Φplus).toLinearMap (Φminus).toLinearMap
        ((Dplus).smoothToSobolev 1) ((Dminus).smoothToSobolev 1)
        ((Dplus).smoothToSobolev 0) ((Dminus).smoothToSobolev 0)
        PhiPlus PhiMinus PsiPlus PsiMinus
        (fun m ↦ (KFamily (epsSeq m)).toLinearMap)
        (fun m ↦ ((KFamily (epsSeq m)).metricFormalAdjoint kPlus kMinus).toLinearMap)
        (fun m ↦ (KFamily (epsSeq m)).sobolevRealization Dplus Dminus 1 0 (by norm_num))
        (fun m ↦ ((KFamily (epsSeq m)).metricFormalAdjoint kPlus kMinus).sobolevRealization
          Dminus Dplus 1 0 (by norm_num))
        (fun m ↦ (nativeU₀ (epsSeq m)).toLinearMap)
        (fun m ↦ ((nativeU₀ (epsSeq m)).metricFormalAdjoint k₀₀ k₁₀).toLinearMap)
        (fun m ↦ (nativeU₁ (epsSeq m)).toLinearMap)
        (fun m ↦ ((nativeU₁ (epsSeq m)).metricFormalAdjoint k₀₁ k₁₁).toLinearMap)
        (fun m ↦ (nativeV₀ (epsSeq m)).toLinearMap)
        (fun m ↦ ((nativeV₀ (epsSeq m)).metricFormalAdjoint k₀₀ k₀₁).toLinearMap)
        (fun m ↦ (nativeV₁ (epsSeq m)).toLinearMap)
        (fun m ↦ ((nativeV₁ (epsSeq m)).metricFormalAdjoint k₁₀ k₁₁).toLinearMap)
        WR₀ WR₁ hLimitH₀Data hLimitH₁Data hLimitV₀Data hLimitV₁Data
        hPhiPlus hPhiMinus hPsiPlus hPsiMinus
        (fun m s ↦ (KFamily (epsSeq m)).sobolevRealization_smoothToSobolev
          Dplus Dminus 1 0 (by norm_num) s)
        (fun m s ↦ by
          let Pa := (KFamily (epsSeq m)).metricFormalAdjoint kPlus kMinus
          exact Pa.sobolevRealization_smoothToSobolev Dminus Dplus 1 0 (by norm_num) s)
        (fun m ↦ hKmodel (epsSeq m)) (fun m ↦ hKadjmodel (epsSeq m))
        L La hLclosed hLaclosed hLgraph hLagraph hformal
        hLrange hLarange hLfinite hLafinite hFredholm hindex
        (fun m ↦ (epsSeq m).val ≤ δ) hsmall
    obtain ⟨m, hm, hKernel⟩ := hEq3
    exact ⟨epsSeq m, hm, hKernel⟩

end KernelParameter

end AtiyahSinger
