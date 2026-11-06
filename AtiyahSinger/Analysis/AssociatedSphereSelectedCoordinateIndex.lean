/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereCoefficientWitness
public import AtiyahSinger.Analysis.AssociatedSphereKernelParameter

/-!
# The selected cutoff index in its Sobolev coordinates

Public module ID: M0128.

This integer is the index of the designated cutoff in the specified order-one
source and order-zero target coordinates. The seed, Green selection, native
sums and parameter are shared with the original cutoff and kernel comparisons.
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

section SelectedEqualities

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
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Enr" => EuclideanSpace ℝ (Fin (n + r))
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "πS" => associatedBundleProjection («F» := Y) S.toIsPrincipalBundle

variable (hn : 0 < n) (hr : 0 < r)
  (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := B)))
  (v : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
    (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))

-- Each producer uses the fixed seed, Green models and native-object selectors.
local notation "s" => associatedSpherePositiveSeed S μ hn hr u v
local notation "g" => associatedSphereGreenSelection s
local notation "sums" => associatedSphereNativeSums s g
local notation "coordinates" => associatedSphereCoordinateWitness s g sums
local notation "kernel" => associatedSphereKernelWitness s g sums

set_option quotPrecheck false in
local notation "E" => (s).baseSource
set_option quotPrecheck false in
local notation "E'" => (s).baseTarget
set_option quotPrecheck false in
local notation "F" => (s).fiberSource
set_option quotPrecheck false in
local notation "F'" => (s).fiberTarget
set_option quotPrecheck false in
local notation "σ" => (s).fiberAction
set_option quotPrecheck false in
local notation "σ'" => (s).fiberTargetAction
set_option quotPrecheck false in
local notation "h" => (s).baseSourceMetric
set_option quotPrecheck false in
local notation "h'" => (s).baseTargetMetric
set_option quotPrecheck false in
local notation "k" => (s).fiberSourceMetric
set_option quotPrecheck false in
local notation "k'" => (s).fiberTargetMetric
set_option quotPrecheck false in
local notation "ν" => (s).fiberMeasure
set_option quotPrecheck false in
local notation "C" => (s).localization
set_option quotPrecheck false in
local notation "Q" => (s).fiberOperator
set_option quotPrecheck false in
local notation "hσ" => (s).fiberAction_smooth
set_option quotPrecheck false in
local notation "hσ'" => (s).fiberTargetAction_smooth
set_option quotPrecheck false in
local notation "hQ" => (s).fiberOperator_equivariant
set_option quotPrecheck false in
local notation "hQell" => (s).fiberOperator_elliptic

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
   associatedProductMeasure S.toIsPrincipalBundle μ ν (s).fiberMeasure_invariant)

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

set_option quotPrecheck false in
local notation "L₀" => (s).sphereSourcePresentation
set_option quotPrecheck false in
local notation "L₁" => (s).sphereTargetPresentation
set_option quotPrecheck false in
local notation "JH" => (L₀).toAtlasBundlePresentation
set_option quotPrecheck false in
local notation "JH'" => (L₁).toAtlasBundlePresentation
set_option quotPrecheck false in
local notation "JV" => (s).baseSourcePresentation
set_option quotPrecheck false in
local notation "JV'" => (s).baseTargetPresentation
set_option quotPrecheck false in
local notation "b" => (s).basePartitionCenter
set_option quotPrecheck false in
local notation "hJV" => (s).basePartition_subordinate
set_option quotPrecheck false in
local notation "hQA" => (g).fiberAtlasOperator_equivariant
set_option quotPrecheck false in
local notation "qa" => nativeAtlasGlobalSymbol 1 (s).fiberFullSymbol
local notation "Eps" => {ε : ℝ // 0 < ε ∧ ε ≤ 1}
set_option quotPrecheck false in
local notation "pfFamily" => (C).horizontalCutoffFactor S (E).Fiber A (E').Fiber JH

set_option quotPrecheck false in
local notation "N₀₀" => (g).native₀₀
set_option quotPrecheck false in
local notation "k₀₀" => (g).nativeMetric₀₀
set_option quotPrecheck false in
local notation "l₀₀" => (g).atlasMetric₀₀
set_option quotPrecheck false in
local notation "e₀₀" => (g).nativeIso₀₀
set_option quotPrecheck false in
local notation "he₀₀" => (g).nativeIso₀₀_smooth
set_option quotPrecheck false in
local notation "hi₀₀" => (g).nativeIso₀₀_symm_smooth
set_option quotPrecheck false in
local notation "hk₀₀" => (g).nativeIso₀₀_isometry
set_option quotPrecheck false in
local notation "hl₀₀" => (g).atlasMetric₀₀_smooth
set_option quotPrecheck false in
local notation "S₀₀" => (atlasSmoothSectionEquiv A₀₀
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₀₀).rank) (N₀₀).Fiber)
  e₀₀ he₀₀ hi₀₀).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₀₀).rank) (N₀₀).Fiber)

set_option quotPrecheck false in
local notation "N₁₀" => (g).native₁₀
set_option quotPrecheck false in
local notation "k₁₀" => (g).nativeMetric₁₀
set_option quotPrecheck false in
local notation "l₁₀" => (g).atlasMetric₁₀
set_option quotPrecheck false in
local notation "e₁₀" => (g).nativeIso₁₀
set_option quotPrecheck false in
local notation "he₁₀" => (g).nativeIso₁₀_smooth
set_option quotPrecheck false in
local notation "hi₁₀" => (g).nativeIso₁₀_symm_smooth
set_option quotPrecheck false in
local notation "hk₁₀" => (g).nativeIso₁₀_isometry
set_option quotPrecheck false in
local notation "hl₁₀" => (g).atlasMetric₁₀_smooth
set_option quotPrecheck false in
local notation "S₁₀" => (atlasSmoothSectionEquiv A₁₀
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₁₀).rank) (N₁₀).Fiber)
  e₁₀ he₁₀ hi₁₀).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₁₀).rank) (N₁₀).Fiber)

set_option quotPrecheck false in
local notation "N₀₁" => (g).native₀₁
set_option quotPrecheck false in
local notation "k₀₁" => (g).nativeMetric₀₁
set_option quotPrecheck false in
local notation "l₀₁" => (g).atlasMetric₀₁
set_option quotPrecheck false in
local notation "e₀₁" => (g).nativeIso₀₁
set_option quotPrecheck false in
local notation "he₀₁" => (g).nativeIso₀₁_smooth
set_option quotPrecheck false in
local notation "hi₀₁" => (g).nativeIso₀₁_symm_smooth
set_option quotPrecheck false in
local notation "hk₀₁" => (g).nativeIso₀₁_isometry
set_option quotPrecheck false in
local notation "hl₀₁" => (g).atlasMetric₀₁_smooth
set_option quotPrecheck false in
local notation "S₀₁" => (atlasSmoothSectionEquiv A₀₁
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₀₁).rank) (N₀₁).Fiber)
  e₀₁ he₀₁ hi₀₁).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₀₁).rank) (N₀₁).Fiber)

set_option quotPrecheck false in
local notation "N₁₁" => (g).native₁₁
set_option quotPrecheck false in
local notation "k₁₁" => (g).nativeMetric₁₁
set_option quotPrecheck false in
local notation "l₁₁" => (g).atlasMetric₁₁
set_option quotPrecheck false in
local notation "e₁₁" => (g).nativeIso₁₁
set_option quotPrecheck false in
local notation "he₁₁" => (g).nativeIso₁₁_smooth
set_option quotPrecheck false in
local notation "hi₁₁" => (g).nativeIso₁₁_symm_smooth
set_option quotPrecheck false in
local notation "hk₁₁" => (g).nativeIso₁₁_isometry
set_option quotPrecheck false in
local notation "hl₁₁" => (g).atlasMetric₁₁_smooth
set_option quotPrecheck false in
local notation "S₁₁" => (atlasSmoothSectionEquiv A₁₁
  (nativeSmoothComplexBundleAtlas (n := n + r) (r := (N₁₁).rank) (N₁₁).Fiber)
  e₁₁ he₁₁ hi₁₁).trans
    (nativeSmoothSectionLinearEquiv (n := n + r) (r := (N₁₁).rank) (N₁₁).Fiber)

set_option quotPrecheck false in
local notation "Li" => (g).presentation₀₀
set_option quotPrecheck false in
local notation "Lo" => (g).presentation₁₀
set_option quotPrecheck false in
local notation "Li₁" => (g).presentation₀₁
set_option quotPrecheck false in
local notation "Lo₁" => (g).presentation₁₁
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

set_option quotPrecheck false in
local notation "qfull" => (s).fiberFullSymbol
set_option quotPrecheck false in
local notation "hqfixed" => (s).fiberFullSymbol_invariant
set_option quotPrecheck false in
local notation "hqfull" => (s).fiberFullSymbol_elliptic
set_option quotPrecheck false in
local notation "hQpr" => (s).fiberOperator_principal
set_option quotPrecheck false in
local notation "hk" => (s).fiberSourceMetric_invariant
set_option quotPrecheck false in
local notation "hk'" => (s).fiberTargetMetric_invariant
set_option quotPrecheck false in
local notation "hνinv" => (s).fiberMeasure_invariant
set_option quotPrecheck false in
local notation "hCell" => (s).localization_elliptic
set_option quotPrecheck false in
local notation "hJA" => (g).fiberAtlasAdjoint_equivariant
set_option quotPrecheck false in
local notation "hJV'" => (s).basePartition_subordinate
local notation "split" => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
set_option quotPrecheck false in
local notation "L" => (g).graded
set_option quotPrecheck false in
local notation "La" => (g).gradedAdjoint
set_option quotPrecheck false in
local notation "Even" => (g).Even
set_option quotPrecheck false in
local notation "Odd" => (g).Odd
set_option quotPrecheck false in
local notation "β₀" => (g).baseAdjointCutoff₀
set_option quotPrecheck false in
local notation "hβ₀" => (g).baseAdjointCutoff₀_smooth
set_option quotPrecheck false in
local notation "hsβ₀" => (g).baseAdjointCutoff₀_support
set_option quotPrecheck false in
local notation "hβ₀one" => (g).baseAdjointCutoff₀_one
set_option quotPrecheck false in
local notation "H₀'" => (g).horizontalPieceAdjoint₀
set_option quotPrecheck false in
local notation "hH₀formula" => (g).horizontalPieceAdjoint₀_formula
set_option quotPrecheck false in
local notation "H₀a" => (g).horizontalAdjoint₀
set_option quotPrecheck false in
local notation "hH₀sum" => (g).horizontalAdjoint₀_sum
set_option quotPrecheck false in
local notation "hH₀" => (g).horizontal₀_adjoint
set_option quotPrecheck false in
local notation "hV₀" => (g).vertical₀_adjoint
set_option quotPrecheck false in
local notation "V₀a" => (g).verticalAdjoint₀
set_option quotPrecheck false in
local notation "β₁" => (g).baseAdjointCutoff₁
set_option quotPrecheck false in
local notation "hβ₁" => (g).baseAdjointCutoff₁_smooth
set_option quotPrecheck false in
local notation "hsβ₁" => (g).baseAdjointCutoff₁_support
set_option quotPrecheck false in
local notation "hβ₁one" => (g).baseAdjointCutoff₁_one
set_option quotPrecheck false in
local notation "H₁'" => (g).horizontalPieceAdjoint₁
set_option quotPrecheck false in
local notation "hH₁formula" => (g).horizontalPieceAdjoint₁_formula
set_option quotPrecheck false in
local notation "H₁a" => (g).horizontalAdjoint₁
set_option quotPrecheck false in
local notation "hH₁sum" => (g).horizontalAdjoint₁_sum
set_option quotPrecheck false in
local notation "hH₁" => (g).horizontal₁_adjoint
set_option quotPrecheck false in
local notation "hV₁" => (g).vertical₁_adjoint
set_option quotPrecheck false in
local notation "V₁a" => (g).verticalAdjoint₁
set_option quotPrecheck false in
local notation "i₀₀" => (g).inclusion₀₀
set_option quotPrecheck false in
local notation "hkPure₀₀" => (g).nativeIso₀₀_pairing_tmul
set_option quotPrecheck false in
local notation "i₁₀" => (g).inclusion₁₀
set_option quotPrecheck false in
local notation "hkPure₁₀" => (g).nativeIso₁₀_pairing_tmul
set_option quotPrecheck false in
local notation "i₀₁" => (g).inclusion₀₁
set_option quotPrecheck false in
local notation "hkPure₀₁" => (g).nativeIso₀₁_pairing_tmul
set_option quotPrecheck false in
local notation "i₁₁" => (g).inclusion₁₁
set_option quotPrecheck false in
local notation "hkPure₁₁" => (g).nativeIso₁₁_pairing_tmul
set_option quotPrecheck false in
local notation "Rq" => associatedSphereFiberQuantization s
set_option quotPrecheck false in
local notation "nativeU₀" => associatedSphereHorizontalFamily₀ s g
set_option quotPrecheck false in
local notation "RH₀" => associatedSphereHorizontalRealization₀ s g
set_option quotPrecheck false in
local notation "nativeU₁" => associatedSphereHorizontalFamily₁ s g
set_option quotPrecheck false in
local notation "RH₁" => associatedSphereHorizontalRealization₁ s g
set_option quotPrecheck false in
local notation "nativeV₀" => associatedSphereVerticalFamily₀ s g
set_option quotPrecheck false in
local notation "WR₀" => associatedSphereVerticalResidualRealization₀ s g
set_option quotPrecheck false in
local notation "nativeV₁" => associatedSphereVerticalFamily₁ s g
set_option quotPrecheck false in
local notation "WR₁" => associatedSphereVerticalResidualRealization₁ s g
set_option quotPrecheck false in
local notation "Nplus" => (sums).nativePlus
set_option quotPrecheck false in
local notation "Nminus" => (sums).nativeMinus
set_option quotPrecheck false in
local notation "ePlus" => (sums).sumPlus
set_option quotPrecheck false in
local notation "eMinus" => (sums).sumMinus
set_option quotPrecheck false in
local notation "hPlus₀" => (sums).plus₀_smooth
set_option quotPrecheck false in
local notation "hPlus₁" => (sums).plus₁_smooth
set_option quotPrecheck false in
local notation "hMinus₀" => (sums).minus₀_smooth
set_option quotPrecheck false in
local notation "hMinus₁" => (sums).minus₁_smooth
set_option quotPrecheck false in
local notation "kPlus" => (sums).metricPlus
set_option quotPrecheck false in
local notation "kMinus" => (sums).metricMinus
set_option quotPrecheck false in
local notation "Dplus" => (sums).presentationPlus
set_option quotPrecheck false in
local notation "Dminus" => (sums).presentationMinus
set_option quotPrecheck false in
local notation "DD" => (sums).cornerPresentationsPlus
set_option quotPrecheck false in
local notation "HH" => (sums).cornerPresentationsMinus
set_option quotPrecheck false in
local notation "KFamily" => (sums).cutoffFamily
set_option quotPrecheck false in
local notation "hKmodel" => (sums).cutoff_blocks
set_option quotPrecheck false in
local notation "hKadjmodel" => (sums).adjoint_cutoff_blocks
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

set_option quotPrecheck false in
local notation "PhiPlus" => (coordinates).phiPlus
set_option quotPrecheck false in
local notation "PsiMinus" => (coordinates).psiMinus
set_option quotPrecheck false in
local notation "hPhiPlus" => (coordinates).phiPlus_smooth
set_option quotPrecheck false in
local notation "hPsiMinus" => (coordinates).psiMinus_smooth
set_option quotPrecheck false in
local notation "PhiMinus" => (kernel).phiMinus
set_option quotPrecheck false in
local notation "PsiPlus" => (kernel).psiPlus
set_option quotPrecheck false in
local notation "hPhiMinus" => (kernel).phiMinus_smooth
set_option quotPrecheck false in
local notation "hPsiPlus" => (kernel).psiPlus_smooth
set_option quotPrecheck false in
local notation "Θ₀₀" => (kernel).sobolevZero₀₀
set_option quotPrecheck false in
local notation "hΘ₀₀" => (kernel).sobolevZero₀₀_smooth
set_option quotPrecheck false in
local notation "Θ₁₀" => (kernel).sobolevZero₁₀
set_option quotPrecheck false in
local notation "hΘ₁₀" => (kernel).sobolevZero₁₀_smooth
set_option quotPrecheck false in
local notation "Θ₀₁" => (kernel).sobolevZero₀₁
set_option quotPrecheck false in
local notation "hΘ₀₁" => (kernel).sobolevZero₀₁_smooth
set_option quotPrecheck false in
local notation "Θ₁₁" => (kernel).sobolevZero₁₁
set_option quotPrecheck false in
local notation "hΘ₁₁" => (kernel).sobolevZero₁₁_smooth
set_option quotPrecheck false in
local notation "RV₀" => (kernel).verticalRealization₀
set_option quotPrecheck false in
local notation "hRV₀" => (kernel).verticalRealization₀_smooth
set_option quotPrecheck false in
local notation "RV₁" => (kernel).verticalRealization₁
set_option quotPrecheck false in
local notation "hRV₁" => (kernel).verticalRealization₁_smooth
set_option quotPrecheck false in
local notation "RH₀a" => (kernel).horizontalAdjointRealization₀
set_option quotPrecheck false in
local notation "hRH₀a" => (kernel).horizontalAdjointRealization₀_smooth
set_option quotPrecheck false in
local notation "RH₁a" => (kernel).horizontalAdjointRealization₁
set_option quotPrecheck false in
local notation "hRH₁a" => (kernel).horizontalAdjointRealization₁_smooth
set_option quotPrecheck false in
local notation "RV₀a" => (kernel).verticalAdjointRealization₀
set_option quotPrecheck false in
local notation "hRV₀a" => (kernel).verticalAdjointRealization₀_smooth
set_option quotPrecheck false in
local notation "RV₁a" => (kernel).verticalAdjointRealization₁
set_option quotPrecheck false in
local notation "hRV₁a" => (kernel).verticalAdjointRealization₁_smooth
set_option quotPrecheck false in
local notation "hLimitH₀Data" => (kernel).horizontal₀_paired_limit
set_option quotPrecheck false in
local notation "hLimitH₁Data" => (kernel).horizontal₁_paired_limit
set_option quotPrecheck false in
local notation "hLimitV₀Data" => (kernel).vertical₀_paired_limit
set_option quotPrecheck false in
local notation "hLimitV₁Data" => (kernel).vertical₁_paired_limit
set_option quotPrecheck false in
local notation "B₀₀" => (kernel).reverseBound₀₀
set_option quotPrecheck false in
local notation "hB₀₀" => (kernel).reverseBound₀₀_nonneg
set_option quotPrecheck false in
local notation "hReverse₀₀" => (kernel).reverseBound₀₀_estimate
set_option quotPrecheck false in
local notation "B₁₀" => (kernel).reverseBound₁₀
set_option quotPrecheck false in
local notation "hB₁₀" => (kernel).reverseBound₁₀_nonneg
set_option quotPrecheck false in
local notation "hReverse₁₀" => (kernel).reverseBound₁₀_estimate
set_option quotPrecheck false in
local notation "B₀₁" => (kernel).reverseBound₀₁
set_option quotPrecheck false in
local notation "hB₀₁" => (kernel).reverseBound₀₁_nonneg
set_option quotPrecheck false in
local notation "hReverse₀₁" => (kernel).reverseBound₀₁_estimate
set_option quotPrecheck false in
local notation "B₁₁" => (kernel).reverseBound₁₁
set_option quotPrecheck false in
local notation "hB₁₁" => (kernel).reverseBound₁₁_nonneg
set_option quotPrecheck false in
local notation "hReverse₁₁" => (kernel).reverseBound₁₁_estimate

local notation "chosenEps" =>
  associatedSphereKernelParameter s g sums coordinates kernel

-- The coefficient comparison uses only the Seed and Green selection.
set_option quotPrecheck false in
local notation "selectedGreenContext%[" t "]" =>
  (letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
   letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
   letI : CompactSpace Z := ⟨by
     have hcontrol : associatedControl G P Y Set.univ = Set.univ := by
       apply Set.eq_univ_of_forall
       intro z
       induction z using Quotient.inductionOn with
       | «h» w => exact ⟨w, ⟨Set.mem_univ w.1, Set.mem_univ w.2⟩, rfl⟩
     rw [← hcontrol]
     exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
       (fun _ _ ↦ Iff.rfl)⟩
   letI : T2Space Z := associatedBundle_t2Space («Y» := Y) S.toIsPrincipalBundle
   letI : SecondCountableTopology Z :=
     ChartedSpace.secondCountable_of_sigmaCompact (En × Er) Z
   letI : MeasurableSpace Z := borel Z
   letI : BorelSpace Z := ⟨rfl⟩
   letI : IsSmoothPositiveMeasure (n := r) ν := (s).fiberMeasure_smooth
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
     isSmoothPositiveMeasure_associatedProductMeasure S μ ν (s).fiberMeasure_invariant
   t)

set_option quotPrecheck false in
local notation "selectedContext%[" t "]" =>
  (letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
   letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
   letI : CompactSpace Z := ⟨by
     have hcontrol : associatedControl G P Y Set.univ = Set.univ := by
       apply Set.eq_univ_of_forall
       intro z
       induction z using Quotient.inductionOn with
       | «h» w => exact ⟨w, ⟨Set.mem_univ w.1, Set.mem_univ w.2⟩, rfl⟩
     rw [← hcontrol]
     exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
       (fun _ _ ↦ Iff.rfl)⟩
   letI : T2Space Z := associatedBundle_t2Space («Y» := Y) S.toIsPrincipalBundle
   letI : SecondCountableTopology Z :=
     ChartedSpace.secondCountable_of_sigmaCompact (En × Er) Z
   letI : MeasurableSpace Z := borel Z
   letI : BorelSpace Z := ⟨rfl⟩
   letI : IsSmoothPositiveMeasure (n := r) ν := (s).fiberMeasure_smooth
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
     isSmoothPositiveMeasure_associatedProductMeasure S μ ν (s).fiberMeasure_invariant
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

set_option maxHeartbeats 8000000 in
-- The extended limit accommodates elaboration of the shared dependent coordinate witness context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the shared dependent coordinate witness context.
/-- The index of the designated cutoff in its selected forward Sobolev coordinates. -/
def associatedSphereSelectedCoordinateIndex : ℤ := selectedContext%[
  -- Give the source coordinate space its standard product Sobolev norm.
  letI : NormedAddCommGroup (WithLp 2 ((Li).SobolevSpace 1 × (Lo₁).SobolevSpace 1)) :=
    WithLp.instProdNormedAddCommGroup 2 ((Li).SobolevSpace 1) ((Lo₁).SobolevSpace 1)
  letI : NormedSpace ℂ (WithLp 2 ((Li).SobolevSpace 1 × (Lo₁).SobolevSpace 1)) :=
    WithLp.instProdNormedSpace 2 ℂ ((Li).SobolevSpace 1) ((Lo₁).SobolevSpace 1)
  ((KFamily chosenEps).sobolevCoordinateRealization Dplus Dminus
    (X := WithLp 2 ((Li).SobolevSpace 1 × (Lo₁).SobolevSpace 1))
    («Y» := Odd) PhiPlus PsiMinus).index]

end SelectedEqualities

end AtiyahSinger
