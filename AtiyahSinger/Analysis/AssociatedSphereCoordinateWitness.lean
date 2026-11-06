/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereCutoffWitness

/-!
# The two forward coordinates for the associated-sphere index comparison

Public module ID: M0111.

This producer preserves the four fixed Green domains and the already selected native
sums. It returns the positive order-one and negative order-zero coordinates with their
smooth-core identities. Its temporary corner completions remain local. The second
index equality itself is proved in `AssociatedSphereIndexEqualities`.
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
/-- Implementation data for two specified coordinate maps and their smooth identities.
The geometric spaces and smooth maps enter only when this record is specialized. -/
structure AssociatedSphereCoordinateData
    {E₁ : Type*} {F₁ : Type*} {E₀ : Type*} {F₀ : Type*}
    [TopologicalSpace E₁] [AddCommMonoid E₁] [Module ℂ E₁]
    [TopologicalSpace F₁] [AddCommMonoid F₁] [Module ℂ F₁]
    [TopologicalSpace E₀] [AddCommMonoid E₀] [Module ℂ E₀]
    [TopologicalSpace F₀] [AddCommMonoid F₀] [Module ℂ F₀]
    {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
    (smoothPlus : α → β → E₁) (coordinatePlus : α → β → F₁)
    (smoothMinus : γ → δ → E₀) (coordinateMinus : γ → δ → F₀) where
  /-- Forward coordinates for the specified positive source. -/
  phiPlus : E₁ ≃L[ℂ] F₁
  /-- Forward coordinates for the specified negative source. -/
  psiMinus : E₀ ≃L[ℂ] F₀
  /-- The positive coordinate has the specified smooth value. -/
  phiPlus_smooth : ∀ (a : α) (w : β), phiPlus (smoothPlus a w) = coordinatePlus a w
  /-- The negative coordinate has the specified smooth value. -/
  psiMinus_smooth : ∀ (a : γ) (w : δ), psiMinus (smoothMinus a w) = coordinateMinus a w

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

/- The notation quotation precheck lacks handlers for projections and letI in this Lean
version. Only those notation declarations bypass it; elaboration and kernel checking remain. -/
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

section CoordinateWitnessTypes

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

set_option maxHeartbeats 400000 in
-- The extended limit accommodates the dependent coordinate witnesses over the fixed native Green
-- sums.
/-- The two forward coordinates needed for the second index equality.
The smooth identities also allow the third equality to use these exact maps. -/
abbrev AssociatedSphereCoordinateWitness : Type _ :=
  sphereContext%[AssociatedSphereCoordinateData
    (E₁ := (Dplus).SobolevSpace 1)
    (F₁ := WithLp 2 ((Li).SobolevSpace 1 × (Lo₁).SobolevSpace 1))
    (E₀ := (Dminus).SobolevSpace 0) (F₀ := Odd)
    (fun (a : (A₀₀).smoothSections) (w : (A₁₁).smoothSections) ↦
      (Dplus).smoothToSobolev 1 (Φplus (S₀₀ a, S₁₁ w)))
    (fun (a : (A₀₀).smoothSections) (w : (A₁₁).smoothSections) ↦
      WithLp.toLp 2 ((Li).smoothToSobolev 1 a, (Lo₁).smoothToSobolev 1 w))
    (fun (a : (A₁₀).smoothSections) (w : (A₀₁).smoothSections) ↦
      (Dminus).smoothToSobolev 0 (Φminus (S₁₀ a, S₀₁ w)))
    (fun (a : (A₁₀).smoothSections) (w : (A₀₁).smoothSections) ↦
      WithLp.toLp 2 (i₁₀ a, i₀₁ w))]

end CoordinateWitnessTypes

set_option maxHeartbeats 80000000 in
-- The extended limit accommodates the dependent coordinate witnesses over the fixed native Green
-- sums.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the dependent coordinate witnesses over the fixed native Green
-- sums.
/-- Construct the minimal coordinate witnesses over the fixed Green models and native sums. -/
theorem nonempty_associatedSphereCoordinateWitness :
    Nonempty (AssociatedSphereCoordinateWitness s g sums) := by
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
  -- Construct the positive Sobolev coordinate from the prescribed native sum.
  obtain ⟨PhiPlus, hPhiPlus⟩ := exists_sobolevEquiv_of_atlas_native_sum (μ := η)
    A₀₀ Li A₁₁ Lo₁ N₀₀ N₁₁ Nplus (DD 0) (DD 1) Dplus 1
    e₀₀ he₀₀ hi₀₀ e₁₁ he₁₁ hi₁₁ (ePlus).linearEquiv hPlus₀ hPlus₁
  -- Complete the two fixed odd inclusions before constructing their native sum coordinate.
  obtain ⟨Θ₁₀, hΘ₁₀, _hJ₁₀inj, _hJ₁₀⟩ := (A₁₀).exists_sobolevZero_equiv_nativeL2
    Lo l₁₀ hl₁₀ N₁₀ k₁₀ η e₁₀ he₁₀ hi₁₀ hk₁₀
  obtain ⟨Θ₀₁, hΘ₀₁, _hJ₀₁inj, _hJ₀₁⟩ := (A₀₁).exists_sobolevZero_equiv_nativeL2
    Li₁ l₀₁ hl₀₁ N₀₁ k₀₁ η e₀₁ he₀₁ hi₀₁ hk₀₁
  obtain ⟨_PhiMinus, PsiMinus, _hPhiMinus, hPsiMinus⟩ :=
    exists_sobolev_and_nativeL2_coordinates_of_atlas_native_sum (μ := η)
      A₁₀ Lo A₀₁ Li₁ N₁₀ N₀₁ Nminus (HH 0) (HH 1) Dminus
      Θ₁₀ Θ₀₁ i₁₀ i₀₁ hΘ₁₀ hΘ₀₁
      e₁₀ he₁₀ hi₁₀ e₀₁ he₀₁ hi₀₁ (eMinus).linearEquiv hMinus₀ hMinus₁
  -- Only the maps consumed by the second equality leave this construction.
  exact ⟨{
    phiPlus := PhiPlus
    psiMinus := PsiMinus
    phiPlus_smooth := hPhiPlus
    psiMinus_smooth := hPsiMinus }⟩

/-- The selected coordinate witnesses retain the prescribed common data. -/
def associatedSphereCoordinateWitness : AssociatedSphereCoordinateWitness s g sums :=
  Classical.choice (nonempty_associatedSphereCoordinateWitness s g sums)

end AtiyahSinger
