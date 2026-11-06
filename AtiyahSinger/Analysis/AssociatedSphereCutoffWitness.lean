/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereIndexAuxiliary

/-!
# Cutoff witnesses for the associated-sphere comparison

Public module ID: M0114.

The named objects retain the four native approximation families and the
realizations shared with the kernel comparison. Each vertical selection keeps
its six witnesses and full certificate together; the family, realization,
common sums and kernel comparison read those same selected values. The seed
and Green selection are explicit arguments shared by all constructions.

The common cutoff bound comes from the universal geometric comparison used
in the index equality. This module gives its positivity, unit-interval bound
and ellipticity consequences. The index equalities are proved in
`AssociatedSphereIndexEqualities`.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AtiyahSinger

section SixChoice

universe u v w u₁ v₁ w₁

variable {α : Type u} {β : Type v} {γ : Type w}
  {δ : Type u₁} {ε : Type v₁} {ζ : Type w₁}
  {p : α → β → γ → δ → ε → ζ → Prop}

/-- Package six witness types and their predicate inferred from an existence proof.
An inhabitant is any tuple satisfying that predicate. `sixChoiceData h` selects
the designated tuple from the proof, in the original witness order. -/
abbrev SixChoiceData
    (_h : ∃ (a : α) (b : β) (c : γ) (d : δ) (e : ε) (f : ζ), p a b c d e f) :
    Type (max u v w u₁ v₁ w₁) :=
  {t : α × β × γ × δ × ε × ζ //
    p t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2}

/-- Package the original six choices directly, retaining their original order and predicate. -/
noncomputable def sixChoiceData
    (h : ∃ (a : α) (b : β) (c : γ) (d : δ) (e : ε) (f : ζ), p a b c d e f) :
    SixChoiceData h where
  val := (h.choose,
    h.choose_spec.choose,
    h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose)
  property := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end SixChoice

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

-- Only notation prechecking is scoped off; expanded terms retain normal elaboration.
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
local notation "sphereContext%[" t "]" =>
  (letI : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
   letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
   letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
   letI : ChartedSpace Enr Z := linearModelChartedSpace
     (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
   letI : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
     (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
   letI : IsSmoothPositiveMeasure (n := n + r) η :=
     isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
   t)

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
local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₀₀).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₀₀).rank)) (N₀₀).Fiber]
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
local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₁₀).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₁₀).rank)) (N₁₀).Fiber]
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
local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₀₁).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₀₁).rank)) (N₀₁).Fiber]
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
local instance : sphereContext%[TopologicalSpace (TotalSpace Unit (N₁₁).Fiber)] :=
  sphereContext%[modelTopology (EuclideanSpace ℂ (Fin (N₁₁).rank)) (N₁₁).Fiber]
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

/-! The cross-stage objects are fixed once; the remaining row certificates stay local. -/

/-- The one original fiber quantization used by both vertical rows and the cutoff threshold. -/
def associatedSphereFiberQuantization : AtlasQuantizationPresentation A A' := by
  exact Classical.choice (nonempty_atlasQuantizationPresentation A A')

local notation "Rq" => associatedSphereFiberQuantization s
set_option quotPrecheck false in
local notation "Lq" => fun j : Fin (Rq).size ↦ ((Rq).patch j).toPiece qa

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
omit [MeasurableSpace Z] [BorelSpace Z] in
omit [T2Space Z] [CompactSpace Z] [SecondCountableTopology Z] in
/-- The original quantization residual has its bounded sphere H⁰-to-H⁰ realization. -/
theorem exists_associatedSphereFiberResidualRealization :
    ∃ Rres : (L₀).toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
      (L₁).toAtlasBundlePresentation.SobolevSpace 0,
      ∀ w : (A).smoothSections,
        Rres ((L₀).toAtlasBundlePresentation.smoothToSobolev 0 w) =
          (L₁).toAtlasBundlePresentation.smoothToSobolev 0
            (((QA).toLinearMap - ∑ j, (Lq j).toLinearMap) w) := by
  classical
  -- The fixed original Rq family differs from QA by an actual order-zero PDO.
  have hQqa : (QA).principalSymbol = atlasGlobalPrincipalSymbolClass A A' 1 qa :=
    (Q).principalSymbol_toAtlasPseudodifferentialOperator
      s.fiberFullSymbol s.fiberOperator_principal
  have hresidualOrder : IsAtlasPseudodifferentialOperator A A' 0
      ((QA).toLinearMap - ((Rq).quantize qa).toLinearMap) := by
    have hpr : (QA).principalSymbol = ((Rq).quantize qa).principalSymbol :=
      hQqa.trans ((Rq).principalSymbol_quantize qa).symm
    simpa only [sub_self] using
      (AtlasPseudodifferentialOperator.principalSymbol_eq_iff A A' QA
        ((Rq).quantize qa)).mp hpr
  let Qres : AtlasPseudodifferentialOperator A A' 0 :=
    ⟨(QA).toLinearMap - ((Rq).quantize qa).toLinearMap, hresidualOrder⟩
  -- Normalize only the zero target order of this same Sobolev extension.
  have hR : ∃ Rres : (L₀).toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
      (L₁).toAtlasBundlePresentation.SobolevSpace (0 - 0),
      ∀ w : (A).smoothSections,
        Rres ((L₀).toAtlasBundlePresentation.smoothToSobolev 0 w) =
          (L₁).toAtlasBundlePresentation.smoothToSobolev (0 - 0)
            (((QA).toLinearMap - ∑ j, (Lq j).toLinearMap) w) :=
    (Qres.existsUnique_sobolevExtension (L₀).toAtlasBundlePresentation
      (L₁).toAtlasBundlePresentation 0).exists
  exact Eq.mp (congrArg (fun t : ℝ ↦
    ∃ Rres : (L₀).toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
      (L₁).toAtlasBundlePresentation.SobolevSpace t,
      ∀ w : (A).smoothSections,
        Rres ((L₀).toAtlasBundlePresentation.smoothToSobolev 0 w) =
          (L₁).toAtlasBundlePresentation.smoothToSobolev t
            (((QA).toLinearMap - ∑ j, (Lq j).toLinearMap) w)) (sub_self (0 : ℝ))) hR

/-- One sphere residual and its smooth identity, shared by both vertical provider calls. -/
def associatedSphereFiberResidualRealization :
    {Rres : (L₀).toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
      (L₁).toAtlasBundlePresentation.SobolevSpace 0 //
      ∀ w : (A).smoothSections,
        Rres ((L₀).toAtlasBundlePresentation.smoothToSobolev 0 w) =
          (L₁).toAtlasBundlePresentation.smoothToSobolev 0
            (((QA).toLinearMap - ∑ j, (Lq j).toLinearMap) w)} := by
  exact ⟨(exists_associatedSphereFiberResidualRealization s).choose,
    (exists_associatedSphereFiberResidualRealization s).choose_spec⟩

set_option quotPrecheck false in
local notation "Rres" => (associatedSphereFiberResidualRealization s).val
set_option quotPrecheck false in
local notation "hRres" => (associatedSphereFiberResidualRealization s).property

/- These are exactly the original provider applications. Consumers recover certificates
from their fixed choice paths; they never eliminate the whole existence statement again. -/
set_option quotPrecheck false in
local notation "horizontalRow₀" =>
  (C).exists_horizontalLift_native_regularization S (E).Fiber A σ (E').Fiber hA JH
    Li Lo η N₀₀ N₁₀ e₀₀ e₁₀ he₀₀ hi₀₀ he₁₀ hi₁₀
set_option quotPrecheck false in
local notation "horizontalRow₁" =>
  (C).exists_horizontalLift_native_regularization S (E).Fiber A' σ' (E').Fiber hA' JH'
    Li₁ Lo₁ η N₀₁ N₁₁ e₀₁ e₁₁ he₀₁ hi₀₁ he₁₁ hi₁₁
set_option quotPrecheck false in
local notation "verticalRow₀" =>
  exists_associatedSphereTensorVertical_native_approximation
    S (E).Fiber F F' σ σ' hσ hσ' k k' ν L₀ L₁ JV b hJV
    QA hQA (Rq).size Lq Rres hRres
    Li Li₁ l₀₀ hl₀₀ l₀₁ hl₀₁ N₀₀ N₀₁ k₀₀ k₀₁ η
    e₀₀ he₀₀ hi₀₀ e₀₁ he₀₁ hi₀₁ hk₀₀ hk₀₁
set_option quotPrecheck false in
local notation "verticalRow₁" =>
  exists_associatedSphereTensorVertical_native_approximation
    S (E').Fiber F F' σ σ' hσ hσ' k k' ν L₀ L₁ JV' b (fun j ↦ hJV j)
    QA hQA (Rq).size Lq Rres hRres
    Lo Lo₁ l₁₀ hl₁₀ l₁₁ hl₁₁ N₁₀ N₁₁ k₁₀ k₁₁ η
    e₁₀ he₁₀ hi₁₀ e₁₁ he₁₁ hi₁₁ hk₁₀ hk₁₁

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The designated horizontal native family in row ₀, over the fixed Green models. -/
def associatedSphereHorizontalFamily₀ : sphereContext%[
    Eps → PseudodifferentialOperator (n := n + r)
      (r := (N₀₀).rank) (q := (N₁₀).rank) (N₀₀).Fiber (N₁₀).Fiber η 1] := by
  exact sphereContext%[(horizontalRow₀).choose_spec.choose_spec.choose_spec.choose]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The full horizontal realization selected together with row ₀'s native family. -/
def associatedSphereHorizontalRealization₀ : sphereContext%[
    (Li).SobolevSpace 1 →L[ℂ] (Lo).SobolevSpace 0] := by
  exact sphereContext%[(horizontalRow₀).choose]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The designated horizontal native family in row ₁, over the fixed Green models. -/
def associatedSphereHorizontalFamily₁ : sphereContext%[
    Eps → PseudodifferentialOperator (n := n + r)
      (r := (N₀₁).rank) (q := (N₁₁).rank) (N₀₁).Fiber (N₁₁).Fiber η 1] := by
  exact sphereContext%[(horizontalRow₁).choose_spec.choose_spec.choose_spec.choose]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The full horizontal realization selected together with row ₁'s native family. -/
def associatedSphereHorizontalRealization₁ : sphereContext%[
    (Li₁).SobolevSpace 1 →L[ℂ] (Lo₁).SobolevSpace 0] := by
  exact sphereContext%[(horizontalRow₁).choose]

set_option maxHeartbeats 80000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The six original choices and their full certificate for vertical row ₀. -/
def associatedSphereVerticalSelection₀ : sphereContext%[SixChoiceData verticalRow₀] := by
  exact sphereContext%[sixChoiceData verticalRow₀]

set_option maxHeartbeats 80000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The six original choices and their full certificate for vertical row ₁. -/
def associatedSphereVerticalSelection₁ : sphereContext%[SixChoiceData verticalRow₁] := by
  exact sphereContext%[sixChoiceData verticalRow₁]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The designated vertical native family in row ₀, using the common fiber residual. -/
def associatedSphereVerticalFamily₀ : sphereContext%[
    Eps → PseudodifferentialOperator (n := n + r)
      (r := (N₀₀).rank) (q := (N₀₁).rank) (N₀₀).Fiber (N₀₁).Fiber η 1] := by
  exact sphereContext%[(associatedSphereVerticalSelection₀ s g).val.2.2.1]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The native L² realization selected for the same total residual in vertical row ₀. -/
def associatedSphereVerticalResidualRealization₀ : sphereContext%[
    (k₀₀).L2SectionSpace η →L[ℂ] (k₀₁).L2SectionSpace η] := by
  exact sphereContext%[(associatedSphereVerticalSelection₀ s g).val.2.2.2.2.2]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The designated vertical native family in row ₁, using the common fiber residual. -/
def associatedSphereVerticalFamily₁ : sphereContext%[
    Eps → PseudodifferentialOperator (n := n + r)
      (r := (N₁₀).rank) (q := (N₁₁).rank) (N₁₀).Fiber (N₁₁).Fiber η 1] := by
  exact sphereContext%[(associatedSphereVerticalSelection₁ s g).val.2.2.1]

set_option maxHeartbeats 16000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The native L² realization selected for the same total residual in vertical row ₁. -/
def associatedSphereVerticalResidualRealization₁ : sphereContext%[
    (k₁₀).L2SectionSpace η →L[ℂ] (k₁₁).L2SectionSpace η] := by
  exact sphereContext%[(associatedSphereVerticalSelection₁ s g).val.2.2.2.2.2]

local notation "nativeU₀" => associatedSphereHorizontalFamily₀ s g
local notation "nativeU₁" => associatedSphereHorizontalFamily₁ s g
local notation "nativeV₀" => associatedSphereVerticalFamily₀ s g
local notation "nativeV₁" => associatedSphereVerticalFamily₁ s g

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
  (Rq).size
  (fun j ↦ ((Rq).patch j).toPiece qa)


set_option maxHeartbeats 8000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The common sums attached to the four fixed native families. -/
abbrev AssociatedSphereNativeSums : Type _ := sphereContext%[
  letI : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ
  letI : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'
  letI (z : Z) : FiniteDimensional ℂ (D z) := finite_fiber («E» := D) z
  letI (z : Z) : FiniteDimensional ℂ (D' z) := finite_fiber («E» := D') z
  NativeGradedFamilySelection
    (n := n + r) (M := Z) (ι := Eps) (μ := η)
    («N₀₀» := N₀₀) («N₁₀» := N₁₀) («N₀₁» := N₀₁) («N₁₁» := N₁₁)
    (E₀ := fun z ↦ (E).Fiber (πS z)) (E₁ := fun z ↦ (E').Fiber (πS z))
    (F₀ := D) (F₁ := D')
    («e₀₀» := (e₀₀).linearEquiv) («e₁₀» := (e₁₀).linearEquiv)
    («e₀₁» := (e₀₁).linearEquiv) («e₁₁» := (e₁₁).linearEquiv)
    («k₀₀» := k₀₀) («k₁₀» := k₁₀) («k₀₁» := k₀₁) («k₁₁» := k₁₁)
    («c₀» := c₀) («c₁» := c₁) («d₀» := d₀) («d₁» := d₁)
    (U₀Family := nativeU₀) (U₁Family := nativeU₁)
    (V₀Family := nativeV₀) (V₁Family := nativeV₁)
    («pfFamily» := fun ε : Eps ↦ pfFamily ε.val)
    («qfFamily» := fun ε : Eps ↦ qfFamily ε.val)]

set_option maxHeartbeats 8000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- Select the common cutoff family through the original tensor-symbol identities. -/
theorem nonempty_associatedSphereNativeSums : Nonempty (AssociatedSphereNativeSums s g) := by
  classical
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  let : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ
  let : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'
  let (z : Z) : FiniteDimensional ℂ (D z) := finite_fiber («E» := D) z
  let (z : Z) : FiniteDimensional ℂ (D' z) := finite_fiber («E» := D') z
  -- Recover symbols and certificates from the fixed row selections, without new witnesses.
  have hH₀ := horizontalRow₀
  have hH₁ := horizontalRow₁
  let row₀ := associatedSphereVerticalSelection₀ s g
  let row₁ := associatedSphereVerticalSelection₁ s g
  let a₀ : Eps → globalSymbolSpace (n := n + r)
      (r := (N₀₀).rank) (q := (N₁₀).rank) (N₀₀).Fiber (N₁₀).Fiber 1 :=
    hH₀.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let a₁ : Eps → globalSymbolSpace (n := n + r)
      (r := (N₀₁).rank) (q := (N₁₁).rank) (N₀₁).Fiber (N₁₁).Fiber 1 :=
    hH₁.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let b₀ : Eps → globalSymbolSpace (n := n + r)
      (r := (N₀₀).rank) (q := (N₀₁).rank) (N₀₀).Fiber (N₀₁).Fiber 1 :=
    row₀.val.2.2.2.1
  let b₁ : Eps → globalSymbolSpace (n := n + r)
      (r := (N₁₀).rank) (q := (N₁₁).rank) (N₁₀).Fiber (N₁₁).Fiber 1 :=
    row₁.val.2.2.2.1
  -- Only the principal and tensor certificates enter the common-sum construction.
  -- Project them from the same choices; the row estimates remain at their provider.
  have hH₀Data :=
    hH₀.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hH₁Data :=
    hH₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hV₀Data := row₀.property
  have hV₁Data := row₁.property
  have hPrincipalH₀ := hH₀Data.2.2.2.1
  have hPrincipalH₁ := hH₁Data.2.2.2.1
  have hPrincipalV₀ := hV₀Data.2.2.1
  have hPrincipalV₁ := hV₁Data.2.2.1
  have hTensorH₀ := hH₀Data.2.2.2.2.1
  have hTensorH₁ := hH₁Data.2.2.2.2.1
  have hTensorV₀ := hV₀Data.2.2.2.1
  have hTensorV₁ := hV₁Data.2.2.2.1
  -- Use the aligned base and sphere presentations in both target rows.
  have hTensorH₁same (ε : Eps) (z : Z) (ξ : CotangentFiber (n := n + r) z)
      (u : (E).Fiber (πS z)) (v : D' z) :
      (a₁ ε).val z ξ ((e₀₁).linearEquiv z (u ⊗ₜ[ℂ] v)) =
        (e₁₁).linearEquiv z (pfFamily ε.val z ξ u ⊗ₜ[ℂ] v) := by
    exact hTensorH₁ ε z ξ u v
  have hTensorV₁same (ε : Eps) (z : Z) (ξ : CotangentFiber (n := n + r) z)
      (u : (E').Fiber (πS z)) (v : D z) :
      (b₁ ε).val z ξ ((e₁₀).linearEquiv z (u ⊗ₜ[ℂ] v)) =
        (e₁₁).linearEquiv z (u ⊗ₜ[ℂ]
          verticalCutoffFactor S (E).Fiber A σ A' σ' hA hA' JV b
            (Rq).size Lq ε.val z ξ v) := by
    exact hTensorV₁ ε z ξ u v
  -- The consumer sees precisely the named PDOs selected above and these same symbols.
  exact nonempty_nativeGradedFamilySelection
    (n := n + r) (M := Z) (ι := Eps) (μ := η)
    («N₀₀» := N₀₀) («N₁₀» := N₁₀) («N₀₁» := N₀₁) («N₁₁» := N₁₁)
    (E₀ := fun z ↦ (E).Fiber (πS z)) (E₁ := fun z ↦ (E').Fiber (πS z))
    (F₀ := D) (F₁ := D')
    («e₀₀» := (e₀₀).linearEquiv) («e₁₀» := (e₁₀).linearEquiv)
    («e₀₁» := (e₀₁).linearEquiv) («e₁₁» := (e₁₁).linearEquiv)
    («k₀₀» := k₀₀) («k₁₀» := k₁₀) («k₀₁» := k₀₁) («k₁₁» := k₁₁)
    («c₀» := c₀) («c₁» := c₁) («d₀» := d₀) («d₁» := d₁)
    (U₀Family := nativeU₀) (U₁Family := nativeU₁)
    (V₀Family := nativeV₀) (V₁Family := nativeV₁)
    («pfFamily» := fun ε : Eps ↦ pfFamily ε.val)
    («qfFamily» := fun ε : Eps ↦ qfFamily ε.val)
    («hk₁₀» := g.nativeIso₁₀_pairing_tmul)
    («hk₀₁» := g.nativeIso₀₁_pairing_tmul)
    («hk₁₁» := g.nativeIso₁₁_pairing_tmul)
    (a₀Family := a₀) (a₁Family := a₁)
    (b₀Family := b₀) (b₁Family := b₁)
    (ha₀ := hPrincipalH₀) (ha₁ := hPrincipalH₁)
    (hb₀ := hPrincipalV₀) (hb₁ := hPrincipalV₁)
    (ha₀tensor := hTensorH₀) (ha₁tensor := hTensorH₁same)
    (hb₀tensor := hTensorV₀) (hb₁tensor := hTensorV₁same)

/-- The common native sum and cutoff selection shared by the index comparisons. -/
def associatedSphereNativeSums : AssociatedSphereNativeSums s g :=
  Classical.choice (nonempty_associatedSphereNativeSums s g)

variable (S) in
/-- A designated cotangent metric for the original canonical associated-sphere model. -/
def associatedSphereCutoffMetric :
    letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
    letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
    letI : ChartedSpace Enr Z := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    SmoothCotangentMetric (n := n + r) (M := Z) := by
  letI : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  letI : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  letI : ChartedSpace Enr Z := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  letI : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  exact Classical.choice (SmoothCotangentMetric.nonempty (n := n + r) (M := Z))

/-- The threshold chosen from the geometric comparison for the fixed fiber quantization. -/
def associatedSphereCutoffBound (_g : AssociatedSphereGreenSelection s) : ℝ := sphereContext%[
  Classical.choose (s.exists_cutoff_intrinsic_index_bound (Rq)
    (associatedSphereCutoffMetric S))]

/-- Positivity of the designated geometric cutoff threshold. -/
theorem associatedSphereCutoffBound_pos : 0 < associatedSphereCutoffBound s g := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  exact (Classical.choose_spec (s.exists_cutoff_intrinsic_index_bound (Rq)
    (associatedSphereCutoffMetric S))).1

/-- The designated threshold remains in the original unit cutoff interval. -/
theorem associatedSphereCutoffBound_le_one : associatedSphereCutoffBound s g ≤ 1 := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  exact (Classical.choose_spec (s.exists_cutoff_intrinsic_index_bound (Rq)
    (associatedSphereCutoffMetric S))).2.1

variable (sums : AssociatedSphereNativeSums s g)


set_option maxHeartbeats 8000000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the designated rows in the common Green and
-- Sobolev context.
/-- The specified cutoff family is elliptic below that same universal geometric threshold. -/
theorem isElliptic_associatedSphereCutoffFamily (ε : Eps)
    (hε : ε.val ≤ associatedSphereCutoffBound s g) :
    sphereContext%[(sums.cutoffFamily ε).IsElliptic] := by
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ChartedSpace (En × Er) Z := associatedSphereChartedSpace S
  let : IsManifold 𝓘(ℝ, En × Er) ∞ Z := associatedSphereIsManifold S
  let : ChartedSpace Enr Z := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsManifold (𝓡 (n + r)) ∞ Z := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν s.fiberMeasure_invariant
  let : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ
  let : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'
  let (z : Z) : FiniteDimensional ℂ (D z) := finite_fiber («E» := D) z
  let (z : Z) : FiniteDimensional ℂ (D' z) := finite_fiber («E» := D') z
  let : TopologicalSpace (TotalSpace Unit sums.nativePlus.Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin sums.nativePlus.rank)) sums.nativePlus.Fiber
  let : TopologicalSpace (TotalSpace Unit sums.nativeMinus.Fiber) :=
    modelTopology (EuclideanSpace ℂ (Fin sums.nativeMinus.rank)) sums.nativeMinus.Fiber
  -- Use the same geometric threshold certificate as the index comparison.
  have hAt := (Classical.choose_spec
    (s.exists_cutoff_intrinsic_index_bound (Rq)
      (associatedSphereCutoffMetric S))).2.2
  exact (hAt sums.nativePlus sums.nativeMinus
    ((g.nativeIso₀₀.sum g.nativeIso₁₁).trans sums.sumPlus)
    ((g.nativeIso₁₀.sum g.nativeIso₀₁).trans sums.sumMinus)
    η sums.cutoffFamily sums.cutoff_symbol ε hε).1

end AtiyahSinger
