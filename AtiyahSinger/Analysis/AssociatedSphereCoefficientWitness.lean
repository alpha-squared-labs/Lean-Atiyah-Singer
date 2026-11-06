/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereIndexAuxiliary

/-!
# Green witnesses for the associated-sphere coefficient comparison

Public module ID: M0108.

This file provides a common seed from the representative and partition producers.
It then chooses the four native models, their Green pair and the coefficient
certificate over that specified seed. Specialization to the fourth index equality
belongs to `AssociatedSphereIndexEqualities`.

The existence proof establishes the canonical instances for the original principal
atlas and native bundle models.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AtiyahSinger

section SeedProduction

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

variable {u v}

set_option maxHeartbeats 12000000 in
-- The extended limit accommodates elaboration of the common positive seed and complete Green
-- selection.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the common positive seed and complete Green
-- selection.
/-- Choose the common seed from the existing original-input and partition providers. -/
theorem nonempty_associatedSpherePositiveSeed (hn : 0 < n) (hr : 0 < r)
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero G SphereCot) :
    Nonempty (AssociatedSpherePositiveSeed S μ u v) := by
  classical
  -- Select the original classes before any Green, metric model or cutoff family is chosen.
  have hInputs := exists_associatedSphere_positiveIndexInputs
    (n := n) (r := r) (P := P) (B := B) (projection := projection) S μ hn hr u v
  -- Base representatives retain their original homogeneous class.
  rcases hInputs with ⟨E, E', p, hpi, hBaseCertificate⟩
  have hu := hBaseCertificate.1
  have hBaseLocalization := hBaseCertificate.2
  -- Keep the same localization and project its six compatibility certificates.
  rcases hBaseLocalization with ⟨gB, h, h', pfull, Rp, C, hLocalizationCertificate⟩
  have hptail := hLocalizationCertificate.1
  have hLocalizationTail₁ := hLocalizationCertificate.2
  have _hpfull := hLocalizationTail₁.1
  have hLocalizationTail₂ := hLocalizationTail₁.2
  have hCsum := hLocalizationTail₂.1
  have hLocalizationTail₃ := hLocalizationTail₂.2
  have _hCpr := hLocalizationTail₃.1
  have hLocalizationTail₄ := hLocalizationTail₃.2
  have hCell := hLocalizationTail₄.1
  have hLocalizationTail₅ := hLocalizationTail₄.2
  have hCA := hLocalizationTail₅.1
  have hPatchInputs := hLocalizationTail₅.2
  -- Retain the actual source indices, smooth cutoffs and original piece identities.
  rcases hPatchInputs with ⟨index, χ, ρ, hχ, hρ, hPatchCertificate⟩
  have hpieces := hPatchCertificate.1
  have hFiberInputs := hPatchCertificate.2
  -- Use the same fiber bundles, actions and homogeneous class.
  rcases hFiberInputs with ⟨F, F', σ, σ', hσ, hσ', q, hqi, hqe, hFiberCertificate⟩
  have hv := hFiberCertificate.1
  have hInvariantInputs := hFiberCertificate.2
  -- Project invariance of the selected cotangent and Hermitian metrics.
  rcases hInvariantInputs with ⟨g, k, k', hInvariantCertificate⟩
  have hk := hInvariantCertificate.1
  have hInvariantTail₁ := hInvariantCertificate.2
  have hk' := hInvariantTail₁.1
  have hInvariantTail₂ := hInvariantTail₁.2
  have hlength := hInvariantTail₂.1
  have hFullSymbolInputs := hInvariantTail₂.2
  -- Retain the exact invariant full symbol and its homogeneous tail.
  rcases hFullSymbolInputs with ⟨qfull, hFullSymbolCertificate⟩
  have hqfixed := hFullSymbolCertificate.1
  have hFullSymbolTail₁ := hFullSymbolCertificate.2
  have hqtail := hFullSymbolTail₁.1
  have hFullSymbolTail₂ := hFullSymbolTail₁.2
  have hqfull := hFullSymbolTail₂.1
  have hOperatorInputs := hFullSymbolTail₂.2
  -- Restore the selected smooth measure before unpacking its actual operator.
  rcases hOperatorInputs with ⟨_RqNative, ν, hν, hQuantizedInputs⟩
  let := hν
  -- Project the same operator principal classes and full representation index.
  rcases hQuantizedInputs with ⟨Q, hQ, hQell, hQCertificate⟩
  have hνinv := hQCertificate.1
  have hQTail₁ := hQCertificate.2
  have hQpr := hQTail₁.1
  have hQTail₂ := hQTail₁.2
  have _hQreg := hQTail₂.1
  have hQindex := hQTail₂.2
  -- All original fields are now available; remove the temporary certificate hypotheses.
  clear hBaseCertificate hLocalizationCertificate hLocalizationTail₁ hLocalizationTail₂
    hLocalizationTail₃ hLocalizationTail₄ hLocalizationTail₅ hPatchCertificate hFiberCertificate
    hInvariantCertificate hInvariantTail₁ hInvariantTail₂ hFullSymbolCertificate
    hFullSymbolTail₁ hFullSymbolTail₂ hQCertificate hQTail₁ hQTail₂
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := S.toIsPrincipalBundle
  -- A common native sphere partition serves both the Green energy and cutoff constructions.
  obtain ⟨L₀, Lother, eL, _iL, _hLchart, hLcutoff, _hLsupport⟩ :=
    exists_common_smoothBundlePresentation_subordinate
      (n := r) (r := F.rank) (q := F'.rank) F.Fiber F'.Fiber
      (fun _ : Unit ↦ (Set.univ : Set Sphere)) (fun _ ↦ isOpen_univ)
      (fun _ ↦ ⟨(), Set.mem_univ _⟩)
  let sphereFrame₁ := fun j ↦ Lother.frame (eL j)
  have hsphereFrame₁ (j : Fin L₀.size) : MemTrivializationAtlas (sphereFrame₁ j) :=
    Lother.frame_mem_atlas (eL j)
  have hsphereSupport₁ (j : Fin L₀.size) :
      tsupport (L₀.cutoff j) ⊆ (sphereFrame₁ j).baseSet := by
    intro y hy
    exact (Lother.support_subset (eL j) (by rwa [hLcutoff])).2
  -- The actual common base frames are the same named selection used by the cutoff construction.
  have hcommon := exists_associatedSphere_common_base_partition
    (n := n) (r := r) (a := E.rank) (a' := E'.rank) S E.Fiber E'.Fiber
  let Bpres := hcommon.choose
  let frame' := hcommon.choose_spec.choose
  have hframe' := hcommon.choose_spec.choose_spec.choose
  have hsframe' := hcommon.choose_spec.choose_spec.choose_spec.choose
  let b := hcommon.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hb := hcommon.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hcommonData := hcommon.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose_spec
  -- Store only these fixed geometric objects and their original certificates.
  -- Every later Green/native construction receives this one seed as an explicit parameter.
  exact ⟨{
    baseSource := E
    baseTarget := E'
    baseSymbol := p
    baseSymbol_elliptic := hpi
    baseClass_eq := hu
    baseCotangentMetric := gB
    baseSourceMetric := h
    baseTargetMetric := h'
    baseFullSymbol := pfull
    baseQuantization := Rp
    localization := C
    localization_elliptic := hCell
    localization_symbol_sum := hCsum
    baseSymbol_tail := hptail
    patchIndex := index
    inputCutoff := χ
    outputCutoff := ρ
    inputCutoff_smooth := hχ
    outputCutoff_smooth := hρ
    piece_origin := hpieces
    base_atlas_principal := hCA
    fiberSource := F
    fiberTarget := F'
    fiberAction := σ
    fiberTargetAction := σ'
    fiberAction_smooth := hσ
    fiberTargetAction_smooth := hσ'
    fiberSymbol := q
    fiberSymbol_elliptic := hqi
    fiberSymbol_equivariant := hqe
    fiberClass_eq := hv
    fiberCotangentMetric := g
    fiberSourceMetric := k
    fiberTargetMetric := k'
    fiberSourceMetric_invariant := hk
    fiberTargetMetric_invariant := hk'
    fiberLength_invariant := hlength
    fiberFullSymbol := qfull
    fiberFullSymbol_invariant := hqfixed
    fiberSymbol_tail := hqtail
    fiberFullSymbol_elliptic := hqfull
    fiberMeasure := ν
    fiberMeasure_smooth := hν
    fiberMeasure_invariant := hνinv
    fiberOperator := Q
    fiberOperator_equivariant := hQ
    fiberOperator_elliptic := hQell
    fiberOperator_principal := hQpr
    fiberOperator_index := hQindex
    sphereSourcePresentation := L₀
    sphereTargetFrame := sphereFrame₁
    sphereTargetFrame_mem := hsphereFrame₁
    sphereTargetFrame_support := hsphereSupport₁
    baseSourcePresentation := Bpres
    baseTargetFrame := frame'
    baseTargetFrame_mem := hframe'
    baseTargetFrame_support := hsframe'
    basePartitionCenter := b
    basePartition_subordinate := hb
    basePartition_sum := hcommonData.2 }⟩

/-- The designated common seed used by all positive-dimensional comparison stages. -/
def associatedSpherePositiveSeed (hn : 0 < n) (hr : 0 < r)
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero G SphereCot) :
    AssociatedSpherePositiveSeed S μ u v :=
  Classical.choice (nonempty_associatedSpherePositiveSeed S μ hn hr u v)

end SeedProduction

section GreenProduction

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

set_option maxHeartbeats 8000000 in
-- The extended limit accommodates elaboration of the common positive seed and complete Green
-- selection.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the common positive seed and complete Green
-- selection.
/-- Select one complete Green stage over the specified seed and its common presentations. -/
theorem nonempty_associatedSphereGreenSelection : Nonempty (AssociatedSphereGreenSelection s) := by
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
  classical
  have hb' (j : Fin s.baseTargetPresentation.size) :
      tsupport (s.baseTargetPresentation.cutoff j) ⊆
        (S.trivialization (s.basePartitionCenter j)).baseSet := s.basePartition_subordinate j
  -- All four native models, their adjoints and the graded pair come from this one call.
  have hgreen := (C).exists_associated_gradedIndexCore
    S (E).Fiber F F' σ σ' hσ hσ' k k'
    s.fiberSourceMetric_invariant s.fiberTargetMetric_invariant (E').Fiber
    s.localization_elliptic h h' ν s.fiberMeasure_invariant Q hQell hQ
    s.sphereSourcePresentation s.sphereTargetPresentation
    s.baseSourcePresentation s.baseTargetPresentation
    s.basePartitionCenter s.basePartitionCenter s.basePartition_subordinate hb'
  have hQA : (QA).IsEquivariant IG σ σ' hA hA' := hgreen.choose
  have hgreen := hgreen.choose_spec
  have hJA : (JA).IsEquivariant IG σ' σ hA' hA := hgreen.choose
  have hgreen := hgreen.choose_spec
  choose l₀₀ l₁₀ l₀₁ l₁₁ N₀₀ N₁₀ N₀₁ N₁₁ k₀₀ k₁₀ k₀₁ k₁₁ hgreen using hgreen
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  choose e₀₀ e₁₀ e₀₁ e₁₁ he₀₀ hi₀₀ he₁₀ hi₁₀ he₀₁ hi₀₁ he₁₁ hi₁₁ hgreen using hgreen
  choose hl₀₀ hl₁₀ hl₀₁ hl₁₁ hN₀₀ hN₁₀ hN₀₁ hN₁₁ hpure₀₀ hpure₁₀ hpure₀₁ hpure₁₁
    hk₀₀ hk₁₀ hk₀₁ hk₁₁ hgreen using hgreen
  choose β₀ hβ₀ hsβ₀ hβ₀one H₀' hH₀formula β₁ hβ₁ hsβ₁ hβ₁one H₁' hH₁formula H₀a H₁a
    hH₀sum hH₁sum hH₀ hH₁ hV₀ hV₁ hgreen using hgreen
  obtain ⟨L, La, hpair⟩ := hgreen
  -- Only the four domains are newly chosen, once, before the native rows depend on them.
  let Li := Classical.choice (nonempty_atlasBundlePresentation A₀₀)
  let Lo := Classical.choice (nonempty_atlasBundlePresentation A₁₀)
  let Li₁ := Classical.choice (nonempty_atlasBundlePresentation A₀₁)
  let Lo₁ := Classical.choice (nonempty_atlasBundlePresentation A₁₁)
  exact ⟨{
    fiberAtlasOperator_equivariant := hQA
    fiberAtlasAdjoint_equivariant := hJA
    atlasMetric₀₀ := l₀₀
    atlasMetric₁₀ := l₁₀
    atlasMetric₀₁ := l₀₁
    atlasMetric₁₁ := l₁₁
    native₀₀ := N₀₀
    native₁₀ := N₁₀
    native₀₁ := N₀₁
    native₁₁ := N₁₁
    nativeMetric₀₀ := k₀₀
    nativeMetric₁₀ := k₁₀
    nativeMetric₀₁ := k₀₁
    nativeMetric₁₁ := k₁₁
    nativeIso₀₀ := e₀₀
    nativeIso₁₀ := e₁₀
    nativeIso₀₁ := e₀₁
    nativeIso₁₁ := e₁₁
    nativeIso₀₀_smooth := he₀₀
    nativeIso₀₀_symm_smooth := hi₀₀
    nativeIso₁₀_smooth := he₁₀
    nativeIso₁₀_symm_smooth := hi₁₀
    nativeIso₀₁_smooth := he₀₁
    nativeIso₀₁_symm_smooth := hi₀₁
    nativeIso₁₁_smooth := he₁₁
    nativeIso₁₁_symm_smooth := hi₁₁
    atlasMetric₀₀_smooth := hl₀₀
    atlasMetric₁₀_smooth := hl₁₀
    atlasMetric₀₁_smooth := hl₀₁
    atlasMetric₁₁_smooth := hl₁₁
    native₀₀_rank := hN₀₀
    native₁₀_rank := hN₁₀
    native₀₁_rank := hN₀₁
    native₁₁_rank := hN₁₁
    atlasMetric₀₀_pure := hpure₀₀
    atlasMetric₁₀_pure := hpure₁₀
    atlasMetric₀₁_pure := hpure₀₁
    atlasMetric₁₁_pure := hpure₁₁
    nativeIso₀₀_isometry := hk₀₀
    nativeIso₁₀_isometry := hk₁₀
    nativeIso₀₁_isometry := hk₀₁
    nativeIso₁₁_isometry := hk₁₁
    baseAdjointCutoff₀ := β₀
    baseAdjointCutoff₀_smooth := hβ₀
    baseAdjointCutoff₀_support := hsβ₀
    baseAdjointCutoff₀_one := hβ₀one
    horizontalPieceAdjoint₀ := H₀'
    horizontalPieceAdjoint₀_formula := hH₀formula
    baseAdjointCutoff₁ := β₁
    baseAdjointCutoff₁_smooth := hβ₁
    baseAdjointCutoff₁_support := hsβ₁
    baseAdjointCutoff₁_one := hβ₁one
    horizontalPieceAdjoint₁ := H₁'
    horizontalPieceAdjoint₁_formula := hH₁formula
    horizontalAdjoint₀ := H₀a
    horizontalAdjoint₁ := H₁a
    horizontalAdjoint₀_sum := hH₀sum
    horizontalAdjoint₁_sum := hH₁sum
    horizontal₀_adjoint := hH₀
    horizontal₁_adjoint := hH₁
    vertical₀_adjoint := hV₀
    vertical₁_adjoint := hV₁
    graded := L
    gradedAdjoint := La
    graded_spec := hpair
    presentation₀₀ := Li
    presentation₁₀ := Lo
    presentation₀₁ := Li₁
    presentation₁₁ := Lo₁ }⟩
/-- The one Green selection shared by the cutoff and coefficient-index stages. -/
def associatedSphereGreenSelection : AssociatedSphereGreenSelection s :=
  Classical.choice (nonempty_associatedSphereGreenSelection s)


end GreenProduction

end AtiyahSinger
