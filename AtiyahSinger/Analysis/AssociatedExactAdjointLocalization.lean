/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalAdjoint
public import AtiyahSinger.Analysis.NativePieceExactMetricAdjoint

/-!
# The original horizontal adjoint as an exact principal localization

Public module ID: M0090.

Use the exact same-chart, swapped-cutoff native adjoint pieces. Keep every
original principal center and supplied adjoint plateau. Their native sum is
identified with the metric adjoint of the actual original base operator, and
their horizontal lift is the given full global adjoint by its raw value formula.
This permits a separate regularization for the odd joint graph without altering
the prescribed adjoint or relying on a uniform parametrix estimate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

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
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable {a' : ℕ} [T2Space B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]


set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3000000 in
-- Normalize the exact local adjoints and their lifts at the original chart centers.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original adjoint lift has an exact principal localization at its original centers. -/
theorem PrincipalPseudodifferentialLocalization.exists_exact_horizontalAdjoint_localization {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (β : Fin C.size → B → ℝ)
    (hβ : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ (S.trivialization (C.center j)).baseSet)
    (hβone : ∀ j x, x ∈ (C.piece j).chart.symm ''
      (tsupport (C.piece j).input.cutoff ∪ tsupport (C.piece j).output.cutoff) → β j x = 1) :
    let Q (j : Fin C.size) : PseudodifferentialOperator
        (n := n) (r := a) (q := a') E E' μ m :=
      ⟨(C.piece j).toLinearMap, (C.piece j).isPseudodifferentialOperator m⟩
    let J (j : Fin C.size) := (Q j).metricFormalAdjoint h h'
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
      .of_injective
        (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
        (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    ∀ H' : Fin C.size → AT'.smoothSections →ₗ[ℂ] AT.smoothSections,
      (∀ j w z, (H' j w).val z = associatedSphereTensorBaseExtension S E σ (C.center j)
        (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E') (smoothSections E)
          (J j).toLinearMap)
            (associatedSphereTensorCutoffBaseRestriction (a := a')
              S E' A σ hσ (C.center j) (β j) (hβ j) (hβsupport j) y w)).val x) z) →
      ∃ C' : PrincipalPseudodifferentialLocalization (a := a') (a' := a) S E' E μ m,
        C'.baseOperator = C.baseOperator.metricFormalAdjoint h h' ∧
          C'.horizontalLift S E' A σ E hσ = ∑ j, H' j := by
  classical
  -- Each selected piece is the full original native adjoint, in the unchanged base chart.
  have hpieces (j : Fin C.size) :=
    (C.piece j).exists_exact_metricFormalAdjoint_piece (μ := μ) h h'
  choose Tj hchart hin hout hmap using hpieces
  intro Q J
  have hpair (j : Fin C.size) :
      IsMetricFormalAdjoint h h' μ (C.piece j).toLinearMap (Tj j).toLinearMap := by
    rw [hmap j]
    exact (Q j).isMetricFormalAdjoint_metricFormalAdjoint h h'
  have hsum (s : Finset (Fin C.size)) :
      IsMetricFormalAdjoint h h' μ
        (∑ j ∈ s, (C.piece j).toLinearMap) (∑ j ∈ s, (Tj j).toLinearMap) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro u v
      change (h'.smoothL2SectionCore μ).inner 0 v = (h.smoothL2SectionCore μ).inner u 0
      have hzeroLeft : (h'.smoothL2SectionCore μ).inner 0 v = 0 := by
        exact InnerProductSpace.Core.inner_zero_left
          (c := (h'.smoothL2SectionCore μ).toCore) v
      have hzeroRight : (h.smoothL2SectionCore μ).inner u 0 = 0 := by
        exact InnerProductSpace.Core.inner_zero_right
          (c := (h.smoothL2SectionCore μ).toCore) u
      exact hzeroLeft.trans hzeroRight.symm
    | @insert j s hj ih =>
      simpa only [Finset.sum_insert hj] using (hpair j).add ih
  have hbase : (C.baseOperator.metricFormalAdjoint h h').toLinearMap =
      ∑ j, (Tj j).toLinearMap := by
    apply (C.baseOperator.isMetricFormalAdjoint_metricFormalAdjoint h h').unique
    rw [C.baseOperator_eq]
    exact hsum Finset.univ
  -- The new localization retains the original centers and the given adjoint plateaus literally.
  let C' : PrincipalPseudodifferentialLocalization (a := a') (a' := a) S E' E μ m :=
    { size := C.size
      center := C.center
      piece := Tj
      baseOperator := C.baseOperator.metricFormalAdjoint h h'
      baseOperator_eq := hbase
      piece_support := by
        intro j
        rw [hout j, hin j, hchart j, Set.union_comm]
        exact C.piece_support j
      inputCutoff := β
      smooth_inputCutoff := hβ
      inputCutoff_support := hβsupport
      inputCutoff_eq_one := by
        intro j x hx
        rw [hin j, hchart j] at hx
        exact hβone j x (Set.image_mono Set.subset_union_right hx) }
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
    .of_injective
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  intro AT AT' H' hH'
  refine ⟨C', rfl, ?_⟩
  -- Compare the complete base-section operator inside each original raw principal return.
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  rw [C'.horizontalLift_apply S E' A σ E hσ]
  have hsumval : ((∑ j, H' j) (show AT'.smoothSections from w)).val z =
      ∑ j, (H' j w).val z := by
    change (AT.smoothSections.subtype ((∑ j, H' j) w)) z = _
    rw [LinearMap.sum_apply, map_sum, Finset.sum_apply]
    rfl
  rw [hsumval]
  apply Finset.sum_congr rfl
  intro j _
  rw [hH' j w z]
  change associatedSphereTensorBaseExtension S E σ (C.center j)
    (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E') (smoothSections E)
      (Tj j).toLinearMap)
        (associatedSphereTensorCutoffBaseRestriction (a := a')
          S E' A σ hσ (C.center j) (β j) (hβ j) (hβsupport j) y w)).val x) z = _
  rw [hmap j]

end AtiyahSinger
