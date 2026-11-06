/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalLift
public import AtiyahSinger.Analysis.AssociatedTensorLocalHorizontalAdjunction

/-!
# The full adjoint of the fixed global horizontal lift

Public module ID: M0145.

Each principal piece has a complete native metric adjoint, with a base plateau
and supported lift. Their finite sum is the integral adjoint of the global
horizontal map, including all smoothing terms. The plateaus and full adjoint
formulas are retained for controlled regularization in the supplied principal
localization, metrics and associated product measure.
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

variable [IsFiniteMeasure μ]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]


set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1400000 in
-- The extended limit accommodates the finite assembly of the specified local adjoints.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite sum of the full local adjoints is the adjoint of this same global lift. -/
theorem PrincipalPseudodifferentialLocalization.exists_horizontalLift_integral_adjoint {m : ℝ}
    (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (ν : Measure (OrthogonalSphere r)) [IsFiniteMeasure ν]
    (hν : ∀ g : G, Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)
    (k : ∀ y, InnerProductSpace.Core ℂ (F y)) :
    let Q (j : Fin C₀.size) : PseudodifferentialOperator
        (n := n) (r := a) (q := a') E E' μ m :=
      ⟨(C₀.piece j).toLinearMap, (C₀.piece j).isPseudodifferentialOperator m⟩
    let J (j : Fin C₀.size) := (Q j).metricFormalAdjoint h h'
    let K (j : Fin C₀.size) := (C₀.piece j).chart.symm ''
      (tsupport (C₀.piece j).input.cutoff ∪ tsupport (C₀.piece j).output.cutoff)
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
    ∃ (β : Fin C₀.size → B → ℝ)
      (hβ : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (β j))
      (hβsupport : ∀ j, tsupport (β j) ⊆ (S.trivialization (C₀.center j)).baseSet),
      (∀ j, ∀ x ∈ K j, β j x = 1) ∧
      ∃ H' : Fin C₀.size → AT'.smoothSections →ₗ[ℂ] AT.smoothSections,
        (∀ j w z, (H' j w).val z = associatedSphereTensorBaseExtension S E σ (C₀.center j)
          (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E') (smoothSections E)
            (J j).toLinearMap)
              (associatedSphereTensorCutoffBaseRestriction (a := a')
                S E' A σ hσ (C₀.center j) (β j) (hβ j) (hβsupport j) y w)).val x) z) ∧
        ∀ (l : ContinuousHermitianMetric T) (l' : ContinuousHermitianMetric T'),
          AT.IsSmoothHermitianMetric l → AT'.IsSmoothHermitianMetric l' →
          (∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F y),
            (l.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
                (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
              h.pairing (projection p) u v * (k y).inner s t) →
          (∀ (p : P) (y : OrthogonalSphere r) (u v : E' (projection p)) (s t : F y),
            (l'.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
                (associatedSphereTensorFiberEquiv S E' σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E' σ p y (v ⊗ₜ[ℂ] t)) =
              h'.pairing (projection p) u v * (k y).inner s t) →
          ∀ (s : AT.smoothSections) (t : AT'.smoothSections),
            (∫ z, (l'.toCore z).inner ((C₀.horizontalLift S E A σ E' hσ s).val z) (t.val z)
              ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
            ∫ z, (l.toCore z).inner (s.val z) (((∑ j, H' j) t).val z)
              ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let := linearModelChartedSpace lm Z
  let := isManifold_linearModelChartedSpace lm Z
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
    .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
  have houtput (j : Fin C₀.size) :
      (C₀.piece j).chart.symm '' tsupport (C₀.piece j).output.cutoff ⊆
        (S.trivialization (C₀.center j)).baseSet :=
    fun _ hx ↦ C₀.piece_support j (Set.image_mono Set.subset_union_left hx)
  have hinput (j : Fin C₀.size) :
      (C₀.piece j).chart.symm '' tsupport (C₀.piece j).input.cutoff ⊆
        (S.trivialization (C₀.center j)).baseSet :=
    fun _ hx ↦ C₀.piece_support j (Set.image_mono Set.subset_union_right hx)
  -- Choose the full local adjoints and plateaus uniformly over the compatible metric pairings.
  have hlocal (j : Fin C₀.size) :=
    exists_associatedSphereTensorLocalHorizontal_integral_adjoint (a := a) (μ := μ)
      S E A σ E' (C₀.piece j) h h' hσ ν hν k (C₀.center j)
      (C₀.inputCutoff j) (C₀.smooth_inputCutoff j) (C₀.inputCutoff_support j)
      (C₀.inputCutoff_eq_one j) (hinput j) (houtput j)
  choose β hβ hβsupport hβone H' hH' hAdj using hlocal
  dsimp only
  refine ⟨β, hβ, hβsupport, hβone, H', hH', ?_⟩
  intro l l' hl hl' hpair hpair' s t
  let H (j : Fin C₀.size) := associatedSphereTensorLocalHorizontalLift (a := a)
    S E A σ E' (C₀.piece j) hσ (C₀.center j) (C₀.inputCutoff j)
      (C₀.smooth_inputCutoff j) (C₀.inputCutoff_support j) (houtput j)
  have hsum : C₀.horizontalLift S E A σ E' hσ = ∑ j, H j := rfl
  have hleft (z : Z) :
      (l'.toCore z).inner ((C₀.horizontalLift S E A σ E' hσ s).val z) (t.val z) =
        ∑ j, (l'.toCore z).inner ((H j s).val z) (t.val z) := by
    rw [hsum]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    let L : T' z →+ ℂ := AddMonoidHom.mk'
      (fun v ↦ (l'.toCore z).inner v (t.val z)) (fun v w ↦ (l'.toCore z).add_left v w _)
    exact map_sum L _ _
  have hright (z : Z) :
      (l.toCore z).inner (s.val z) (((∑ j, H' j) t).val z) =
        ∑ j, (l.toCore z).inner (s.val z) ((H' j t).val z) := by
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    let := l.toCore z
    let L : T z →+ ℂ := AddMonoidHom.mk'
      (fun v ↦ (l.toCore z).inner (s.val z) v)
      (fun v w ↦ InnerProductSpace.Core.inner_add_right (s.val z) v w)
    exact map_sum L _ _
  -- Each summand is integrable for the original finite measure, before passing sums through it.
  have hi (j : Fin C₀.size) :
      Integrable (fun z ↦ (l'.toCore z).inner ((H j s).val z) (t.val z)) η :=
    (AT'.contMDiff_pairing l' hl' (H j s) t).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi' (j : Fin C₀.size) :
      Integrable (fun z ↦ (l.toCore z).inner (s.val z) ((H' j t).val z)) η :=
    (AT.contMDiff_pairing l hl s (H' j t)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z, ∑ j, (l'.toCore z).inner ((H j s).val z) (t.val z) ∂η :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∑ j, ∫ z, (l'.toCore z).inner ((H j s).val z) (t.val z) ∂η :=
      integral_finsetSum _ (fun j _ ↦ hi j)
    _ = ∑ j, ∫ z, (l.toCore z).inner (s.val z) ((H' j t).val z) ∂η := by
      apply Finset.sum_congr rfl
      intro j _
      exact hAdj j l l' hl hl' hpair hpair' s t
    _ = ∫ z, ∑ j, (l.toCore z).inner (s.val z) ((H' j t).val z) ∂η :=
      (integral_finsetSum _ (fun j _ ↦ hi' j)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hright z).symm))

end AtiyahSinger
