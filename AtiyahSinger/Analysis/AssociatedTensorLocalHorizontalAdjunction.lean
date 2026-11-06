/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalFormalAdjoint
public import AtiyahSinger.Analysis.AssociatedTensorLocalHorizontalProperties
public import AtiyahSinger.Analysis.AssociatedTensorNativeHorizontalAdjoint

/-!
# Integral adjunction of the local horizontal lift

Public module ID: M0180.

The piece and its input cutoff define the forward map. The native metric
adjoint is lifted with one base plateau on both input and output supports.
Agreement on the input support identifies the forward lift with the plateau
lift. For compatible tensor metrics, the associated product measure then gives
the integral adjunction. The conclusion retains the same plateau and the full
adjoint value formula.
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
set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the full localized metric-adjoint integral comparison.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original local horizontal map has the lifted full native metric adjoint. -/
theorem exists_associatedSphereTensorLocalHorizontal_integral_adjoint {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (ν : Measure (OrthogonalSphere r)) [IsFiniteMeasure ν]
    (hν : ∀ g : G, Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)
    (k : ∀ y, InnerProductSpace.Core ℂ (F y))
    (b : B) (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet) :
    let Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m :=
      ⟨L.toLinearMap, L.isPseudodifferentialOperator m⟩
    let J := Q.metricFormalAdjoint h h'
    let K := L.chart.symm '' (tsupport L.input.cutoff ∪ tsupport L.output.cutoff)
    ∃ (β : B → ℝ) (hβ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ β)
      (hβsupport : tsupport β ⊆ (S.trivialization b).baseSet),
      (∀ x ∈ K, β x = 1) ∧
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
      let H := associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ
        b χ hχ hχsupport houtput
      ∃ H' : AT'.smoothSections →ₗ[ℂ] AT.smoothSections,
        (∀ w z, (H' w).val z = associatedSphereTensorBaseExtension S E σ b
          (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E') (smoothSections E)
            J.toLinearMap)
              (associatedSphereTensorCutoffBaseRestriction (a := a')
                S E' A σ hσ b β hβ hβsupport y w)).val x) z) ∧
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
            (∫ z, (l'.toCore z).inner ((H s).val z) (t.val z)
              ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
            ∫ z, (l.toCore z).inner (s.val z) ((H' t).val z)
              ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν := by
  classical
  let Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m :=
    ⟨L.toLinearMap, L.isPseudodifferentialOperator m⟩
  let J := Q.metricFormalAdjoint h h'
  let K := L.chart.symm '' (tsupport L.input.cutoff ∪ tsupport L.output.cutoff)
  have hKb : K ⊆ (S.trivialization b).baseSet := by
    rintro x ⟨y, hy | hy, rfl⟩
    · exact hinput ⟨y, hy, rfl⟩
    · exact houtput ⟨y, hy, rfl⟩
  -- The same native adjoint and one plateau are chosen before all upstairs metrics and sections.
  obtain ⟨hJ, β, hβ, hβsupport, hβone, H', hH'⟩ :=
    exists_associatedSphereTensorLocalHorizontalAdjoint (a := a) (μ := μ)
      S E A σ E' L h h' hσ b hKb
  refine ⟨β, hβ, hβsupport, hβone, ?_⟩
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
    .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let H := associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ
    b χ hχ hχsupport houtput
  let Hβ := associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ
    b β hβ hβsupport houtput
  dsimp only
  refine ⟨H', hH', ?_⟩
  intro l l' hl hl' hpair hpair' s t
  -- The original cutoff needs to agree with the plateau only on the original input support.
  have hHHβ : H = Hβ :=
    associatedSphereTensorLocalHorizontalLift_eq_of_eq_on_support (a := a)
      S E A σ E' L hσ b χ β hχ hχsupport hβ hβsupport
      (fun x hx ↦ (hχone x hx).trans (hβone x (Set.image_mono Set.subset_union_left hx)).symm)
      houtput
  have hQzero (u : smoothSections (n := n) (r := a) E) (x : B) (hx : x ∉ K) :
      (Q.toLinearMap u).val x = 0 :=
    L.toLinearMap_eq_zero u x (fun hx' ↦ hx (Set.image_mono Set.subset_union_right hx'))
  have hJzero (u : smoothSections (n := n) (r := a') E') (x : B) (hx : x ∉ K) :
      (J.toLinearMap u).val x = 0 := by
    by_contra hne
    exact hx (hJ.1 u (subset_closure hne))
  -- Use the full normalized lift formulas, then the actual measure's supported Fubini identity.
  have hHβ (w : AT.smoothSections) (z : Z) : (Hβ w).val z =
      associatedSphereTensorBaseExtension S E' σ b
        (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E) (smoothSections E')
          Q.toLinearMap)
            (associatedSphereTensorCutoffBaseRestriction (a := a)
              S E A σ hσ b β hβ hβsupport y w)).val x) z := by
    rw [associatedSphereTensorLocalHorizontalLift_apply]
    rfl
  change (∫ z, (l'.toCore z).inner ((H s).val z) (t.val z)
    ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) = _
  rw [hHHβ]
  exact associatedSphereTensorSupportedHorizontalLift_integral_adjoint (a := a)
    S E A σ E' Q J h h' (Q.isMetricFormalAdjoint_metricFormalAdjoint h h')
    hσ ν hν k b K hKb β hβ hβsupport hβone hQzero hJzero
    Hβ H' hHβ hH' l l' hl hl' hpair hpair' s t

end AtiyahSinger
