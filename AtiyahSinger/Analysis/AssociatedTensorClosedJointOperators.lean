/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalAdjoint
public import AtiyahSinger.Analysis.AssociatedTensorJointL2Realization
public import AtiyahSinger.Analysis.AssociatedTensorNativeVerticalAdjoint
public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev
public import AtiyahSinger.Geometry.AssociatedSphereTensorMetric

/-!
# Closed joint operators for the associated tensor square

Public module ID: M0140.

Four tensor metrics and compatible native models are chosen once. The full
native sphere operator and its metric formal adjoint give the two vertical
adjunctions. The principal localization supplies the two complete horizontal
adjoints. These certificates produce two dense closed joint graphs in the same
four integral Hilbert spaces, with the cross pairing inherited from the
commuting square.
-/

@[expose] public noncomputable section

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
  (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (y : OrthogonalSphere r) (u v : F.Fiber y),
      k.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = k.pairing y u v)
  (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (y : OrthogonalSphere r) (u v : F'.Fiber y),
      k'.pairing (g • y) (σ'.linearMap g y u) (σ'.linearMap g y v) = k'.pairing y u v)
  [MeasurableSpace B] [BorelSpace B] [CompactSpace B]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

variable {a' : ℕ} [T2Space B] [SecondCountableTopology B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ] [IsFiniteMeasure μ]

local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z

include hk hk' in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 6400000 in
-- The extended limit accommodates the original factor metrics, adjoints and both joint operators.
/-- Actual factor metrics and adjoints give the two associated closed joint operators. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_closed_jointOperators
    {m d : ℝ} (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (ν : Measure Y) [IsFiniteMeasure ν] [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν d)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') :
    let Pbase (j : Fin C₀.size) : PseudodifferentialOperator
        (n := n) (r := a) (q := a') E E' μ m :=
      ⟨(C₀.piece j).toLinearMap, (C₀.piece j).isPseudodifferentialOperator m⟩
    let Jbase (j : Fin C₀.size) := (Pbase j).metricFormalAdjoint h h'
    let Kbase (j : Fin C₀.size) := (C₀.piece j).chart.symm ''
      (tsupport (C₀.piece j).input.cutoff ∪ tsupport (C₀.piece j).output.cutoff)
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let QA := Q.toAtlasPseudodifferentialOperator
    let JA := (Q.metricFormalAdjoint k k').toAtlasPseudodifferentialOperator
    ∃ (hQA : QA.IsEquivariant IG σ σ' hA hA')
      (hJA : JA.IsEquivariant IG σ' σ hA' hA),
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI : TopologicalSpace (TotalSpace Unit U) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI : TopologicalSpace (TotalSpace Unit U') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
    letI : IsSmoothPositiveMeasure (n := n + r) η :=
      isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
    let A₀₀ := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    let A₁₀ := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
    let A₀₁ := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
    let A₁₁ := associatedSphereTensorBundleAtlas (a := a') S E' A' σ' hA'
    letI (y : Y) : FiniteDimensional ℂ (F.Fiber y) :=
      .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
        (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
    letI (y : Y) : FiniteDimensional ℂ (F'.Fiber y) :=
      .of_injective
        (A'.frameLinearEquiv (A'.covers y).choose y (A'.covers y).choose_spec).toLinearMap
        (A'.frameLinearEquiv (A'.covers y).choose y (A'.covers y).choose_spec).injective
    let H₀ := C₀.horizontalLift S E A σ E' hA
    let H₁ := C₀.horizontalLift S E A' σ' E' hA'
    let V₀ := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
    let V₁ := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A' σ' hA' QA hQA
    let V₀a := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hA' A σ hA JA hJA
    let V₁a := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hA' A σ hA JA hJA
    ∃ (l₀₀ : ContinuousHermitianMetric T) (l₁₀ : ContinuousHermitianMetric U)
      (l₀₁ : ContinuousHermitianMetric T') (l₁₁ : ContinuousHermitianMetric U')
      (N₀₀ N₁₀ N₀₁ N₁₁ : SmoothFiniteComplexBundle (n := n + r) Z)
      (k₀₀ : SmoothHermitianMetric (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
      (k₁₀ : SmoothHermitianMetric (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
      (k₀₁ : SmoothHermitianMetric (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
      (k₁₁ : SmoothHermitianMetric (n := n + r) (r := N₁₁.rank) N₁₁.Fiber),
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
      ∃ (e₀₀ : Iso T N₀₀.Fiber)
        (e₁₀ : Iso U N₁₀.Fiber)
        (e₀₁ : Iso T' N₀₁.Fiber)
        (e₁₁ : Iso U' N₁₁.Fiber)
        (he₀₀ : IsSmoothAtlasBundleMap A₀₀
          (nativeSmoothComplexBundleAtlas N₀₀.Fiber) e₀₀.toHom.linearMap)
        (hi₀₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀₀.Fiber)
          A₀₀ e₀₀.symm.toHom.linearMap)
        (he₁₀ : IsSmoothAtlasBundleMap A₁₀
          (nativeSmoothComplexBundleAtlas N₁₀.Fiber) e₁₀.toHom.linearMap)
        (hi₁₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁₀.Fiber)
          A₁₀ e₁₀.symm.toHom.linearMap)
        (he₀₁ : IsSmoothAtlasBundleMap A₀₁
          (nativeSmoothComplexBundleAtlas N₀₁.Fiber) e₀₁.toHom.linearMap)
        (hi₀₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀₁.Fiber)
          A₀₁ e₀₁.symm.toHom.linearMap)
        (he₁₁ : IsSmoothAtlasBundleMap A₁₁
          (nativeSmoothComplexBundleAtlas N₁₁.Fiber) e₁₁.toHom.linearMap)
        (hi₁₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁₁.Fiber)
          A₁₁ e₁₁.symm.toHom.linearMap),
        A₀₀.IsSmoothHermitianMetric l₀₀ ∧
        A₁₀.IsSmoothHermitianMetric l₁₀ ∧
        A₀₁.IsSmoothHermitianMetric l₀₁ ∧
        A₁₁.IsSmoothHermitianMetric l₁₁ ∧
        N₀₀.rank = a * F.rank ∧
        N₁₀.rank = a' * F.rank ∧
        N₀₁.rank = a * F'.rank ∧
        N₁₁.rank = a' * F'.rank ∧
        (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F.Fiber y),
          (l₀₀.toCore (associatedBundleMk G P Y p y)).inner
              (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
            h.pairing (projection p) u v * k.pairing y s t) ∧
        (∀ (p : P) (y : Y) (u v : E' (projection p)) (s t : F.Fiber y),
          (l₁₀.toCore (associatedBundleMk G P Y p y)).inner
              (associatedSphereTensorFiberEquiv S E' σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E' σ p y (v ⊗ₜ[ℂ] t)) =
            h'.pairing (projection p) u v * k.pairing y s t) ∧
        (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F'.Fiber y),
          (l₀₁.toCore (associatedBundleMk G P Y p y)).inner
              (associatedSphereTensorFiberEquiv S E σ' p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E σ' p y (v ⊗ₜ[ℂ] t)) =
            h.pairing (projection p) u v * k'.pairing y s t) ∧
        (∀ (p : P) (y : Y) (u v : E' (projection p)) (s t : F'.Fiber y),
          (l₁₁.toCore (associatedBundleMk G P Y p y)).inner
              (associatedSphereTensorFiberEquiv S E' σ' p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E' σ' p y (v ⊗ₜ[ℂ] t)) =
            h'.pairing (projection p) u v * k'.pairing y s t) ∧
        (∀ (z : Z) (v w : T z),
          k₀₀.pairing z (e₀₀.linearEquiv z v) (e₀₀.linearEquiv z w) =
            (l₀₀.toCore z).inner v w) ∧
        (∀ (z : Z) (v w : U z),
          k₁₀.pairing z (e₁₀.linearEquiv z v) (e₁₀.linearEquiv z w) =
            (l₁₀.toCore z).inner v w) ∧
        (∀ (z : Z) (v w : T' z),
          k₀₁.pairing z (e₀₁.linearEquiv z v) (e₀₁.linearEquiv z w) =
            (l₀₁.toCore z).inner v w) ∧
        (∀ (z : Z) (v w : U' z),
          k₁₁.pairing z (e₁₁.linearEquiv z v) (e₁₁.linearEquiv z w) =
            (l₁₁.toCore z).inner v w) ∧
        ∃ (β₀ : Fin C₀.size → B → ℝ)
          (hβ₀ : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (β₀ j))
          (hsβ₀ : ∀ j, tsupport (β₀ j) ⊆ (S.trivialization (C₀.center j)).baseSet),
          (∀ j, ∀ x ∈ Kbase j, β₀ j x = 1) ∧
          ∃ H₀' : Fin C₀.size → A₁₀.smoothSections →ₗ[ℂ] A₀₀.smoothSections,
            (∀ j w z, (H₀' j w).val z = associatedSphereTensorBaseExtension S E σ
              (C₀.center j)
              (fun y x ↦ ((tensorSectionOperator (F.Fiber y)
                (smoothSections E') (smoothSections E) (Jbase j).toLinearMap)
                  (associatedSphereTensorCutoffBaseRestriction (a := a') S E' A σ hA
                    (C₀.center j) (β₀ j) (hβ₀ j) (hsβ₀ j) y w)).val x) z) ∧
        ∃ (β₁ : Fin C₀.size → B → ℝ)
          (hβ₁ : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (β₁ j))
          (hsβ₁ : ∀ j, tsupport (β₁ j) ⊆ (S.trivialization (C₀.center j)).baseSet),
          (∀ j, ∀ x ∈ Kbase j, β₁ j x = 1) ∧
          ∃ H₁' : Fin C₀.size → A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections,
            (∀ j w z, (H₁' j w).val z = associatedSphereTensorBaseExtension S E σ'
              (C₀.center j)
              (fun y x ↦ ((tensorSectionOperator (F'.Fiber y)
                (smoothSections E') (smoothSections E) (Jbase j).toLinearMap)
                  (associatedSphereTensorCutoffBaseRestriction (a := a') S E' A' σ' hA'
                    (C₀.center j) (β₁ j) (hβ₁ j) (hsβ₁ j) y w)).val x) z) ∧
        ∃ (H₀a : A₁₀.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
          (H₁a : A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections),
        H₀a = ∑ j, H₀' j ∧ H₁a = ∑ j, H₁' j ∧
        (∀ u v, (∫ z, (l₁₀.toCore z).inner ((H₀ u).val z) (v.val z) ∂η) =
          ∫ z, (l₀₀.toCore z).inner (u.val z) ((H₀a v).val z) ∂η) ∧
        (∀ u v, (∫ z, (l₁₁.toCore z).inner ((H₁ u).val z) (v.val z) ∂η) =
          ∫ z, (l₀₁.toCore z).inner (u.val z) ((H₁a v).val z) ∂η) ∧
        (∀ u v, (∫ z, (l₀₁.toCore z).inner ((V₀ u).val z) (v.val z) ∂η) =
          ∫ z, (l₀₀.toCore z).inner (u.val z) ((V₀a v).val z) ∂η) ∧
        (∀ u v, (∫ z, (l₁₁.toCore z).inner ((V₁ u).val z) (v.val z) ∂η) =
          ∫ z, (l₁₀.toCore z).inner (u.val z) ((V₁a v).val z) ∂η) ∧
        let S₀₀ := (atlasSmoothSectionEquiv A₀₀ (nativeSmoothComplexBundleAtlas N₀₀.Fiber)
          e₀₀ he₀₀ hi₀₀).trans (nativeSmoothSectionLinearEquiv N₀₀.Fiber)
        let i₀₀ := (k₀₀.smoothToL2 η).comp S₀₀.toLinearMap
        let S₁₀ := (atlasSmoothSectionEquiv A₁₀ (nativeSmoothComplexBundleAtlas N₁₀.Fiber)
          e₁₀ he₁₀ hi₁₀).trans (nativeSmoothSectionLinearEquiv N₁₀.Fiber)
        let i₁₀ := (k₁₀.smoothToL2 η).comp S₁₀.toLinearMap
        let S₀₁ := (atlasSmoothSectionEquiv A₀₁ (nativeSmoothComplexBundleAtlas N₀₁.Fiber)
          e₀₁ he₀₁ hi₀₁).trans (nativeSmoothSectionLinearEquiv N₀₁.Fiber)
        let i₀₁ := (k₀₁.smoothToL2 η).comp S₀₁.toLinearMap
        let S₁₁ := (atlasSmoothSectionEquiv A₁₁ (nativeSmoothComplexBundleAtlas N₁₁.Fiber)
          e₁₁ he₁₁ hi₁₁).trans (nativeSmoothSectionLinearEquiv N₁₁.Fiber)
        let i₁₁ := (k₁₁.smoothToL2 η).comp S₁₁.toLinearMap
        ∃ (R₀ : k₀₀.L2SectionSpace η →ₗ.[ℂ] (k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η))
          (R₁ : k₁₁.L2SectionSpace η →ₗ.[ℂ] (k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η)),
          R₀.graph = (i₀₀.prod ((i₁₀.comp H₀).prod (i₀₁.comp V₀))).range.topologicalClosure ∧
          R₀.IsClosed ∧ Dense (R₀.domain : Set (k₀₀.L2SectionSpace η)) ∧
          R₁.graph = (i₁₁.prod ((i₁₀.comp V₁a).prod (i₀₁.comp H₁a))).range.topologicalClosure ∧
          R₁.IsClosed ∧ Dense (R₁.domain : Set (k₁₁.L2SectionSpace η)) ∧
          ∀ (u : R₀.domain) (v : R₁.domain),
            inner ℂ (R₀ u).1 (R₁ v).1 = inner ℂ (R₀ u).2 (R₁ v).2 := by
  classical
  let Pbase (j : Fin C₀.size) : PseudodifferentialOperator
      (n := n) (r := a) (q := a') E E' μ m :=
    ⟨(C₀.piece j).toLinearMap, (C₀.piece j).isPseudodifferentialOperator m⟩
  let Jbase (j : Fin C₀.size) := (Pbase j).metricFormalAdjoint h h'
  let Kbase (j : Fin C₀.size) := (C₀.piece j).chart.symm ''
    (tsupport (C₀.piece j).input.cutoff ∪ tsupport (C₀.piece j).output.cutoff)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
  let QA := Q.toAtlasPseudodifferentialOperator
  let JA := (Q.metricFormalAdjoint k k').toAtlasPseudodifferentialOperator
  -- Both vertical certificates use the full same sphere operator and the same native adjoint.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hvertical₀ := associatedSphereTensorNativeVertical_integral_adjoint (a := a)
    S E F F' σ σ' hσ hσ' k k' hk hk' μ ν hν Q hQ h.toCore
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hvertical₁ := associatedSphereTensorNativeVertical_integral_adjoint (a := a')
    S E' F F' σ σ' hσ hσ' k k' hk hk' μ ν hν Q hQ h'.toCore
  obtain ⟨hQA, hJA, hV₀⟩ := hvertical₀
  obtain ⟨_, _, hV₁⟩ := hvertical₁
  refine ⟨hQA, hJA, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let := linearModelChartedSpace lm Z
  let := isManifold_linearModelChartedSpace lm Z
  let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  let A₀₀ := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let A₁₀ := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
  let A₀₁ := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
  let A₁₁ := associatedSphereTensorBundleAtlas (a := a') S E' A' σ' hA'
  -- Each original product metric is chosen once, before either joint graph is formed.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hmetric₀₀ := exists_associatedSphereTensorMetric (a := a)
    S E A σ hA h.toContinuousHermitianMetric
    h.isSmoothHermitianMetric_nativeAtlas k.toContinuousHermitianMetric
    k.isSmoothHermitianMetric_nativeAtlas hk
  choose l₀₀ hl₀₀ hpure₀₀ using hmetric₀₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hmetric₁₀ := exists_associatedSphereTensorMetric (a := a')
    S E' A σ hA h'.toContinuousHermitianMetric
    h'.isSmoothHermitianMetric_nativeAtlas k.toContinuousHermitianMetric
    k.isSmoothHermitianMetric_nativeAtlas hk
  choose l₁₀ hl₁₀ hpure₁₀ using hmetric₁₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hmetric₀₁ := exists_associatedSphereTensorMetric (a := a)
    S E A' σ' hA' h.toContinuousHermitianMetric
    h.isSmoothHermitianMetric_nativeAtlas k'.toContinuousHermitianMetric
    k'.isSmoothHermitianMetric_nativeAtlas hk'
  choose l₀₁ hl₀₁ hpure₀₁ using hmetric₀₁
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hmetric₁₁ := exists_associatedSphereTensorMetric (a := a')
    S E' A' σ' hA' h'.toContinuousHermitianMetric
    h'.isSmoothHermitianMetric_nativeAtlas k'.toContinuousHermitianMetric
    k'.isSmoothHermitianMetric_nativeAtlas hk'
  choose l₁₁ hl₁₁ hpure₁₁ using hmetric₁₁
  -- The actual tensor-fiber equivalences determine the four native ranks, including rank zero.
  have hr₀₀ (z : Z) : Module.finrank ℂ (T z) = a * F.rank := by
    obtain ⟨⟨p, y⟩, rfl⟩ := Quotient.exists_rep z
    change Module.finrank ℂ (T (associatedBundleMk G P Y p y)) = a * F.rank
    rw [← (associatedSphereTensorFiberEquiv S E σ p y).finrank_eq,
      Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a)) E (projection p),
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber y]
    simp
  have hr₁₀ (z : Z) : Module.finrank ℂ (U z) = a' * F.rank := by
    obtain ⟨⟨p, y⟩, rfl⟩ := Quotient.exists_rep z
    change Module.finrank ℂ (U (associatedBundleMk G P Y p y)) = a' * F.rank
    rw [← (associatedSphereTensorFiberEquiv S E' σ p y).finrank_eq,
      Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a')) E' (projection p),
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber y]
    simp
  have hr₀₁ (z : Z) : Module.finrank ℂ (T' z) = a * F'.rank := by
    obtain ⟨⟨p, y⟩, rfl⟩ := Quotient.exists_rep z
    change Module.finrank ℂ (T' (associatedBundleMk G P Y p y)) = a * F'.rank
    rw [← (associatedSphereTensorFiberEquiv S E σ' p y).finrank_eq,
      Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a)) E (projection p),
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber y]
    simp
  have hr₁₁ (z : Z) : Module.finrank ℂ (U' z) = a' * F'.rank := by
    obtain ⟨⟨p, y⟩, rfl⟩ := Quotient.exists_rep z
    change Module.finrank ℂ (U' (associatedBundleMk G P Y p y)) = a' * F'.rank
    rw [← (associatedSphereTensorFiberEquiv S E' σ' p y).finrank_eq,
      Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a')) E' (projection p),
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber y]
    simp
  -- Choose one model and one metric transport for each corner, and share them on both sides.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hn₀₀ := A₀₀.exists_native_model_with_atlasMaps (a * F.rank) hr₀₀
  choose N₀₀ hN₀₀ hmaps₀₀ using hn₀₀
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  choose e₀₀ he₀₀ hi₀₀ using hmaps₀₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hnativeMetric₀₀ := A₀₀.exists_native_smoothHermitianMetric l₀₀ hl₀₀
    N₀₀ e₀₀ hi₀₀
  choose k₀₀ hk₀₀ using hnativeMetric₀₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hn₁₀ := A₁₀.exists_native_model_with_atlasMaps (a' * F.rank) hr₁₀
  choose N₁₀ hN₁₀ hmaps₁₀ using hn₁₀
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  choose e₁₀ he₁₀ hi₁₀ using hmaps₁₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hnativeMetric₁₀ := A₁₀.exists_native_smoothHermitianMetric l₁₀ hl₁₀
    N₁₀ e₁₀ hi₁₀
  choose k₁₀ hk₁₀ using hnativeMetric₁₀
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hn₀₁ := A₀₁.exists_native_model_with_atlasMaps (a * F'.rank) hr₀₁
  choose N₀₁ hN₀₁ hmaps₀₁ using hn₀₁
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  choose e₀₁ he₀₁ hi₀₁ using hmaps₀₁
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hnativeMetric₀₁ := A₀₁.exists_native_smoothHermitianMetric l₀₁ hl₀₁
    N₀₁ e₀₁ hi₀₁
  choose k₀₁ hk₀₁ using hnativeMetric₀₁
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hn₁₁ := A₁₁.exists_native_model_with_atlasMaps (a' * F'.rank) hr₁₁
  choose N₁₁ hN₁₁ hmaps₁₁ using hn₁₁
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  choose e₁₁ he₁₁ hi₁₁ using hmaps₁₁
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hnativeMetric₁₁ := A₁₁.exists_native_smoothHermitianMetric l₁₁ hl₁₁
    N₁₁ e₁₁ hi₁₁
  choose k₁₁ hk₁₁ using hnativeMetric₁₁
  -- The full global horizontal adjoints are finite sums for this same principal localization.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hhorizontal₀ := C₀.exists_horizontalLift_integral_adjoint
    S E A σ E' h h' hA ν hν k.toCore
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hhorizontal₁ := C₀.exists_horizontalLift_integral_adjoint
    S E A' σ' E' h h' hA' ν hν k'.toCore
  obtain ⟨β₀, hβ₀, hsβ₀, hβ₀one, H₀', hH₀formula, hH₀⟩ := hhorizontal₀
  obtain ⟨β₁, hβ₁, hsβ₁, hβ₁one, H₁', hH₁formula, hH₁⟩ := hhorizontal₁
  let H₀a := ∑ j, H₀' j
  let H₁a := ∑ j, H₁' j
  have hH₀actual := hH₀ l₀₀ l₁₀ hl₀₀ hl₁₀ hpure₀₀ hpure₁₀
  have hH₁actual := hH₁ l₀₁ l₁₁ hl₀₁ hl₁₁ hpure₀₁ hpure₁₁
  have hV₀actual := hV₀ l₀₀ l₀₁ hl₀₀ hl₀₁ hpure₀₀ hpure₀₁
  have hV₁actual := hV₁ l₁₀ l₁₁ hl₁₀ hl₁₁ hpure₁₀ hpure₁₁
  refine ⟨l₀₀, l₁₀, l₀₁, l₁₁, N₀₀, N₁₀, N₀₁, N₁₁, k₀₀, k₁₀, k₀₁, k₁₁,
    e₀₀, e₁₀, e₀₁, e₁₁, he₀₀, hi₀₀, he₁₀, hi₁₀, he₀₁, hi₀₁, he₁₁, hi₁₁,
    hl₀₀, hl₁₀, hl₀₁, hl₁₁, hN₀₀, hN₁₀, hN₀₁, hN₁₁,
    hpure₀₀, hpure₁₀, hpure₀₁, hpure₁₁, hk₀₀, hk₁₀, hk₀₁, hk₁₁,
    β₀, hβ₀, hsβ₀, hβ₀one, H₀', hH₀formula,
    β₁, hβ₁, hsβ₁, hβ₁one, H₁', hH₁formula,
    H₀a, H₁a, rfl, rfl, hH₀actual, hH₁actual, hV₀actual, hV₁actual, ?_⟩
  -- Both graph closures use these four models and all four proved adjunctions.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hclosed := C₀.exists_closed_horizontalVertical_jointRealizations
    S E A σ hA A' σ' hA' E' QA JA hQA hJA ν hν
    l₀₀ l₁₀ l₀₁ l₁₁ N₀₀ N₁₀ N₀₁ N₁₁ k₀₀ k₁₀ k₀₁ k₁₁
    e₀₀ e₁₀ e₀₁ e₁₁ he₀₀ hi₀₀ he₁₀ hi₁₀ he₀₁ hi₀₁ he₁₁ hi₁₁
    hk₀₀ hk₁₀ hk₀₁ hk₁₁ H₀a H₁a hH₀actual hH₁actual hV₀actual hV₁actual
  exact hclosed

end AtiyahSinger
