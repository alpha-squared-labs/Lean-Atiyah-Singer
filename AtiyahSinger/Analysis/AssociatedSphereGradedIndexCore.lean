/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereGreenIndexSummary

/-!
# The graded Green core and its coefficient index

Public module ID: M0115.

The original four native bundles, metrics and eight corner maps are retained.
The four auxiliary joint graphs are consumed inside this module: their closed
crossing identities give the two smooth-core crossing identities needed for
compact approximation. Only the signed graded pair, its graph and finite-kernel
properties, and its associated coefficient index cross the module boundary.

This is a same-witness consequence of the original Green construction, without
any assumption of the associated-sphere twisted-product index formula.
-/

@[expose] public noncomputable section

set_option Elab.async false

namespace AtiyahSinger

universe u v w w'

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  t2Space_cotangent locallyCompactSpace_cotangent

variable {n r a : ℕ} {P : Type u} {B : Type v} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type w) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
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
  (E' : B → Type w') [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ] [IsFiniteMeasure μ]

local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z

include hk hk' in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 96000000 in
-- The extended limit accommodates elaboration of the same dependent graded Green and kernel data.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates elaboration of the same dependent graded Green and kernel data.
/-- The graded Green pair retains smooth crossing, finite kernels and the coefficient index. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_gradedIndexCore
    (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C₀.baseOperator.IsElliptic)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (ν : Measure Y) [IsFiniteMeasure ν] [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1) (hQell : Q.IsElliptic)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ')
    (L₀ : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L₁ : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (Bpres : SmoothBundlePresentation (n := n) (r := a) E)
    (Bpres' : SmoothBundlePresentation (n := n) (r := a') E')
    (b : Fin Bpres.size → B) (b' : Fin Bpres'.size → B)
    (hb : ∀ j, tsupport (Bpres.cutoff j) ⊆ (S.trivialization (b j)).baseSet)
    (hb' : ∀ j, tsupport (Bpres'.cutoff j) ⊆ (S.trivialization (b' j)).baseSet) :
    let Pbase (j : Fin C₀.size) : PseudodifferentialOperator
        (n := n) (r := a) (q := a') E E' μ 1 :=
      ⟨(C₀.piece j).toLinearMap, (C₀.piece j).isPseudodifferentialOperator 1⟩
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
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
          e₀₀.toHom.linearMap)
        (hi₀₀ : IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
          A₀₀ e₀₀.symm.toHom.linearMap)
        (he₁₀ : IsSmoothAtlasBundleMap A₁₀
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
          e₁₀.toHom.linearMap)
        (hi₁₀ : IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
          A₁₀ e₁₀.symm.toHom.linearMap)
        (he₀₁ : IsSmoothAtlasBundleMap A₀₁
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
          e₀₁.toHom.linearMap)
        (hi₀₁ : IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
          A₀₁ e₀₁.symm.toHom.linearMap)
        (he₁₁ : IsSmoothAtlasBundleMap A₁₁
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
          e₁₁.toHom.linearMap)
        (hi₁₁ : IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
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
        let S₀₀ := (atlasSmoothSectionEquiv A₀₀
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
          e₀₀ he₀₀ hi₀₀).trans
            (nativeSmoothSectionLinearEquiv (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
        let i₀₀ := (k₀₀.smoothToL2 η).comp S₀₀.toLinearMap
        let S₁₀ := (atlasSmoothSectionEquiv A₁₀
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
          e₁₀ he₁₀ hi₁₀).trans
            (nativeSmoothSectionLinearEquiv (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
        let i₁₀ := (k₁₀.smoothToL2 η).comp S₁₀.toLinearMap
        let S₀₁ := (atlasSmoothSectionEquiv A₀₁
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
          e₀₁ he₀₁ hi₀₁).trans
            (nativeSmoothSectionLinearEquiv (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
        let i₀₁ := (k₀₁.smoothToL2 η).comp S₀₁.toLinearMap
        let S₁₁ := (atlasSmoothSectionEquiv A₁₁
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
          e₁₁ he₁₁ hi₁₁).trans
            (nativeSmoothSectionLinearEquiv (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
        let i₁₁ := (k₁₁.smoothToL2 η).comp S₁₁.toLinearMap
        let X₀ := k₀₀.L2SectionSpace η
        let X₁ := k₁₁.L2SectionSpace η
        let Y₀ := k₁₀.L2SectionSpace η
        let Y₁ := k₀₁.L2SectionSpace η
        let Even := WithLp 2 (X₀ × X₁)
        let Odd := WithLp 2 (Y₀ × Y₁)
        let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ
          (X₀) (X₁)
        let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ
          (Y₀) (Y₁)
        let iEven : (A₀₀.smoothSections × A₁₁.smoothSections) →ₗ[ℂ] Even :=
          cEven.symm.toLinearMap.comp (i₀₀.prodMap i₁₁)
        let dSmooth : (A₀₀.smoothSections × A₁₁.smoothSections) →ₗ[ℂ] Odd :=
          cOdd.symm.toLinearMap.comp
          (((i₁₀.comp H₀).coprod (-(i₁₀.comp V₁a))).prod
            ((i₀₁.comp V₀).coprod (i₀₁.comp H₁a)))
        let jOdd := cOdd.symm.toLinearMap.comp (i₁₀.prodMap i₀₁)
        let aSmooth := cEven.symm.toLinearMap.comp
          (((i₀₀.comp H₀a).coprod (i₀₀.comp V₀a)).prod
            ((-(i₁₁.comp V₁)).coprod (i₁₁.comp H₁)))
        ∃ (L : Even →ₗ.[ℂ] Odd) (La : Odd →ₗ.[ℂ] Even),
          L.IsClosed ∧ La.IsClosed ∧
          L.graph = (iEven.prod dSmooth).range.topologicalClosure ∧
          La.graph = (jOdd.prod aSmooth).range.topologicalClosure ∧
          L.IsFormalAdjoint La ∧
          (∀ (s : A₀₀.smoothSections) (t : A₁₁.smoothSections),
            inner ℂ ((i₁₀.comp H₀) s) ((i₁₀.comp V₁a) t) =
              inner ℂ ((i₀₁.comp V₀) s) ((i₀₁.comp H₁a) t)) ∧
          (∀ (s : A₁₀.smoothSections) (t : A₀₁.smoothSections),
            inner ℂ ((i₀₀.comp H₀a) s) ((i₀₀.comp V₀a) t) =
              inner ℂ ((i₁₁.comp V₁) s) ((i₁₁.comp H₁) t)) ∧
          IsClosed (L.toFun.range : Set Odd) ∧
          FiniteDimensional ℂ L.ker ∧
          IsClosed (La.toFun.range : Set Even) ∧
          FiniteDimensional ℂ La.ker ∧
          ∀ (g : SmoothCotangentMetric (n := n) (M := B))
            (p : AtlasSymbolFunction (n := n) E E'),
            let B₀ := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
            let B₁ := nativeSmoothComplexBundleAtlas (n := n) (r := a') E'
            ∀ (hs : IsSmoothOffZeroAtlasSymbol B₀ B₁ p)
              (hh : IsHomogeneousAtlasSymbol 1 p) (hi : IsEllipticAtlasSymbol p),
              C₀.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
                atlasGlobalPrincipalSymbolClass B₀ B₁ 1
                  (atlasRegularizedSymbol B₀ B₁ g 1 p hs hh) →
              analyticIndexOfComponents μ
                (complexKZeroCompactSupportAction
                  (cotangentProjection (n := n) (M := B))
                  (associatedRepresentationKZero S.toIsPrincipalBundle
                    (Q.smoothEquivariantAnalyticIndex IG σ σ' hσ hσ' hQ hQell))
                  (atlasSymbolKClass B₀ B₁ p hs hi)) =
                (Module.finrank ℂ L.ker : ℤ) - Module.finrank ℂ La.ker := by
  classical
  intro Pbase Jbase Kbase
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  intro A A' hA hA' QA JA
  -- Obtain all geometric and adjoint witnesses once from the original joint construction.
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hactual := C₀.exists_associated_gradedIndexSummary
    S E F F' σ σ' hσ hσ' k k' hk hk' E' hC h h' ν hν Q hQell hQ
      L₀ L₁ Bpres Bpres' b b' hb hb'
  obtain ⟨hQA, hJA, hactual⟩ := hactual
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
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
  intro η A₀₀ A₁₀ A₀₁ A₁₁ H₀ H₁ V₀ V₁ V₀a V₁a
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  obtain ⟨l₀₀, l₁₀, l₀₁, l₁₁, N₀₀, N₁₀, N₀₁, N₁₁, k₀₀, k₁₀, k₀₁, k₁₁, hactual⟩ := hactual
  -- Commit the original models before unpacking their certificates.
  refine ⟨l₀₀, l₁₀, l₀₁, l₁₁, N₀₀, N₁₀, N₀₁, N₁₁, k₀₀, k₁₀, k₀₁, k₁₁, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  obtain ⟨e₀₀, e₁₀, e₀₁, e₁₁, he₀₀, hi₀₀, he₁₀, hi₁₀, he₀₁, hi₀₁, he₁₁, hi₁₁, hactual⟩ := hactual
  refine ⟨e₀₀, e₁₀, e₀₁, e₁₁, he₀₀, hi₀₀, he₁₀, hi₁₀, he₀₁, hi₀₁, he₁₁, hi₁₁, ?_⟩
  obtain ⟨hl₀₀, hl₁₀, hl₀₁, hl₁₁, hN₀₀, hN₁₀, hN₀₁, hN₁₁, hpure₀₀, hpure₁₀, hpure₀₁, hpure₁₁, hk₀₀,
    hk₁₀, hk₀₁, hk₁₁, hactual⟩ := hactual
  refine ⟨hl₀₀, hl₁₀, hl₀₁, hl₁₁, hN₀₀, hN₁₀, hN₀₁, hN₁₁,
    hpure₀₀, hpure₁₀, hpure₀₁, hpure₁₁, hk₀₀, hk₁₀, hk₀₁, hk₁₁, ?_⟩
  -- Both backward maps retain the original cutoffs, pieces, and complete adjunctions.
  obtain ⟨β₀, hβ₀, hsβ₀, hβ₀one, H₀', hH₀formula, β₁, hβ₁, hsβ₁, hβ₁one, H₁', hH₁formula, H₀a, H₁a,
    hH₀sum, hH₁sum, hH₀, hH₁, hV₀, hV₁, hactual⟩ := hactual
  refine ⟨β₀, hβ₀, hsβ₀, hβ₀one, H₀', hH₀formula,
    β₁, hβ₁, hsβ₁, hβ₁one, H₁', hH₁formula,
    H₀a, H₁a, hH₀sum, hH₁sum, hH₀, hH₁, hV₀, hV₁, ?_⟩
  intro S₀₀ i₀₀ S₁₀ i₁₀ S₀₁ i₀₁ S₁₁ i₁₁ X₀ X₁ Y₀ Y₁ Even Odd
    cEven cOdd iEven dSmooth jOdd aSmooth
  -- Keep L and La from the same joint-graph certificate while consuming its auxiliary graphs.
  obtain ⟨R₀, R₁, hgraph₀, _hclosed₀, _hdense₀, hgraph₁, _hclosed₁, _hdense₁,
    hcross, L, hLclosed, _hLdense, hLgraph, _hLdom, _hLker, _hL, _hsmoothKer,
    hactual⟩ := hactual
  obtain ⟨R₁₀, R₀₁, hR₁₀, _hc₁₀, _hd₁₀, hR₀₁, _hc₀₁, _hd₀₁,
    hcrossOdd, hactual⟩ := hactual
  obtain ⟨La, hLaclosed, _hLadense, _hLadom, _hLaker, hLagraph, hformal,
    hactual⟩ := hactual
  -- Smooth graph points lie in the specified joint graphs, so closed crossing restricts to them.
  have hcrossSmooth (s : A₀₀.smoothSections) (t : A₁₁.smoothSections) :
      inner ℂ ((i₁₀.comp H₀) s) ((i₁₀.comp V₁a) t) =
        inner ℂ ((i₀₁.comp V₀) s) ((i₀₁.comp H₁a) t) := by
    have hs : (i₀₀ s, ((i₁₀.comp H₀) s, (i₀₁.comp V₀) s)) ∈ R₀.graph := by
      rw [hgraph₀]
      exact (i₀₀.prod ((i₁₀.comp H₀).prod (i₀₁.comp V₀))).range.le_topologicalClosure ⟨s, rfl⟩
    have ht : (i₁₁ t, ((i₁₀.comp V₁a) t, (i₀₁.comp H₁a) t)) ∈ R₁.graph := by
      rw [hgraph₁]
      exact (i₁₁.prod ((i₁₀.comp V₁a).prod (i₀₁.comp H₁a))).range.le_topologicalClosure ⟨t, rfl⟩
    obtain ⟨u, _hu, hRu⟩ := R₀.mem_graph_iff.mp hs
    obtain ⟨v, _hv, hRv⟩ := R₁.mem_graph_iff.mp ht
    simpa only [hRu, hRv] using hcross u v
  -- The opposite signed pair uses its original two joint graphs and the same native cores.
  have hcrossOddSmooth (s : A₁₀.smoothSections) (t : A₀₁.smoothSections) :
      inner ℂ ((i₀₀.comp H₀a) s) ((i₀₀.comp V₀a) t) =
        inner ℂ ((i₁₁.comp V₁) s) ((i₁₁.comp H₁) t) := by
    have hs : (i₁₀ s, ((i₀₀.comp H₀a) s, (i₁₁.comp V₁) s)) ∈ R₁₀.graph := by
      rw [hR₁₀]
      exact (i₁₀.prod ((i₀₀.comp H₀a).prod (i₁₁.comp V₁))).range.le_topologicalClosure ⟨s, rfl⟩
    have ht : (i₀₁ t, ((i₀₀.comp V₀a) t, (i₁₁.comp H₁) t)) ∈ R₀₁.graph := by
      rw [hR₀₁]
      exact (i₀₁.prod ((i₀₀.comp V₀a).prod (i₁₁.comp H₁))).range.le_topologicalClosure ⟨t, rfl⟩
    obtain ⟨u, _hu, hRu⟩ := R₁₀.mem_graph_iff.mp hs
    obtain ⟨v, _hv, hRv⟩ := R₀₁.mem_graph_iff.mp ht
    simpa only [hRu, hRv] using hcrossOdd u v
  -- Closed range, finite kernels and the coefficient index concern this literal same pair.
  exact ⟨L, La, hLclosed, hLaclosed, hLgraph, hLagraph, hformal,
    hcrossSmooth, hcrossOddSmooth, hactual⟩

end AtiyahSinger
