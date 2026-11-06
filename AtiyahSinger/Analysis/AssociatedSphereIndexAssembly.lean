/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGradedKernelGreenConstruction
public import AtiyahSinger.Analysis.AssociatedCoefficientIndex
public import AtiyahSinger.Analysis.HermitianMetricAdjointKernel
public import AtiyahSinger.Analysis.IndexIntertwining
public import AtiyahSinger.Analysis.SmoothEquivariantIndex
public import AtiyahSinger.Topology.AssociatedKZero

/-!
# The associated graded kernels and their coefficient index

Public module ID: M0118.

The proof obtains the graded Green certificate once and retains its graphs,
metrics, coefficient representations and kernel maps. Parametrices and the
fixed smooth conjugations identify the graded kernel-dimension difference with
the difference of the associated coefficient indices. The positive coefficient
representation comes from the kernel of Q; the negative one comes from the
kernel of its metric formal adjoint.

The same representation difference then gives the coefficient action on the
base symbol class. The regularized cutoff comparison is handled separately.
-/

@[expose] public noncomputable section

set_option Elab.async false


/- This is the standard auxiliary-theorem construction with explicit expansion of
free local let values. The resulting closed declaration is checked by Lean's kernel. -/
open Lean Elab Tactic Meta in
local elab "as_aux_lemma_zeta" " => " s:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic s)
  unless remaining.isEmpty do
    throwError "Cannot abstract an unfinished proof"
  let value ← instantiateMVars (mkMVar goal)
  if value.hasSorry then
    throwError "Cannot abstract a proof containing a recovery placeholder"
  let value ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign value

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
-- The extended limit accommodates the dependent Green data and the two coefficient-index
-- comparisons.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the dependent Green data and the two coefficient-index
-- comparisons.
/-- The same actual graded Green kernels compute the two associated coefficient indices. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_gradedKernelIndexRealization
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
        let Joint₀ := X₀ →ₗ.[ℂ] (Y₀ × Y₁)
        let Joint₁ := X₁ →ₗ.[ℂ] (Y₀ × Y₁)
        let Graded := Even →ₗ.[ℂ] Odd
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
        ∃ (R₀ : Joint₀)
          (R₁ : Joint₁),
          R₀.graph = (i₀₀.prod ((i₁₀.comp H₀).prod (i₀₁.comp V₀))).range.topologicalClosure ∧
          R₀.IsClosed ∧ Dense (R₀.domain : Set (X₀)) ∧
          R₁.graph = (i₁₁.prod ((i₁₀.comp V₁a).prod (i₀₁.comp H₁a))).range.topologicalClosure ∧
          R₁.IsClosed ∧ Dense (R₁.domain : Set (X₁)) ∧
          (∀ (u : R₀.domain) (v : R₁.domain),
            inner ℂ (R₀ u).1 (R₁ v).1 = inner ℂ (R₀ u).2 (R₁ v).2) ∧
          ∃ L : Graded,
            L.IsClosed ∧ Dense (L.domain : Set Even) ∧
            L.graph = (iEven.prod dSmooth).range.topologicalClosure ∧
            L.domain = (R₀.domain.prod R₁.domain).comap cEven.toLinearMap ∧
            L.ker = (R₀.ker.prod R₁.ker).comap cEven.toLinearMap ∧
            (∀ (u : R₀.domain) (v : R₁.domain),
              (WithLp.toLp 2 (u.val, v.val),
                WithLp.toLp 2 ((R₀ u).1 - (R₁ v).1, (R₀ u).2 + (R₁ v).2)) ∈ L.graph) ∧
            (∀ (s : A₀₀.smoothSections) (t : A₁₁.smoothSections),
              iEven (s, t) ∈ L.ker ↔
                (H₀ s = 0 ∧ V₀ s = 0) ∧ (V₁a t = 0 ∧ H₁a t = 0)) ∧
            ∃ (R₁₀ : k₁₀.L2SectionSpace η →ₗ.[ℂ]
                (k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η))
              (R₀₁ : k₀₁.L2SectionSpace η →ₗ.[ℂ]
                (k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η)),
              R₁₀.graph =
                (i₁₀.prod ((i₀₀.comp H₀a).prod (i₁₁.comp V₁))).range.topologicalClosure ∧
              R₁₀.IsClosed ∧ Dense (R₁₀.domain : Set (k₁₀.L2SectionSpace η)) ∧
              R₀₁.graph =
                (i₀₁.prod ((i₀₀.comp V₀a).prod (i₁₁.comp H₁))).range.topologicalClosure ∧
              R₀₁.IsClosed ∧ Dense (R₀₁.domain : Set (k₀₁.L2SectionSpace η)) ∧
              (∀ (u : R₁₀.domain) (v : R₀₁.domain),
                inner ℂ (R₁₀ u).1 (R₀₁ v).1 = inner ℂ (R₁₀ u).2 (R₀₁ v).2) ∧
              let jOdd := cOdd.symm.toLinearMap.comp (i₁₀.prodMap i₀₁)
              let aSmooth := cEven.symm.toLinearMap.comp
                (((i₀₀.comp H₀a).coprod (i₀₀.comp V₀a)).prod
                  ((-(i₁₁.comp V₁)).coprod (i₁₁.comp H₁)))
              ∃ La : Odd →ₗ.[ℂ] Even,
                La.IsClosed ∧ Dense (La.domain : Set Odd) ∧
                La.domain = (R₁₀.domain.prod R₀₁.domain).comap cOdd.toLinearMap ∧
                La.ker = (R₁₀.ker.prod R₀₁.ker).comap cOdd.toLinearMap ∧
                La.graph = (jOdd.prod aSmooth).range.topologicalClosure ∧
                L.IsFormalAdjoint La ∧
              ∃ ρ ρp : FiniteContinuousRepresentation G,
                ∃ (en : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ]
                    (Q.metricFormalAdjoint k k').toLinearMap.ker)
                  (enp : (Fin ρp.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker),
                  (∀ (g : G) (v : Fin ρ.dimension → ℂ),
                    (en (ρ.representation g v)).val =
                      σ'.smoothSectionRepresentation IG hσ' g (en v).val) ∧
                  (∀ (g : G) (v : Fin ρp.dimension → ℂ),
                    (enp (ρp.representation g v)).val =
                      σ.smoothSectionRepresentation IG hσ g (enp v).val) ∧
                  ∃ (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] JA.toLinearMap.ker)
                    (ep : (Fin ρp.dimension → ℂ) ≃ₗ[ℂ] QA.toLinearMap.ker),
                    (∀ v y, (e v).val.val y = (en v).val.val y) ∧
                    (∀ v y, (ep v).val.val y = (enp v).val.val y) ∧
                    (∀ (g : G) (y : Y) (v : Fin ρ.dimension → ℂ),
                      (e (ρ.representation g v)).val.val (g • y) =
                        σ'.linearMap g y ((e v).val.val y)) ∧
                    (∀ (g : G) (y : Y) (v : Fin ρp.dimension → ℂ),
                      (ep (ρp.representation g v)).val.val (g • y) =
                        σ.linearMap g y ((ep v).val.val y)) ∧
                    let K := AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
                    let Kp := AssociatedVectorFiber S.toIsPrincipalBundle ρp.representation
                    let C := fun x : B ↦ E x ⊗[ℂ] K x
                    let C' := fun x : B ↦ E' x ⊗[ℂ] K x
                    let Cp := fun x : B ↦ E x ⊗[ℂ] Kp x
                    let Cp' := fun x : B ↦ E' x ⊗[ℂ] Kp x
                    letI : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
                    letI : TopologicalSpace (TotalSpace Unit C') :=
                      tensorTopology (E := E') (F := K)
                    letI : TopologicalSpace (TotalSpace Unit Cp) :=
                      tensorTopology (E := E) (F := Kp)
                    letI : TopologicalSpace (TotalSpace Unit Cp') :=
                      tensorTopology (E := E') (F := Kp)
                    let AC := tensorSmoothAtlas
                      (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
                        (associatedOrthogonalRepresentationAtlas S ρ)
                    let AC' := tensorSmoothAtlas
                      (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
                        (associatedOrthogonalRepresentationAtlas S ρ)
                    let AK₀ := tensorSmoothAtlas
                      (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
                        (associatedOrthogonalRepresentationAtlas S ρp)
                    let AK₁ := tensorSmoothAtlas
                      (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
                        (associatedOrthogonalRepresentationAtlas S ρp)
                    let Pc := C₀.coefficientOperator S E E' ρ
                    let Pcp := C₀.coefficientOperator S E E' ρp
        ∃ (d₀ : ContinuousHermitianMetric Cp) (d₁ : ContinuousHermitianMetric Cp')
          (ND₀ ND₁ : SmoothFiniteComplexBundle (n := n) B)
          (kD₀ : SmoothHermitianMetric (n := n) (r := ND₀.rank) ND₀.Fiber)
          (kD₁ : SmoothHermitianMetric (n := n) (r := ND₁.rank) ND₁.Fiber)
          (c₀ : ContinuousHermitianMetric C) (c₁ : ContinuousHermitianMetric C')
          (NC₀ NC₁ : SmoothFiniteComplexBundle (n := n) B)
          (kC₀ : SmoothHermitianMetric (n := n) (r := NC₀.rank) NC₀.Fiber)
          (kC₁ : SmoothHermitianMetric (n := n) (r := NC₁.rank) NC₁.Fiber),
          letI := modelTopology (EuclideanSpace ℂ (Fin ND₀.rank)) ND₀.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin ND₁.rank)) ND₁.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
          ∃ (dIso₀ : Iso Cp ND₀.Fiber) (dIso₁ : Iso Cp' ND₁.Fiber)
            (heD₀ : IsSmoothAtlasBundleMap AK₀
              (nativeSmoothComplexBundleAtlas ND₀.Fiber) dIso₀.toHom.linearMap)
            (hiD₀ : IsSmoothAtlasBundleMap
              (nativeSmoothComplexBundleAtlas ND₀.Fiber) AK₀ dIso₀.symm.toHom.linearMap)
            (heD₁ : IsSmoothAtlasBundleMap AK₁
              (nativeSmoothComplexBundleAtlas ND₁.Fiber) dIso₁.toHom.linearMap)
            (hiD₁ : IsSmoothAtlasBundleMap
              (nativeSmoothComplexBundleAtlas ND₁.Fiber) AK₁ dIso₁.symm.toHom.linearMap)
            (cIso₀ : Iso C NC₀.Fiber) (cIso₁ : Iso C' NC₁.Fiber)
            (heC₀ : IsSmoothAtlasBundleMap AC
              (nativeSmoothComplexBundleAtlas NC₀.Fiber) cIso₀.toHom.linearMap)
            (hiC₀ : IsSmoothAtlasBundleMap
              (nativeSmoothComplexBundleAtlas NC₀.Fiber) AC cIso₀.symm.toHom.linearMap)
            (heC₁ : IsSmoothAtlasBundleMap AC'
              (nativeSmoothComplexBundleAtlas NC₁.Fiber) cIso₁.toHom.linearMap)
            (hiC₁ : IsSmoothAtlasBundleMap
              (nativeSmoothComplexBundleAtlas NC₁.Fiber) AC' cIso₁.symm.toHom.linearMap),
            AK₀.IsSmoothHermitianMetric d₀ ∧ AK₁.IsSmoothHermitianMetric d₁ ∧
            AC.IsSmoothHermitianMetric c₀ ∧ AC'.IsSmoothHermitianMetric c₁ ∧
            ND₀.rank = a * ρp.dimension ∧ ND₁.rank = a' * ρp.dimension ∧
            NC₀.rank = a * ρ.dimension ∧ NC₁.rank = a' * ρ.dimension ∧
            (∀ (x : B) (u v : Cp x),
              kD₀.pairing x (dIso₀.linearEquiv x u) (dIso₀.linearEquiv x v) =
                (d₀.toCore x).inner u v) ∧
            (∀ (x : B) (u v : Cp' x),
              kD₁.pairing x (dIso₁.linearEquiv x u) (dIso₁.linearEquiv x v) =
                (d₁.toCore x).inner u v) ∧
            (∀ (x : B) (u v : C x),
              kC₀.pairing x (cIso₀.linearEquiv x u) (cIso₀.linearEquiv x v) =
                (c₀.toCore x).inner u v) ∧
            (∀ (x : B) (u v : C' x),
              kC₁.pairing x (cIso₁.linearEquiv x u) (cIso₁.linearEquiv x v) =
                (c₁.toCore x).inner u v) ∧
            (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
              (c₀.toCore (projection p)).inner
                  (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                  (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
                h.pairing (projection p) u v *
                  ∫ y, k'.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) ∧
            (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρ.dimension → ℂ),
              (c₁.toCore (projection p)).inner
                  (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                  (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
                h'.pairing (projection p) u v *
                  ∫ y, k'.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) ∧
            (∀ (p : P) (u v : E (projection p)) (s t : Fin ρp.dimension → ℂ),
              (d₀.toCore (projection p)).inner
                  (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation p rfl s)
                  (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation
                      p rfl t) =
                h.pairing (projection p) u v *
                  ∫ y, k.pairing y ((ep s).val.val y) ((ep t).val.val y) ∂ν) ∧
            (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρp.dimension → ℂ),
              (d₁.toCore (projection p)).inner
                  (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation p rfl s)
                  (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation
                      p rfl t) =
                h'.pairing (projection p) u v *
                  ∫ y, k.pairing y ((ep s).val.val y) ((ep t).val.val y) ∂ν) ∧
            let SD₀ := (atlasSmoothSectionEquiv AK₀
              (nativeSmoothComplexBundleAtlas ND₀.Fiber) dIso₀ heD₀ hiD₀).trans
                (nativeSmoothSectionLinearEquiv ND₀.Fiber)
            let SD₁ := (atlasSmoothSectionEquiv AK₁
              (nativeSmoothComplexBundleAtlas ND₁.Fiber) dIso₁ heD₁ hiD₁).trans
                (nativeSmoothSectionLinearEquiv ND₁.Fiber)
            let S₀ := (atlasSmoothSectionEquiv AC
              (nativeSmoothComplexBundleAtlas NC₀.Fiber) cIso₀ heC₀ hiC₀).trans
                (nativeSmoothSectionLinearEquiv NC₀.Fiber)
            let S₁ := (atlasSmoothSectionEquiv AC'
              (nativeSmoothComplexBundleAtlas NC₁.Fiber) cIso₁ heC₁ hiC₁).trans
                (nativeSmoothSectionLinearEquiv NC₁.Fiber)
            ∃ ev : Hom ((πS : Z → B) *ᵖ K) D',
              (∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
                ev.linearMap (associatedBundleMk G P Y p y)
                    (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
                  associatedEquivariantFiberMk S.toIsPrincipalBundle σ' p y rfl ((e v).val.val y)) ∧
              ∃ (Φ : AC.smoothSections ≃ₗ[ℂ] V₀a.ker) (Ψ : AC'.smoothSections ≃ₗ[ℂ] V₁a.ker),
                (∀ u z, (Φ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                (∀ u z, (Ψ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                ∃ Pn : PseudodifferentialOperator (n := n) (r := NC₀.rank) (q := NC₁.rank)
                    NC₀.Fiber NC₁.Fiber μ 1,
                  Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
                  Pn.IsElliptic ∧
                  ∃ evp : Hom ((πS : Z → B) *ᵖ Kp) D,
                    (∀ (p : P) (y : Y) (v : Fin ρp.dimension → ℂ),
                      evp.linearMap (associatedBundleMk G P Y p y)
                          (associatedVectorFiberMk S.toIsPrincipalBundle
                            ρp.representation p rfl v) =
                        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl
                          ((ep v).val.val y)) ∧
                    ∃ (Φp : AK₀.smoothSections ≃ₗ[ℂ] V₀.ker)
                      (Ψp : AK₁.smoothSections ≃ₗ[ℂ] V₁.ker),
                      (∀ u z, (Φp u).val.val z =
                        TensorProduct.map LinearMap.id (evp.linearMap z) (u.val (πS z))) ∧
                      (∀ u z, (Ψp u).val.val z =
                        TensorProduct.map LinearMap.id (evp.linearMap z) (u.val (πS z))) ∧
                      ∃ Pp : PseudodifferentialOperator
                          (n := n) (r := ND₀.rank) (q := ND₁.rank) ND₀.Fiber ND₁.Fiber μ 1,
                        Pp.toLinearMap =
                          SD₁.toLinearMap.comp (Pcp.toLinearMap.comp SD₀.symm.toLinearMap) ∧
                        Pp.IsElliptic ∧
                        ∃ (κ₀₀ : Pp.toLinearMap.ker ≃ₗ[ℂ] R₀.ker)
                          (κ₁₀ : (Pp.metricFormalAdjoint kD₀ kD₁).toLinearMap.ker ≃ₗ[ℂ] R₁₀.ker)
                          (κ₀₁ : Pn.toLinearMap.ker ≃ₗ[ℂ] R₀₁.ker)
                          (κ₁₁ : (Pn.metricFormalAdjoint kC₀ kC₁).toLinearMap.ker ≃ₗ[ℂ] R₁.ker),
                          (∀ u, (κ₀₀ u).val = i₀₀ (Φp (SD₀.symm u.val)).val) ∧
                          (∀ u, (κ₁₀ u).val = i₁₀ (Ψp (SD₁.symm u.val)).val) ∧
                          (∀ u, (κ₀₁ u).val = i₀₁ (Φ (S₀.symm u.val)).val) ∧
                          (∀ u, (κ₁₁ u).val = i₁₁ (Ψ (S₁.symm u.val)).val) ∧
                          ∃ c₀₀ c₁₀ c₀₁ c₁₁ : ℝ,
                            0 ≤ c₀₀ ∧ 0 ≤ c₁₀ ∧ 0 ≤ c₀₁ ∧ 0 ≤ c₁₁ ∧
                            (∀ u : R₀.domain,
                              (u : k₀₀.L2SectionSpace η) ∈ R₀.ker.orthogonal →
                              ‖(u : k₀₀.L2SectionSpace η)‖ ≤ c₀₀ * ‖R₀ u‖) ∧
                            (∀ u : R₁₀.domain,
                              (u : k₁₀.L2SectionSpace η) ∈ R₁₀.ker.orthogonal →
                              ‖(u : k₁₀.L2SectionSpace η)‖ ≤ c₁₀ * ‖R₁₀ u‖) ∧
                            (∀ u : R₀₁.domain,
                              (u : k₀₁.L2SectionSpace η) ∈ R₀₁.ker.orthogonal →
                              ‖(u : k₀₁.L2SectionSpace η)‖ ≤ c₀₁ * ‖R₀₁ u‖) ∧
                            (∀ u : R₁.domain,
                              (u : k₁₁.L2SectionSpace η) ∈ R₁.ker.orthogonal →
                              ‖(u : k₁₁.L2SectionSpace η)‖ ≤ c₁₁ * ‖R₁ u‖) ∧
                            IsClosed (R₀.toFun.range : Set
                              (k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η)) ∧
                            IsClosed (R₁₀.toFun.range : Set
                              (k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η)) ∧
                            IsClosed (R₀₁.toFun.range : Set
                              (k₀₀.L2SectionSpace η × k₁₁.L2SectionSpace η)) ∧
                            IsClosed (R₁.toFun.range : Set
                              (k₁₀.L2SectionSpace η × k₀₁.L2SectionSpace η)) ∧
                            FiniteDimensional ℂ R₀.ker ∧ FiniteDimensional ℂ R₁₀.ker ∧
                            FiniteDimensional ℂ R₀₁.ker ∧ FiniteDimensional ℂ R₁.ker ∧
                            IsClosed (L.toFun.range : Set Odd) ∧
                            FiniteDimensional ℂ L.ker ∧
                            IsClosed (La.toFun.range : Set Even) ∧
                            FiniteDimensional ℂ La.ker ∧
                            (Module.finrank ℂ L.ker : ℤ) - Module.finrank ℂ La.ker =
                              Pcp.toLinearMap.index - Pc.toLinearMap.index ∧
                            Q.smoothEquivariantAnalyticIndex IG σ σ' hσ hσ' hQ hQell =
                              finiteRepresentationClass ρp - finiteRepresentationClass ρ ∧
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
  as_aux_lemma_zeta =>
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
    have hactual := C₀.exists_associated_gradedKernelGreenRealization
      S E F F' σ σ' hσ hσ' k k' hk hk' E' hC h h' ν hν Q hQell hQ
        L₀ L₁ Bpres Bpres' b b' hb hb'
    have hQA : QA.IsEquivariant IG σ σ' hA hA' := hactual.choose
    have hactual := hactual.choose_spec
    have hJA : JA.IsEquivariant IG σ' σ hA' hA := hactual.choose
    have hactual := hactual.choose_spec
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
    choose l₀₀ l₁₀ l₀₁ l₁₁ N₀₀ N₁₀ N₀₁ N₁₁ k₀₀ k₁₀ k₀₁ k₁₁ hactual using hactual
    -- Commit the original models before unpacking their certificates.
    refine ⟨l₀₀, l₁₀, l₀₁, l₁₁, N₀₀, N₁₀, N₀₁, N₁₁, k₀₀, k₁₀, k₀₁, k₁₁, ?_⟩
    let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    choose e₀₀ e₁₀ e₀₁ e₁₁ he₀₀ hi₀₀ he₁₀ hi₁₀ he₀₁ hi₀₁ he₁₁ hi₁₁ hactual using hactual
    refine ⟨e₀₀, e₁₀, e₀₁, e₁₁, he₀₀, hi₀₀, he₁₀, hi₁₀, he₀₁, hi₀₁, he₁₁, hi₁₁, ?_⟩
    choose hl₀₀ hl₁₀ hl₀₁ hl₁₁ hN₀₀ hN₁₀ hN₀₁ hN₁₁ hpure₀₀ hpure₁₀ hpure₀₁ hpure₁₁ hk₀₀ hk₁₀
      hk₀₁ hk₁₁ hactual using hactual
    refine ⟨hl₀₀, hl₁₀, hl₀₁, hl₁₁, hN₀₀, hN₁₀, hN₀₁, hN₁₁,
      hpure₀₀, hpure₁₀, hpure₀₁, hpure₁₁, hk₀₀, hk₁₀, hk₀₁, hk₁₁, ?_⟩
    -- Both backward maps retain the original cutoffs, pieces, and complete adjunctions.
    choose β₀ hβ₀ hsβ₀ hβ₀one H₀' hH₀formula β₁ hβ₁ hsβ₁ hβ₁one H₁' hH₁formula H₀a H₁a
      hH₀sum hH₁sum hH₀ hH₁ hV₀ hV₁ hactual using hactual
    refine ⟨β₀, hβ₀, hsβ₀, hβ₀one, H₀', hH₀formula,
      β₁, hβ₁, hsβ₁, hβ₁one, H₁', hH₁formula,
      H₀a, H₁a, hH₀sum, hH₁sum, hH₀, hH₁, hV₀, hV₁, ?_⟩
    intro S₀₀ i₀₀ S₁₀ i₁₀ S₀₁ i₀₁ S₁₁ i₁₁ X₀ X₁ Y₀ Y₁ Even Odd Joint₀ Joint₁ Graded
      cEven cOdd iEven dSmooth
    choose R₀ R₁ hgraph₀ hclosed₀ hdense₀ hgraph₁ hclosed₁ hdense₁ hcross L hLclosed hLdense
      hLgraph hLdom hLker hL hsmoothKer hactual using hactual
    refine ⟨R₀, R₁, hgraph₀, hclosed₀, hdense₀, hgraph₁, hclosed₁, hdense₁,
      hcross, L, hLclosed, hLdense, hLgraph, hLdom, hLker, hL, hsmoothKer, ?_⟩
    -- Retain the same opposite graphs and literal signed adjoint from the actual call.
    choose R₁₀ R₀₁ hR₁₀ hc₁₀ hd₁₀ hR₀₁ hc₀₁ hd₀₁ hcrossOdd hactual using hactual
    refine ⟨R₁₀, R₀₁, hR₁₀, hc₁₀, hd₁₀, hR₀₁, hc₀₁, hd₀₁, hcrossOdd, ?_⟩
    intro jOdd aSmooth
    choose La hLaclosed hLadense hLadom hLaker hLagraph hformal hactual using hactual
    refine ⟨La, hLaclosed, hLadense, hLadom, hLaker, hLagraph, hformal, ?_⟩
    choose ρ ρp en enp hen henp e ep hevalue hepvalue he hep hactual using hactual
    refine ⟨ρ, ρp, en, enp, hen, henp, e, ep, hevalue, hepvalue, he, hep, ?_⟩
    intro K Kp C C' Cp Cp'
    let : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
    let : TopologicalSpace (TotalSpace Unit C') := tensorTopology (E := E') (F := K)
    let : TopologicalSpace (TotalSpace Unit Cp) := tensorTopology (E := E) (F := Kp)
    let : TopologicalSpace (TotalSpace Unit Cp') := tensorTopology (E := E') (F := Kp)
    intro AC AC' AK₀ AK₁ Pc Pcp
    choose d₀ d₁ ND₀ ND₁ kD₀ kD₁ c₀ c₁ NC₀ NC₁ kC₀ kC₁ hactual using hactual
    refine ⟨d₀, d₁, ND₀, ND₁, kD₀, kD₁, c₀, c₁, NC₀, NC₁, kC₀, kC₁, ?_⟩
    let := modelTopology (EuclideanSpace ℂ (Fin ND₀.rank)) ND₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin ND₁.rank)) ND₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
    choose dIso₀ dIso₁ heD₀ hiD₀ heD₁ hiD₁ cIso₀ cIso₁ heC₀ hiC₀ heC₁ hiC₁ hd₀ hd₁ hc₀ hc₁ hrD₀
      hrD₁ hrC₀ hrC₁ hmD₀ hmD₁ hmC₀ hmC₁ hgramC₀ hgramC₁ hgramD₀ hgramD₁ hactual using hactual
    refine ⟨dIso₀, dIso₁, heD₀, hiD₀, heD₁, hiD₁, cIso₀, cIso₁,
      heC₀, hiC₀, heC₁, hiC₁, hd₀, hd₁, hc₀, hc₁, hrD₀, hrD₁, hrC₀, hrC₁,
      hmD₀, hmD₁, hmC₀, hmC₁, hgramC₀, hgramC₁, hgramD₀, hgramD₁, ?_⟩
    intro SD₀ SD₁ S₀ S₁
    choose ev hev Φ Ψ hΦ hΨ Pn hPn hPnEll evp hevp Φp Ψp hΦp hΨp Pp hPp hPpEll κ₀₀ κ₁₀ κ₀₁ κ₁₁
      hκ₀₀ hκ₁₀ hκ₀₁ hκ₁₁ c₀₀ c₁₀ c₀₁ c₁₁ hc₀₀ hc₁₀ hc₀₁ hc₁₁ hb₀₀ hb₁₀ hb₀₁ hb₁₁ hr₀₀ hr₁₀ hr₀₁
      hr₁₁ hf₀₀ hf₁₀ hf₀₁ hf₁₁ hLrange hLfinite hLarange hLafinite using hactual
    refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pn, hPn, hPnEll,
      evp, hevp, Φp, Ψp, hΦp, hΨp, Pp, hPp, hPpEll,
      κ₀₀, κ₁₀, κ₀₁, κ₁₁, hκ₀₀, hκ₁₀, hκ₀₁, hκ₁₁,
      c₀₀, c₁₀, c₀₁, c₁₁, hc₀₀, hc₁₀, hc₀₁, hc₁₁,
      hb₀₀, hb₁₀, hb₀₁, hb₁₁, hr₀₀, hr₁₀, hr₀₁, hr₁₁,
      hf₀₀, hf₁₀, hf₀₁, hf₁₁, hLrange, hLfinite, hLarange, hLafinite, ?_⟩
    -- The original product-kernel equalities determine the two closed-kernel dimensions.
    let : FiniteDimensional ℂ R₀.ker := hf₀₀
    let : FiniteDimensional ℂ R₁₀.ker := hf₁₀
    let : FiniteDimensional ℂ R₀₁.ker := hf₀₁
    let : FiniteDimensional ℂ R₁.ker := hf₁₁
    have hLdim : Module.finrank ℂ L.ker =
        Module.finrank ℂ R₀.ker + Module.finrank ℂ R₁.ker := by
      rw [hLker]
      let eL := (LinearEquiv.ofSubmodule' cEven.toLinearEquiv (R₀.ker.prod R₁.ker)).trans
        (Submodule.prodEquiv R₀.ker R₁.ker)
      simpa only [Module.finrank_prod] using eL.finrank_eq
    have hLadim : Module.finrank ℂ La.ker =
        Module.finrank ℂ R₁₀.ker + Module.finrank ℂ R₀₁.ker := by
      rw [hLaker]
      let eLa := (LinearEquiv.ofSubmodule' cOdd.toLinearEquiv (R₁₀.ker.prod R₀₁.ker)).trans
        (Submodule.prodEquiv R₁₀.ker R₀₁.ker)
      simpa only [Module.finrank_prod] using eLa.finrank_eq
    -- Parametrices identify each actual coefficient cokernel with its metric-adjoint kernel.
    obtain ⟨LD₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := ND₀.rank) ND₀.Fiber
    obtain ⟨LD₁⟩ := nonempty_smoothBundlePresentation (n := n) (r := ND₁.rank) ND₁.Fiber
    obtain ⟨LC₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := NC₀.rank) NC₀.Fiber
    obtain ⟨LC₁⟩ := nonempty_smoothBundlePresentation (n := n) (r := NC₁.rank) NC₁.Fiber
    obtain ⟨Gp, hGp⟩ := Pp.exists_parametrix_of_isElliptic hPpEll
    obtain ⟨Gn, hGn⟩ := Pn.exists_parametrix_of_isElliptic hPnEll
    have hPpIndex := Pp.index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint
      kD₀ kD₁ LD₀ LD₁ Gp hGp
    have hPnIndex := Pn.index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint
      kC₀ kC₁ LC₀ LC₁ Gn hGn
    -- The specified smooth conjugations recover the same associated coefficient maps.
    have hPcIndex : Pc.toLinearMap.index = Pn.toLinearMap.index :=
      index_eq_of_linearEquiv Pc.toLinearMap Pn.toLinearMap S₀ S₁ (fun u ↦ by
        rw [hPn]
        change S₁ (Pc.toLinearMap (S₀.symm (S₀ u))) = S₁ (Pc.toLinearMap u)
        rw [S₀.symm_apply_apply])
    have hPcpIndex : Pcp.toLinearMap.index = Pp.toLinearMap.index :=
      index_eq_of_linearEquiv Pcp.toLinearMap Pp.toLinearMap SD₀ SD₁ (fun u ↦ by
        rw [hPp]
        change SD₁ (Pcp.toLinearMap (SD₀.symm (SD₀ u))) = SD₁ (Pcp.toLinearMap u)
        rw [SD₀.symm_apply_apply])
    have hkernelIndex : (Module.finrank ℂ L.ker : ℤ) - Module.finrank ℂ La.ker =
        Pcp.toLinearMap.index - Pc.toLinearMap.index := by
      rw [hLdim, hLadim, Nat.cast_add, Nat.cast_add,
        ← κ₀₀.finrank_eq, ← κ₁₁.finrank_eq, ← κ₁₀.finrank_eq, ← κ₀₁.finrank_eq,
        hPcpIndex, hPcIndex, hPpIndex, hPnIndex]
      ring
    -- The original Q quotient action uses the very same original kernel coordinates.
    have hQIndex : Q.smoothEquivariantAnalyticIndex IG σ σ' hσ hσ' hQ hQell =
        finiteRepresentationClass ρp - finiteRepresentationClass ρ := by
      obtain ⟨GQ, hGQ⟩ := Q.exists_parametrix_of_isElliptic hQell
      let cQ := Q.kerMetricFormalAdjointEquivCoker k k' L₀ L₁ GQ hGQ
      let enC := en.trans cQ
      let RE := σ.smoothSectionRepresentation IG hσ
      let RF := σ'.smoothSectionRepresentation IG hσ'
      have hrange (g : G) : Q.toLinearMap.range ≤ Q.toLinearMap.range.comap (RF g) := by
        rintro _ ⟨u, rfl⟩
        exact ⟨RE g u, congrArg (fun f ↦ f u) (hQ g)⟩
      let RC := RF.quotient Q.toLinearMap.range hrange
      have hd (g : G) (v : Fin ρ.dimension → ℂ) :
          enC (ρ.representation g v) = RC g (enC v) := by
        change Q.toLinearMap.range.mkQ (en (ρ.representation g v)).val =
          Q.toLinearMap.range.mkQ (RF g (en v).val)
        rw [hen]
      apply Q.smoothEquivariantAnalyticIndex_eq IG σ σ' hσ hσ' hQ hQell ρp ρ enp enC henp
      intro g v
      rw [hd, enC.apply_symm_apply]
      rfl
    refine ⟨hkernelIndex, hQIndex, ?_⟩
    intro g p B₀ B₁ hs hh hi hbase
    -- Evaluate the same base localization on the original two associated representations.
    have hp := C₀.coefficientOperator_analyticIndex S E E' ρp g p hs hh hi hbase
    have hn := C₀.coefficientOperator_analyticIndex S E E' ρ g p hs hh hi hbase
    rw [hQIndex, hkernelIndex]
    simp only [map_sub, AddMonoidHom.sub_apply, associatedRepresentationKZero_finiteClass,
      associatedKZeroClass]
    exact congrArg₂ (fun x y : ℤ ↦ x - y) hp hn

end AtiyahSinger
