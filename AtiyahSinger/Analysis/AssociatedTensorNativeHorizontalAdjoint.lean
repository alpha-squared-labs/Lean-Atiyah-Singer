/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorSupportedHorizontalLift
public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint
public import AtiyahSinger.Analysis.SectionOperatorSupport

import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Lifting the metric adjoint of a principal-localized piece

Public module ID: M0186.

Wrap the specified native piece by its section map, take its same-order metric
formal adjoint, and transfer the compact operator support through integral
adjunction. A base plateau in the same principal chart gives a smooth
horizontal lift. The displayed value formula retains the complete native
adjoint action, including smoothing terms.
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

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 800000 in
-- The extended limit accommodates the native metric adjoint in the original principal chart.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native metric adjoint lifts smoothly inside the same original principal chart. -/
theorem exists_associatedSphereTensorLocalHorizontalAdjoint {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hL : L.chart.symm '' (tsupport L.input.cutoff ∪ tsupport L.output.cutoff) ⊆
      (S.trivialization b).baseSet) :
    let Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m :=
      ⟨L.toLinearMap, L.isPseudodifferentialOperator m⟩
    let J := Q.metricFormalAdjoint h h'
    let K := L.chart.symm '' (tsupport L.input.cutoff ∪ tsupport L.output.cutoff)
    HasSectionOperatorSupport K J.toLinearMap ∧
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
        ∃ H : (associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ).smoothSections →ₗ[ℂ]
          (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
          ∀ w z, (H w).val z = associatedSphereTensorBaseExtension S E σ b
            (fun y x ↦ ((tensorSectionOperator (F y) (smoothSections E') (smoothSections E)
              J.toLinearMap)
                (associatedSphereTensorCutoffBaseRestriction (a := a')
                  S E' A σ hσ b β hβ hβsupport y w)).val x) z := by
  classical
  let Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m :=
    ⟨L.toLinearMap, L.isPseudodifferentialOperator m⟩
  let J := Q.metricFormalAdjoint h h'
  let K := L.chart.symm '' (tsupport L.input.cutoff ∪ tsupport L.output.cutoff)
  have hcompact := L.input.compact_support.union L.output.compact_support
  have hK : IsCompact K :=
    hcompact.image_of_continuousOn (L.chart.continuousOn_symm.mono (by
      rintro x (hx | hx)
      · exact (L.input.support_subset hx).1
      · exact (L.output.support_subset hx).1))
  -- The original two cutoff supports control the unchanged native piece in both directions.
  have hQ : HasSectionOperatorSupport K Q.toLinearMap := by
    constructor
    · intro u
      apply closure_minimal ?_ hK.isClosed
      intro x hx
      by_contra hxK
      exact hx (L.toLinearMap_eq_zero u x (by
        rintro ⟨z, hz, rfl⟩
        exact hxK ⟨z, Or.inr hz, rfl⟩))
    · intro u hu
      have heq := L.toLinearMap_eq_of_eq_on_support u 0 (by
        intro x hx
        change u.val x = 0
        by_contra hne
        obtain ⟨z, hz, rfl⟩ := hx
        exact Set.disjoint_left.mp hu (subset_closure hne) ⟨z, Or.inl hz, rfl⟩)
      simpa only [map_zero] using heq
  have hJ : HasSectionOperatorSupport K J.toLinearMap :=
    IsMetricFormalAdjoint.hasSectionOperatorSupport h h' μ Q.toLinearMap J.toLinearMap
      (Q.isMetricFormalAdjoint_metricFormalAdjoint h h') K hK.isClosed hQ
  -- Choose one base plateau on both original supports, retaining the same principal chart.
  obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure
    hK (S.trivialization b).open_baseSet hL
  obtain ⟨β, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓡 n) (n := ⊤) hK.isClosed (hKW.trans hW.subset_interior_closure)
  have hβsupport : tsupport β ⊆ (S.trivialization b).baseSet := by
    apply Set.Subset.trans ?_ hWU
    apply closure_minimal ?_ hWc.isClosed
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨hJ, β, β.contMDiff, hβsupport, fun x hx ↦ hone.self_of_nhdsSet x hx, ?_⟩
  -- The full native adjoint now enters the supported lift without a discarded remainder.
  exact exists_associatedSphereTensorSupportedHorizontalLift (a := a')
    S E' A σ E J hσ b β β.contMDiff hβsupport K hK hL
      (fun u x hx ↦ by
        by_contra hne
        exact hx (hJ.1 u (subset_closure hne)))

end AtiyahSinger
