/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricTensorDomain

/-!
# The original geometric tensor graph in its specified coordinates

Public module ID: M0665.

The actual closed tensor graph transports through the exact two original
external tensor unitaries. The formula retains both the domain condition and
the full output, so graph invariance and the fixed graph norm can be checked
on these same geometric coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory UniformSpace
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {n m r₀ r₁ s₀ s₁ : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hTM : T2Space M] [hTN : T2Space N]
  [hSCM : SecondCountableTopology M] [hSCN : SecondCountableTopology N]
  [hCM : CompactSpace M] [hCN : CompactSpace N]
  [MeasurableSpace M] [hBM : BorelSpace M]
  [MeasurableSpace N] [hBN : BorelSpace N]
  {μ : Measure M} {ν : Measure N}
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := m) ν]
  {E₀ : M → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [hE₀ : IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  {E₁ : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [hE₁ : IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  {F₀ : N → Type*}
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, NormedSpace ℂ (F₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [hF₀ : IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  {F₁ : N → Type*}
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [hF₁ : IsSmoothComplexBundle (n := m) (r := s₁) F₁]

include hM hN hTM hTN hSCM hSCN hCM hCN hBM hBN hμ hν hE₀ hE₁ hF₀ hF₁

variable (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
  (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
  (k₀ : SmoothHermitianMetric (n := m) (r := s₀) F₀)
  (k₁ : SmoothHermitianMetric (n := m) (r := s₁) F₁)
  (P : PseudodifferentialOperator (n := n) (r := r₀) (q := r₁) E₀ E₁ μ 1)
  (Q : PseudodifferentialOperator (n := m) (r := s₀) (q := s₁) F₀ F₁ ν 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Normalize the original geometric graph under the specified pair of unitaries.
/-- The original geometric operator graph is the image under its specified pair of unitaries. -/
theorem gradedProductL2Operator_graph :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorTopology (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorTopology (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorTopology (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorTopology (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
    let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₁ k₁)
    let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₀ k₁)
    let P₀ := P.metricL2ClosedRealization h₀ h₁
    let Q₀ := Q.metricL2ClosedRealization k₀ k₁
    let D := gradedTensorOperator P₀ Q₀
    let L := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
    L.graph = D.graph.map
      (Ueven.toContinuousLinearEquiv.prodCongr Uodd.toContinuousLinearEquiv).toLinearMap := by
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberNormedSpace (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorTopology (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorFiberNormedSpace (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorTopology (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorFiberNormedSpace (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorTopology (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorFiberNormedSpace (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorTopology (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
  let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₁ k₁)
  let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₀ k₁)
  let P₀ := P.metricL2ClosedRealization h₀ h₁
  let Q₀ := Q.metricL2ClosedRealization k₀ k₁
  let D := gradedTensorOperator P₀ Q₀
  let L := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
  -- Every original geometric domain point determines its actual abstract graph point.
  apply Submodule.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := L.mem_graph_iff'.mp hz
    let y : D.domain := ⟨Ueven.symm x.val, x.property⟩
    refine ⟨(y.val, D y), D.mem_graph y, ?_⟩
    apply Prod.ext
    · exact Ueven.apply_symm_apply x.val
    · rfl
  · -- Conversely the same input unitary sends every abstract domain point to the geometric domain.
    rintro ⟨z, hz, rfl⟩
    obtain ⟨y, rfl⟩ := D.mem_graph_iff'.mp hz
    have hx : Ueven y.val ∈ L.domain := by
      change Ueven.symm (Ueven y.val) ∈ D.domain
      rw [Ueven.symm_apply_apply]
      exact y.property
    apply L.mem_graph_iff.mpr
    refine ⟨⟨Ueven y.val, hx⟩, rfl, ?_⟩
    change Uodd (D ⟨Ueven.symm (Ueven y.val), hx⟩) = Uodd (D y)
    congr 2
    exact Subtype.ext (Ueven.symm_apply_apply y.val)

end AtiyahSinger
