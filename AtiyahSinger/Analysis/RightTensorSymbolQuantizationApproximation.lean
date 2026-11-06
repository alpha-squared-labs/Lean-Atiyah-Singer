/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RightExternalTensorOperatorApproximation

/-!
# Right tensor approximation from a fixed principal symbol

Public module ID: M0935.

The positive-frequency cutoffs act on the original external tensor bundles.
Their bounded realizations converge in the fixed geometric Sobolev norms, and
the limiting operator is specified on actual pure smooth tensor sections.
The fixed input and output charts and frames are used in every comparison.

Source: the finite-atlas assembly in SG III.13.5, pp.249--250.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped ContDiff Manifold SchwartzMap TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space N] [T2Space M]
  {F₀ F₁ : N → Type*} {E : M → Type*}
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, NormedSpace ℂ (F₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [IsSmoothComplexBundle (n := m) (r := s₁) F₁]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

variable [SecondCountableTopology N] [SecondCountableTopology M]
  [CompactSpace N] [CompactSpace M]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := m) ν] [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the canonical tensor pieces of the specified principal symbol.
/-- Tensor approximation can use the canonical pieces of a specified principal symbol.
The order-zero difference from the original operator is approximated on H1 by
smooth-kernel corrections. -/
theorem PseudodifferentialOperator.exists_rightExternalTensor_symbol_approximation
    (h₀ : SmoothHermitianMetric (n := m) (r := s₀) F₀)
    (h₁ : SmoothHermitianMetric (n := m) (r := s₁) F₁)
    (k : SmoothHermitianMetric (n := n) (r := r) E)
    (P₀ : PseudodifferentialOperator (n := m) (r := s₀) (q := s₁) F₀ F₁ ν 1)
    (p : globalSymbolSpace (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (hp : P₀.principalSymbol = globalPrincipalSymbolClass F₀ F₁ 1 p)
    (C : QuantizationPresentation (n := m) (r := s₀) (q := s₁) F₀ F₁)
    (Q : QuantizationPresentation (n := n) (r := r) (q := r) E E) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
    letI := externalTensorTopology (r := r) (s := s₀) E F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
    letI := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
    letI := externalTensorTopology (r := r) (s := s₁) E F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let g₁ := externalTensorMetric k h₁
    let L := fun i : Fin C.size ↦ (C.patch i).toPiece p
    let hL := fun i : Fin C.size ↦ (C.patch i).hasCompactSupport_localSymbol p.val
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r * s₀) (externalTensorFiber E F₀))
      (D : SmoothBundlePresentation (n := n + m) (r := r * s₁) (externalTensorFiber E F₁)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
        (∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := m) (r := s₀) F₀),
          T (A.smoothToSobolev 1 (externalTensorSection E F₀ u v)) =
            g₁.smoothToL2 (μ.prod ν)
              (externalTensorSection E F₁ u (P₀.toLinearMap v))) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r * s₀) (q := r * s₁)
              (externalTensorFiber E F₀) (externalTensorFiber E F₁) (μ.prod ν) 1,
            IsSmoothingOperator (μ.prod ν) (P.toLinearMap - ∑ i, ∑ j,
              ((L i).rightProductCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
                (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
            ‖(g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap.comp
              (P.sobolevRealization A D 1 0 (by norm_num)) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
  let := externalTensorTopology (r := r) (s := s₀) E F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
  let := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
  let := externalTensorTopology (r := r) (s := s₁) E F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  dsimp only
  intro A D
  let L := fun i : Fin C.size ↦ (C.patch i).toPiece p
  let hL := fun i : Fin C.size ↦ (C.patch i).hasCompactSupport_localSymbol p.val
  have hclass : P₀.principalSymbol = (C.quantize ν p).principalSymbol := by
    rw [C.principalSymbol_quantize]
    exact hp
  have hrep : IsPseudodifferentialOperator F₀ F₁ ν 0
      (P₀.toLinearMap - ∑ i, (L i).toLinearMap) := by
    have h := (P₀.principalSymbol_eq_iff (C.quantize ν p)).mp hclass
    have hC : (C.quantize ν p).toLinearMap = ∑ i, (L i).toLinearMap := rfl
    simpa only [hC, sub_self] using h
  obtain ⟨T, hT, happ⟩ := exists_rightExternalTensor_finite_sum_approximation μ ν h₀ h₁ k L hL
    (P₀.toLinearMap - ∑ i, (L i).toLinearMap) hrep Q A D
  refine ⟨T, ?_, happ⟩
  have heq : (∑ i, (L i).toLinearMap) + (P₀.toLinearMap - ∑ i, (L i).toLinearMap) =
      P₀.toLinearMap := by abel
  simpa only [heq] using hT

end AtiyahSinger
