/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorOperatorApproximation

/-!
# Tensor approximation from a fixed principal symbol

Public module ID: M1036.

The tensor cutoffs act on the original external tensor bundles.
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

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := m) (r := s) F]

variable [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]

set_option maxHeartbeats 1000000 in
-- The original symbol, its chosen quantizer, and all cutoff terms retain one witness tuple.
/-- Tensor approximation uses the canonical pieces of a specified principal symbol.
The order-zero difference is approximated by smooth kernels in the Sobolev-to-L² norm. -/
theorem PseudodifferentialOperator.exists_externalTensor_symbol_approximation
    (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
    (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
    (k : SmoothHermitianMetric (n := m) (r := s) F)
    (P₀ : PseudodifferentialOperator (n := n) (r := r₀) (q := r₁) E₀ E₁ μ 1)
    (p : globalSymbolSpace (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (hp : P₀.principalSymbol = globalPrincipalSymbolClass E₀ E₁ 1 p)
    (C : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (Q : QuantizationPresentation (n := m) (r := s) (q := s) F F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
    letI := externalTensorTopology (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
    letI := externalTensorTopology (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let g₁ := externalTensorMetric h₁ k
    let L := fun i : Fin C.size ↦ (C.patch i).toPiece p
    let hL := fun i : Fin C.size ↦ (C.patch i).hasCompactSupport_localSymbol p.val
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F))
      (D : SmoothBundlePresentation (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
        (∀ (u : smoothSections (n := n) (r := r₀) E₀)
          (v : smoothSections (n := m) (r := s) F),
          T (A.smoothToSobolev 1 (externalTensorSection E₀ F u v)) =
            g₁.smoothToL2 (μ.prod ν)
              (externalTensorSection E₁ F (P₀.toLinearMap u) v)) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
              (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1,
            IsSmoothingOperator (μ.prod ν) (P.toLinearMap - ∑ i, ∑ j,
              ((L i).productCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
                (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
            ‖(g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap.comp
              (P.sobolevRealization A D 1 0 (by norm_num)) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
  let := externalTensorTopology (r := r₀) (s := s) E₀ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
  let := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
  let := externalTensorTopology (r := r₁) (s := s) E₁ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  dsimp only
  intro A D
  let L := fun i : Fin C.size ↦ (C.patch i).toPiece p
  let hL := fun i : Fin C.size ↦ (C.patch i).hasCompactSupport_localSymbol p.val
  have hclass : P₀.principalSymbol = (C.quantize μ p).principalSymbol := by
    rw [C.principalSymbol_quantize]
    exact hp
  have hrep : IsPseudodifferentialOperator E₀ E₁ μ 0
      (P₀.toLinearMap - ∑ i, (L i).toLinearMap) := by
    have h := (P₀.principalSymbol_eq_iff (C.quantize μ p)).mp hclass
    have hC : (C.quantize μ p).toLinearMap = ∑ i, (L i).toLinearMap := rfl
    simpa only [hC, sub_self] using h
  obtain ⟨T, hT, happ⟩ := exists_externalTensor_finite_sum_approximation μ ν h₀ h₁ k L hL
    (P₀.toLinearMap - ∑ i, (L i).toLinearMap) hrep Q A D
  refine ⟨T, ?_, happ⟩
  have heq : (∑ i, (L i).toLinearMap) + (P₀.toLinearMap - ∑ i, (L i).toLinearMap) =
      P₀.toLinearMap := by abel
  simpa only [heq] using hT

end AtiyahSinger
