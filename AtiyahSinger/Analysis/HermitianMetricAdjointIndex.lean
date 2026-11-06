/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.HermitianMetricAdjointKernel

/-!
# The index of the specified metric adjoint

Public module ID: M0718.

An elliptic operator on a compact smooth manifold and its adjoint for the
two prescribed metrics have opposite smooth indices. Two-sided parametrices
identify their cokernels with the opposite smooth kernels. Adjoint
involutivity then recovers the original operator and the paired index formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The original elliptic smooth operator and its specified metric adjoint have opposite indices. -/
theorem index_metricFormalAdjoint_eq_neg (hP : P.IsElliptic) :
    (P.metricFormalAdjoint h k).toLinearMap.index = -P.toLinearMap.index := by
  classical
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  -- Both original operators admit genuine two-sided parametrices.
  have hPa : (P.metricFormalAdjoint h k).IsElliptic :=
    (P.isElliptic_metricFormalAdjoint_iff h k).mpr hP
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  obtain ⟨Qa, hQa⟩ := (P.metricFormalAdjoint h k).exists_parametrix_of_isElliptic hPa
  -- The same two smooth kernels exchange roles under literal adjoint involution.
  have hforward := P.index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint h k A B Q hQ
  have hreverse :=
    (P.metricFormalAdjoint h k).index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint
      k h B A Qa hQa
  rw [P.metricFormalAdjoint_metricFormalAdjoint h k] at hreverse
  rw [hforward, hreverse]
  omega

end PseudodifferentialOperator

end AtiyahSinger
