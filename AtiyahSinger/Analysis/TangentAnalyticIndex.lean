/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.TangentCotangentKZero

/-!
# The analytic index on the actual tangent K group

Public module ID: M1029.

SG II.5 identifies tangent and cotangent bundles by a Riemannian metric;
III.13 then uses both descriptions for symbol classes and index maps.
This file transports the existing componentwise analytic index, keeping the
actual symbol class, density and original operator. Metric and density choices
do not change the resulting homomorphism. The analytic–topological index
comparison is separate from this transport.

Sources: SG II.5, printed p.113, and III.13, (13.7)--(13.8), pp.246--247. The metric and density
comparisons use the existing component index. Evaluation on an operator's symbol class
uses the finite-component evaluation theorem, including its off-diagonal smoothing argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- The original analytic index transported to tangent classes using one smooth metric. -/
def tangentAnalyticIndex :
    letI : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)
    CompactSupportKZero (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) →+ ℤ := by
  let g : SmoothTangentMetric (n := n) (M := M) :=
    Classical.choice SmoothTangentMetric.nonempty
  exact (analyticIndexOfComponents μ).comp (tangentCotangentKZeroEquiv g).toAddMonoidHom

/-- Any supplied smooth metric gives the same analytic index on tangent classes. -/
theorem tangentAnalyticIndex_eq (g : SmoothTangentMetric (n := n) (M := M)) :
    tangentAnalyticIndex (n := n) μ =
      (analyticIndexOfComponents μ).comp (tangentCotangentKZeroEquiv g).toAddMonoidHom := by
  -- The same cotangent index is composed with two equal musical transports.
  unfold tangentAnalyticIndex
  dsimp only
  rw [tangentCotangentKZeroEquiv_independent_metric
    (Classical.choice (SmoothTangentMetric.nonempty (n := n) (M := M))) g]

/-- Changing the positive smooth density leaves the tangent analytic index unchanged. -/
theorem tangentAnalyticIndex_independent_measure
    (ν : Measure M) [IsSmoothPositiveMeasure (n := n) ν] :
    tangentAnalyticIndex (n := n) μ = tangentAnalyticIndex (n := n) ν := by
  -- Use one actual metric on both sides, and change only the positive density.
  let g : SmoothTangentMetric (n := n) (M := M) :=
    Classical.choice SmoothTangentMetric.nonempty
  rw [tangentAnalyticIndex_eq μ g, tangentAnalyticIndex_eq ν g,
    analyticIndexOfComponents_independent_measure μ ν]

variable {r q : ℕ} {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- The transported homogeneous symbol has the index of the original global elliptic operator. -/
theorem PseudodifferentialOperator.tangentAnalyticIndex_symbolKClassOfHomogeneous {m : ℝ}
    (g : SmoothTangentMetric (n := n) (M := M))
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    tangentAnalyticIndex (n := n) μ
        ((tangentCotangentKZeroEquiv g).symm (P.symbolKClassOfHomogeneous R a hp hi)) =
      P.toLinearMap.index := by
  -- The specified musical equivalence cancels its own inverse on the original symbol class.
  rw [tangentAnalyticIndex_eq μ g]
  change analyticIndexOfComponents μ
    ((tangentCotangentKZeroEquiv g)
      ((tangentCotangentKZeroEquiv g).symm (P.symbolKClassOfHomogeneous R a hp hi))) = _
  rw [AddEquiv.apply_symm_apply]
  exact PseudodifferentialOperator.analyticIndexOfComponents_symbolKClassOfHomogeneous
    μ P R a hp hi

end AtiyahSinger
