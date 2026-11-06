/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolAnalyticIndex
public import AtiyahSinger.Analysis.AtlasFullSymbolOperatorKClass
public import AtiyahSinger.Analysis.FullSymbolAnalyticIndex
public import AtiyahSinger.Analysis.IndexTheorem

/-!
# Atiyah--Singer for the same original general full-symbol operator

Public module ID: M2314.

M2312 and M2310 evaluate the actual smooth index of the original atlas and native
operators on their genuine full-symbol classes. M0760 identifies the two existing
index homomorphisms on the entire original compact-support cotangent K group.
Together these results give the index theorem from standard ellipticity alone.

The atlas version constructs its positive Borel density internally. The native
version retains the density already carried by its prescribed operator. The
topological index keeps its original positive Bott coordinate and cotangent
transport; no new index map, homogeneous symbol or quantizer is supplied.

Source: SG III.13, Theorem 13.2, with the same-object general full-symbol
evaluation from M2310--M2312 as an explicit project supplement. SG means
H. Blaine Lawson, Jr. and Marie-Louise Michelsohn, *Spin Geometry*
(Princeton University Press, 1989).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

section AtlasOperator

variable {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

/-- SG III.13.2 for the original variable-rank atlas PDO and its intrinsic full-symbol class. -/
theorem AtlasPseudodifferentialOperator.index_eq_cotangentTopologicalIndex_fullSymbol
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hi : P.IsElliptic) :
    P.toLinearMap.index = cotangentTopologicalIndex n M (P.fullSymbolKClass hi) := by
  classical
  -- Supply a standard positive density without altering the given smooth section action.
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  -- The chosen representative comes from this very hi and evaluates this very P.
  have heval := P.analyticIndexOfComponents_atlasFullSymbolKClass μ
    (Classical.choose hi) (Classical.choose_spec hi).2 (Classical.choose_spec hi).1
  change analyticIndexOfComponents μ (P.fullSymbolKClass hi) = P.toLinearMap.index at heval
  rw [analyticIndexOfComponents_eq_cotangentTopologicalIndex μ] at heval
  exact heval.symm

end AtlasOperator

section NativeOperator

variable [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {r q : ℕ} {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- SG III.13.2 for the same original native PDO, with standard full ellipticity as input. -/
theorem PseudodifferentialOperator.index_eq_cotangentTopologicalIndex_fullSymbol
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic) :
    P.toLinearMap.index = cotangentTopologicalIndex n M (P.fullSymbolKClass hi) := by
  -- Keep the given operator's original density, complete symbol class and smooth index.
  have heval := P.analyticIndexOfComponents_fullSymbolKClass hi
  rw [analyticIndexOfComponents_eq_cotangentTopologicalIndex μ] at heval
  exact heval.symm

end NativeOperator

end AtiyahSinger
