/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolIndexInvariance

/-!
# Small degree-zero representatives of an original elliptic operator

Public module ID: M0959.

The general order reduction and actual smooth bundle models provide a small
representative of the same original symbol class and smooth index. No
connectedness assumption is needed: the class already comes from the given
operator. This reduction lets finite clopen decompositions use native small
bundles without narrowing the original operator's order or fiber universe.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- Every displayed elliptic PDO has a small degree-zero representative with its class and index. -/
theorem PseudodifferentialOperator.exists_small_orderZero_representative {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    ∃ (A B : SmoothFiniteComplexBundle (n := n) M)
      (S : QuantizationPresentation (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber 0)
      (Q : PseudodifferentialOperator (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber μ 0)
      (hQ : Q.principalSymbol = globalPrincipalSymbolClass A.Fiber B.Fiber 0
        (S.regularizedSymbol 0 b.val b.property.1 b.property.2)) (hj : Q.IsElliptic),
      Q.symbolKClassOfHomogeneous S b hQ hj = P.symbolKClassOfHomogeneous R a hp hi ∧
      Q.toLinearMap.index = P.toLinearMap.index := by
  classical
  -- Reduce the given symbol to degree zero while retaining its actual compact-support class.
  obtain ⟨g⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  have ha := (P.isElliptic_iff_homogeneous R a hp).mp hi
  obtain ⟨P₀, a₀, ha₀, _, _, _, _, _, _, hK₀⟩ := P.exists_orderShift g R a hp ha 0
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  obtain ⟨A, _, e, he⟩ := exists_small_smooth_bundle_model (n := n) (r := r) E
  let := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
  obtain ⟨B, _, f, hf⟩ := exists_small_smooth_bundle_model (n := n) (r := q) F
  let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
  -- Transport through the same two smooth isomorphisms and quantize that very symbol.
  obtain ⟨b, hb, hsquare⟩ := exists_homogeneousSymbol_of_bundleIso μ e f
    (he.symm e.linearEquiv) hf a₀ ha₀
  obtain ⟨S⟩ := nonempty_quantizationPresentation (n := n) (r := A.rank) (q := B.rank)
    (E := A.Fiber) (F := B.Fiber)
  let Q := S.quantizeHomogeneous S μ 0 b.val b.property.1 b.property.2
  have hQ := S.principalSymbol_quantizeHomogeneous S μ 0 b.val b.property.1 b.property.2
  have hj : Q.IsElliptic := (Q.isElliptic_iff_homogeneous S b hQ).mpr hb
  have hclass : Q.symbolKClassOfHomogeneous S b hQ hj =
      P.symbolKClassOfHomogeneous R a hp hi := by
    exact (Q.symbolKClassOfHomogeneous_eq S b hQ hj).trans
      ((homogeneousSymbolKClass_eq_of_bundleIso 0 e f a₀ b ha₀ hb
        (fun x ξ _ v ↦ hsquare x ξ v)).symm.trans
          (hK₀.trans (P.symbolKClassOfHomogeneous_eq R a hp hi).symm))
  -- The already proved cross-bundle comparison returns the index of the original operator.
  exact ⟨A, B, S, b, Q, hQ, hj, hclass,
    Q.index_eq_of_symbolKClass_eq S b hQ hj P R a hp hi hclass⟩

end AtiyahSinger
