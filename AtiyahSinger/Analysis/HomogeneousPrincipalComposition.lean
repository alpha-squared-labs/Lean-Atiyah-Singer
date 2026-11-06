/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalComposition
public import AtiyahSinger.Analysis.HomogeneousSymbolOperations

/-!
# Homogeneous principal data of a specified real-order composite

Public module ID: M0741.

The product of two given homogeneous symbols is the principal symbol of their
actual composite, with a specified equality of real orders. This adapter retains
the original section maps and permits finite native Hodge block assembly.

Source: SG III.3, principal-symbol multiplication.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F H : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) H]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := d) H]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- An actual composite has the principal class of its supplied homogeneous product. -/
theorem PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp_order
    {l m t : ℝ} (ht : l + m = t)
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := d) F H)
    (C : QuantizationPresentation (n := n) (r := r) (q := d) E H)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := q) (q := d) F H l)
    (c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := d) E H t)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := d) F H μ l)
    (S : PseudodifferentialOperator (n := n) (r := r) (q := d) E H μ t)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (A.regularizedSymbol m a.val a.property.1 a.property.2))
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass F H l
      (B.regularizedSymbol l b.val b.property.1 b.property.2))
    (hS : S.toLinearMap = Q.toLinearMap.comp P.toLinearMap)
    (hcomp : ∀ x ξ, ξ ≠ 0 → c.val x ξ = globalSymbolComp b.val a.val x ξ) :
    S.principalSymbol = globalPrincipalSymbolClass E H t
      (C.regularizedSymbol t c.val c.property.1 c.property.2) := by
  -- Replace the order before comparing the two actual section maps.
  subst t
  have hraw : (Q.comp P).principalSymbol = globalPrincipalSymbolClass E H (l + m)
      (C.regularizedSymbol (l + m) c.val c.property.1 c.property.2) := by
    rw [Q.principalSymbol_comp P, hQ, hP]
    exact globalPrincipalSymbolComp_regularizedSymbol_eq A B C a b c hcomp
  exact (S.principalSymbol_eq_of_toLinearMap_eq μ (Q.comp P) hS).trans hraw

end AtiyahSinger
