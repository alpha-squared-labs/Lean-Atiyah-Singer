/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalComposition
public import AtiyahSinger.Analysis.HomogeneousSymbolOperations

/-!
# Homogeneous principal data of a specified zero-order composite

Public module ID: M0748.

The principal class of the actual composite is the regularization of its
specified off-zero homogeneous product. The exact real order zero is retained
when the original PDO composition initially has order 0 + 0. This is the
same principal-symbol multiplication of SG III.3, made explicit for the
realizations used in the bundle decomposition index formula.
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

/-- A specified zero-order composite has the principal class of its same homogeneous product. -/
theorem PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := d) F H)
    (C : QuantizationPresentation (n := n) (r := r) (q := d) E H)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := q) (q := d) F H 0)
    (c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := d) E H 0)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := d) F H μ 0)
    (S : PseudodifferentialOperator (n := n) (r := r) (q := d) E H μ 0)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F 0
      (A.regularizedSymbol 0 a.val a.property.1 a.property.2))
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass F H 0
      (B.regularizedSymbol 0 b.val b.property.1 b.property.2))
    (hS : S.toLinearMap = Q.toLinearMap.comp P.toLinearMap)
    (hcomp : ∀ x ξ, ξ ≠ 0 → c.val x ξ = globalSymbolComp b.val a.val x ξ) :
    S.principalSymbol = globalPrincipalSymbolClass E H 0
      (C.regularizedSymbol 0 c.val c.property.1 c.property.2) := by
  have hc' : IsHomogeneousGlobalSymbol E H (0 + 0) c.val := by
    simpa only [zero_add] using c.property.2
  have hraw : (Q.comp P).principalSymbol = globalPrincipalSymbolClass E H (0 + 0)
      (C.regularizedSymbol (0 + 0) c.val c.property.1 hc') := by
    rw [Q.principalSymbol_comp P, hQ, hP]
    exact globalPrincipalSymbolComp_regularizedSymbol_eq A B C a b
      ⟨c.val, c.property.1, hc'⟩ hcomp
  -- Equality of the actual section maps identifies the exact-order principal quotient.
  have htransfer (l : ℝ) (hl : l = 0)
      (T : PseudodifferentialOperator (n := n) (r := r) (q := d) E H μ l)
      (hh : IsHomogeneousGlobalSymbol E H l c.val)
      (hT : T.toLinearMap = S.toLinearMap)
      (hclass : T.principalSymbol = globalPrincipalSymbolClass E H l
        (C.regularizedSymbol l c.val c.property.1 hh)) :
      S.principalSymbol = globalPrincipalSymbolClass E H 0
        (C.regularizedSymbol 0 c.val c.property.1 c.property.2) := by
    subst l
    exact (S.principalSymbol_eq_of_toLinearMap_eq μ T hT.symm).trans hclass
  exact htransfer _ (zero_add 0) (Q.comp P) hc' hS.symm hraw

end AtiyahSinger
