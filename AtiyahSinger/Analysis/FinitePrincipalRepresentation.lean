/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialSpace

/-!
# Finite index sets for principal representations

Public module ID: M0628.

This implementation adapter reindexes the existing Fin-indexed principal
representation formula by any finite type. It allows the two original patch
indices in each of the four product cutoff blocks to remain paired literally.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- Reindex a finite local representation without changing its actual symbol sum. -/
theorem PseudodifferentialOperator.principalSymbol_eq_of_finite_representation
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    {ι : Type*} [Fintype ι]
    (L : ι → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (h : IsSmoothingOperator μ (P.toLinearMap - ∑ i, (L i).toLinearMap)) :
    P.principalSymbol = globalPrincipalSymbolClass E F m (∑ i, (L i).globalSymbol) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hmap : (∑ j, (L (e j)).toLinearMap) = ∑ i, (L i).toLinearMap :=
    e.sum_comp (fun i ↦ (L i).toLinearMap)
  have hsymbol : (∑ j, (L (e j)).globalSymbol) = ∑ i, (L i).globalSymbol :=
    e.sum_comp (fun i ↦ (L i).globalSymbol)
  rw [← hmap] at h
  rw [P.principalSymbol_eq_of_representation (Fintype.card ι) (fun j ↦ L (e j)) h, hsymbol]

end AtiyahSinger
