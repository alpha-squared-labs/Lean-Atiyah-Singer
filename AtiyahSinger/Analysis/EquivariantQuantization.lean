/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantOperatorAverage
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.GlobalQuantization

/-!
# Realization of invariant principal classes by actual equivariant PDOs

Public module ID: M0558.

On the original compact smooth base, a fixed class in the original S^m/S^(m-1)
quotient is realized by an actual equivariant operator of the same real order.
First use ordinary quantization, then average its exact conjugates against the
normalized Haar measure. The average retains the supplied principal class by
the preceding uniform lower-order argument; no homogeneous representative or
invariant original quantization presentation is assumed.

Sources: SG III.3.19 and the equivariant discussion of III.9 and III.13.
The exact quotient and finite-presentation version is a standard supplement.
This theorem does not construct smooth bundles from varying-rank equivariant
K-data, descend an index to that K-group, or prove the associated-bundle formula
of III.13.6. Ellipticity can be read from the retained class by the existing
full-symbol criterion, without a second realization theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  [hGC : CompactSpace G] [hGT : T2Space G] [hGM : MeasurableSpace G] [hGB : BorelSpace G]
  (m : ℝ)

include hGC hGT hGM hGB

/-- Every invariant principal class has an equivariant realization of the same PDO order. -/
theorem exists_equivariant_principalSymbol
    (a : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : ∀ g : G,
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF m g a = a) :
    ∃ P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
      P.IsEquivariant IG σE σF hσE hσF ∧ P.principalSymbol = a := by
  -- Realize the prescribed class on the same bundles and with the original density.
  obtain ⟨Q, hQ⟩ := principalSymbol_surjective (E := E) (F := F) μ m a
  refine ⟨Q.average IG σE σF hσE hσF,
    Q.isEquivariant_average IG σE σF hσE hσF, ?_⟩
  -- The fixed-class average preserves this chosen representative's quotient class.
  have hfixed (g : G) :
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF m g
        Q.principalSymbol = Q.principalSymbol := by
    rw [hQ]
    exact ha g
  exact (Q.principalSymbol_average_of_fixed IG σE σF hσE hσF hfixed).trans hQ

end AtiyahSinger.PseudodifferentialOperator
