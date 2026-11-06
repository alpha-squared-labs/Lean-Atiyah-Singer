/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.ComponentAnalyticIndex

/-!
# Forgetting the full index of one original elliptic symbol

Public module ID: M0592.

Evaluate the same equivariant realization before taking representation dimension.
Its ordinary component index uses the same symbol class and is independent of
its auxiliary positive density. This comparison does not assert that arbitrary
K classes have a fixed global rank representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- Forgetting the same full symbol index gives its original ordinary component index. -/
theorem EquivariantEllipticSymbolData.index_dimension
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    representationDimension G a.index =
      analyticIndexOfComponents μ (homogeneousSymbolKClass 0 a.symbol a.elliptic) := by
  let := modelTopology (EuclideanSpace ℂ (Fin a.source.rank)) a.source.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin a.target.rank)) a.target.Fiber
  -- Choose one invariant realization of this exact symbol and retain all of its data.
  obtain ⟨ν, hν, hνInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G 𝓘(ℝ, VG) (n := n) (M := M)
  let := hν
  obtain ⟨h, hInvariant⟩ :=
    exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG) a.sourceAction a.source_smooth
  obtain ⟨k, kInvariant⟩ :=
    exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG) a.targetAction a.target_smooth
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := a.source.rank) (q := a.target.rank)
    (E := a.source.Fiber) (F := a.target.Fiber)
  let p := R.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2
  have hfixed (g : G) : equivariantPrincipalSymbolRepresentation
      𝓘(ℝ, VG) a.sourceAction a.targetAction a.source_smooth a.target_smooth 0 g
        (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 p) =
          globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 p :=
    (R.equivariant_regularizedSymbol_class_eq_iff 𝓘(ℝ, VG) a.sourceAction a.targetAction
      a.source_smooth a.target_smooth R 0 a.symbol a.symbol g).mpr (a.equivariant g)
  obtain ⟨P, hPg, hp⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := ν) 𝓘(ℝ, VG) a.sourceAction a.targetAction a.source_smooth a.target_smooth 0
      (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 p) hfixed
  have hi : P.IsElliptic := (P.isElliptic_iff_homogeneous R a.symbol hp).mpr a.elliptic
  have heq := equivariantHomogeneousAnalyticIndex_eq 𝓘(ℝ, VG)
    a.sourceAction a.targetAction a.source_smooth a.target_smooth
    a.symbol a.elliptic a.equivariant ν hν h k hInvariant kInvariant hνInvariant R P hPg hi hp
  change a.index = _ at heq
  -- Forget only after identifying the full representation index of that same operator.
  rw [heq, P.representationDimension_equivariantAnalyticIndex 𝓘(ℝ, VG)
    a.sourceAction a.targetAction a.source_smooth a.target_smooth
    h k hInvariant kInvariant hνInvariant hPg hi]
  have hordinary := P.analyticIndexOfComponents_symbolKClassOfHomogeneous ν R a.symbol hp hi
  change analyticIndexOfComponents ν (homogeneousSymbolKClass 0 a.symbol a.elliptic) = _
    at hordinary
  rw [analyticIndexOfComponents_independent_measure ν μ] at hordinary
  exact hordinary.symm

end AtiyahSinger
