/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantOperatorAverage
public import AtiyahSinger.Analysis.EquivariantWeightedSymbolIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

import AtiyahSinger.Analysis.EquivariantAveragingAssembly
import AtiyahSinger.Analysis.EquivariantAveragingPrincipalSymbolAssembly
import AtiyahSinger.Analysis.EquivariantLocalAverage
import AtiyahSinger.Analysis.EquivariantSectionTopologyWeak
import AtiyahSinger.Analysis.EquivariantWeightedSymbolIntegral
import AtiyahSinger.Analysis.PseudodifferentialDistributions
import AtiyahSinger.Analysis.SmoothSectionIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The principal symbol of the actual Haar average

Public module ID: M0470.

The original averaged PDO represents the normalized orbit integral of its
original principal symbol, without a fixed-symbol assumption. This form is
needed for the finite-atlas graded cutoffs whose scalar weights need not be
invariant. The local and finite assembly use the existing audited integrals.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory TopologicalSpace
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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

/-- The chosen Haar-average PDO has the actual orbit-averaged principal class. -/
theorem principalSymbol_average :
    (P.average IG σE σF hσE hσF).principalSymbol =
      equivariantWeightedPrincipalSymbolIntegral IG σE σF hσE hσF
        (Measure.haarMeasure (⊤ : PositiveCompacts G)) (fun _ ↦ 1) continuous_const m
          P.principalSymbol := by
  classical
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let J (w : G → ℂ) (hw : Continuous w) :=
    equivariantWeightedPrincipalSymbolIntegral IG σE σF hσE hσF ν w hw m
  -- Genuine weighted symbol integrals pass through finite group partitions before quotienting.
  have hJsum (N : ℕ) (w : Fin N → G → ℂ) (hw : ∀ j, Continuous (w j))
      (hone : ∀ g, ∑ j, w j g = 1) (pclass : GlobalPrincipalSymbolSpace E F m) :
      (∑ j, J (w j) (hw j) pclass) = J (fun _ ↦ 1) continuous_const pclass := by
    exact equivariantWeightedPrincipalSymbolIntegral_sum IG σE σF hσE hσF ν m
      w hw hone pclass
  -- Each local certificate retains one operator and one source symbol before choosing the weight.
  obtain ⟨Q, hQ, hQclass⟩ := exists_pseudodifferential_average_with_principalSymbol_of_local
    IG σE σF hσE hσF J hJsum
    (fun L g₀ c hc e f _ _ hbase ↦ by
      obtain ⟨U, hU, hg₀U, p, hp, hlocal⟩ :=
        L.exists_local_weighted_average_with_principalSymbol
          (μ := μ) IG σE σF hσE hσF g₀ c hc e f hbase
      refine ⟨U, hU, hg₀U, ?_⟩
      intro w hw hwsupp
      obtain ⟨R, hR, pbar, hpbar, hlower⟩ := hlocal w hw hwsupp
      refine ⟨R, hR, ?_⟩
      rw [hpbar, ← hp]
      change globalPrincipalSymbolClass E F m pbar =
        equivariantWeightedPrincipalSymbolIntegral IG σE σF hσE hσF ν w hw m
          (globalPrincipalSymbolClass E F m p)
      rw [equivariantWeightedPrincipalSymbolIntegral_class]
      apply (globalPrincipalSymbolClass_eq_iff E F m _ _).mpr
      exact hlower) P
  -- Extensional equality identifies this certified PDO with the original chosen average.
  have hsame : (P.average IG σE σF hσE hσF).toLinearMap = Q.toLinearMap := by
    ext u x
    exact (P.average_apply IG σE σF hσE hσF u x).trans (hQ u x).symm
  rw [(P.average IG σE σF hσE hσF).principalSymbol_eq_of_toLinearMap_eq μ Q hsame,
    hQclass]

end AtiyahSinger.PseudodifferentialOperator
