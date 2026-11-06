/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle
public import AtiyahSinger.Topology.FiniteBundle

/-!
# Smooth complex bundle atlases with locally varying finite rank

Public module ID: M1386.

D01: a standard smooth complex-linear bundle atlas on the original fibers
and the original total-space topology. Each chart has a finite-dimensional
complex coordinate space; different connected components may have different
ranks. The covering charts and their actual overlap coordinate maps specify
the smooth structure. No replacement fiber family, new total topology,
global rank bound, compactness or connectedness is part of the definition.

The local models are the finite coordinate spaces already used by
ComplexBundle.IsFiniteRank. Transition smoothness is real smoothness of
the complex-linear matrix columns. On a nonempty overlap the two model
dimensions agree automatically by their fiberwise linear equivalences;
empty overlaps impose no rank equation. The section predicate tests the
actual coordinates of the original section in these same charts.

Sources: Spin Geometry III.1, p.167, gives smooth complex bundles and their
smooth sections. Hatcher, Vector Bundles and K-Theory, section 2.1, p.39,
allows different finite fiber dimensions on different components. The
indexed atlas is the usual transition-function description combining these
conventions. The chart index universe is unrestricted independently of
the fiber universe. No finite-topological-type assumption is built in.
-/

@[expose] public noncomputable section

universe v

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- A covering smooth complex-linear atlas for a bundle of locally varying finite rank.
Every chart acts on the original total space with its given topology. -/
structure SmoothComplexBundleAtlas where
  /-- The index set of the given local bundle charts, with no finiteness requirement. -/
  Index : Type v
  /-- The finite complex dimension of each local coordinate space. -/
  rank : Index → ℕ
  /-- Actual local trivializations of the original bundle projection. -/
  chart : ∀ i : Index, Trivialization (Fin (rank i) → ℂ) (π Unit E)
  /-- The given open chart domains cover every original base point. -/
  covers : ∀ x : M, ∃ i : Index, x ∈ (chart i).baseSet
  /-- Every local coordinate map is complex linear on each fiber in its base set. -/
  linear : ∀ (i : Index) (x : M), x ∈ (chart i).baseSet →
    IsLinearMap ℂ (fun z : E x ↦ (chart i ⟨x, z⟩).2)
  /-- The actual transition columns are real smooth on the original chart overlaps. -/
  contMDiffOn_coordChange : ∀ (i j : Index) (a : Fin (rank i)),
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (rank j) → ℂ) ∞
      (fun x : M ↦ (chart j ((chart i).toPartialEquiv.symm (x, Pi.single a 1))).2)
      ((chart i).baseSet ∩ (chart j).baseSet)

namespace SmoothComplexBundleAtlas

variable {E} (A : SmoothComplexBundleAtlas (n := n) E)

/-- Forgetting smooth transition conditions keeps the original local finite-rank bundle. -/
theorem isFiniteRank (A : SmoothComplexBundleAtlas (n := n) E) :
    ComplexBundle.IsFiniteRank E where
  exists_linear_trivialization x := by
    -- Reuse a covering chart and its original linearity certificate verbatim.
    obtain ⟨i, hx⟩ := A.covers x
    exact ⟨A.rank i, A.chart i, hx, A.linear i⟩

/-- A section is smooth precisely when its actual coordinates are smooth in every atlas chart. -/
def IsSmoothSection (s : ∀ x : M, E x) : Prop :=
  ∀ i : A.Index,
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
      (fun x : M ↦ (A.chart i ⟨x, s x⟩).2) (A.chart i).baseSet

end SmoothComplexBundleAtlas

end AtiyahSinger
