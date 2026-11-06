/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle

/-!
# Bundled smooth complex vector bundles of fixed finite rank

Public module ID: M1397.

This packages the existing standard bundle data so a representative-existence
theorem can quantify over the bundles themselves. The rank is globally fixed;
this is not a replacement for `ComplexBundle.FiniteBundle`, which permits locally
varying ranks. Fibers are small, as in that existing K-theory model. There is no
ellipticity, representative-existence or index assertion in this structure.
Sources: SG III.1, p.167, and III.13 Lemma 13.3, pp.245--246.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- A smooth complex vector bundle with one fixed finite-dimensional model. -/
structure SmoothFiniteComplexBundle {n : ℕ} (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] where
  /-- The complex dimension of the model fiber. -/
  rank : ℕ
  /-- The original fibers, in a fixed universe for existential quantification. -/
  Fiber : M → Type
  /-- Normed additive structure on each fiber. -/
  [normedAddCommGroup : ∀ x, NormedAddCommGroup (Fiber x)]
  /-- The compatible complex normed vector space structure on each fiber. -/
  [normedSpace : ∀ x, NormedSpace ℂ (Fiber x)]
  /-- The total-space topology used by the modeled bundle. -/
  [totalTopology : TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin rank)) Fiber)]
  /-- Local triviality with this same model. -/
  [fiberBundle : FiberBundle (EuclideanSpace ℂ (Fin rank)) Fiber]
  /-- Complex linearity of the local trivializations. -/
  [vectorBundle : VectorBundle ℂ (EuclideanSpace ℂ (Fin rank)) Fiber]
  /-- Real smoothness of the complex-linear transition functions. -/
  [isSmooth : IsSmoothComplexBundle (n := n) (r := rank) Fiber]

attribute [instance] SmoothFiniteComplexBundle.normedAddCommGroup
  SmoothFiniteComplexBundle.normedSpace SmoothFiniteComplexBundle.totalTopology
  SmoothFiniteComplexBundle.fiberBundle SmoothFiniteComplexBundle.vectorBundle
  SmoothFiniteComplexBundle.isSmooth

end AtiyahSinger
