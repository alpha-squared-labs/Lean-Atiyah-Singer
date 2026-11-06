/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothSpinorBundle
public import AtiyahSinger.Geometry.SpinSmoothLift
public import AtiyahSinger.Geometry.TangentMusical

/-!
# Spin structures on the original Riemannian tangent bundle

Public module ID: M1357.

The standard manifold spin structure is the Euclidean spin lift of its
original tangent bundle with the supplied smooth metric. The native
RiemannianBundle construction supplies compatible fiber norms and inner
products while retaining the tangent fibers, linear operations, fiber
topologies and total topology. No independent metric or replacement
tangent bundle is introduced.

The imported arbitrary-dimensional compatible-chart theorem applies to this
very structure. In positive even dimension, the frame-preserving comparison
with TopologicalSpinStructure connects it to the original associated full
and half-spin bundles. SpinSmoothLift and SmoothSpinorBundle then select
compatible smooth principal and associated atlases using those same data.
These are existing generic constructions, not new special-case theorems.

Source: Lawson--Michelsohn, Spin Geometry, II.1 Definition 1.3 and II.3
Example 3.1. Positive dimensions include the separate n=1 and n=2
conventions. At n=0 this inherits the explicit native one-sheeted extension
and its canonical empty-frame orientation restriction; the source does not
state a two-fold spin cover at that endpoint. Connections and Dirac
operators are constructed separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] euclideanSpinGroupTopology euclideanSpinGroup_isTopologicalGroup

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction (spinGroup (euclideanSpinQuadraticForm n))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (euclideanSpinQuadraticForm n))ᵐᵒᵖ P]
  {projection : P → M}

/-- A spin structure for the supplied metric on the original tangent bundle. -/
abbrev RiemannianSpinStructure (g : SmoothTangentMetric (n := n) (M := M))
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) (Fin n))
    (hP : IsPrincipalBundle (spinGroup (euclideanSpinQuadraticForm n)) projection) : Type _ :=
  letI : RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  EuclideanSpinStructure n
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) o hP

end AtiyahSinger
