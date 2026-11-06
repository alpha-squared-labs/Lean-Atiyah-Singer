/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothConnectionExistence
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Existence of a smooth connection on the tangent bundle

Public module ID: M1473.

A01: the integer Sobolev construction can use any smooth tangent connection.
A Hausdorff second countable smooth manifold admits such a connection by
the standard partition-of-unity construction. The theorem uses the native
tangent fibers and topology; it asserts smoothness of the connection.

Source: the smooth connection existence argument underlying the
covariant-derivative norm convention in *Spin Geometry* (SG), III.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC

/-- A smooth real connection exists on the actual tangent bundle of the original manifold. -/
theorem exists_smooth_tangent_connection :
    ∃ cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M)),
      CovariantDerivative.ContMDiffCovariantDerivative cov ∞ := by
  -- Apply the native existence theorem to the given smooth tangent bundle.
  exact exists_smooth_covariantDerivative (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M))

end AtiyahSinger
