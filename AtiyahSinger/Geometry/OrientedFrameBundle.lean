/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinCoordinates
public import AtiyahSinger.Geometry.OrthogonalFrameBundle
public import Mathlib.LinearAlgebra.Orientation

/-!
# Oriented frames inside the original orthogonal frame bundle

Public module ID: M1327.

An oriented orthonormal frame is an original OrthogonalFrameBundle element
whose transported standard real orientation is the specified orientation of
its original fiber. Its topology is the subspace topology of the original
column topology; no second frame carrier or independent bundle topology is
selected. The real coordinate order is interleaved, matching SpinCoordinates.

The orientation field is supplied here as native mathlib Orientation values.
This file alone does not assert its local compatibility. A topological spin
structure provides local continuous positive frames through its own original
principal charts and continuous lift; that implication is stated separately.

Sources: Lawson--Michelsohn, Spin Geometry, II.1, pp. 78--81, and Appendix A.
No smoothness, existence of a spin structure, or global frame is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

variable (m : ℕ) {B : Type*} (E : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  (o : ∀ x, Orientation ℝ (E x) (Fin (2 * m)))

/-- Positive original orthogonal frames, with their actual fiber orientation condition. -/
def OrientedOrthogonalFrameBundle : Type _ :=
  {p : OrthogonalFrameBundle (2 * m) E //
    Orientation.map (Fin (2 * m)) p.2.toLinearEquiv
      (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.orientation = o p.1}

/-- The original base point, unchanged by the orientation restriction. -/
def orientedOrthogonalFrameProjection : OrientedOrthogonalFrameBundle m E o → B :=
  fun f ↦ f.val.1

variable [TopologicalSpace B]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]

/-- The subspace topology inherited from the original orthogonal frame column topology. -/
@[reducible]
def orientedOrthogonalFrameTopology : TopologicalSpace (OrientedOrthogonalFrameBundle m E o) :=
  TopologicalSpace.induced (fun f : OrientedOrthogonalFrameBundle m E o ↦ f.val)
    (orthogonalFrameTopology (2 * m) E)

end AtiyahSinger
