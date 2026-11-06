/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ComplexSpinor
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The fixed interleaved real coordinates of the spinor vector model

Public module ID: M0059.

The real coordinates of complex m-space are ordered as e1, i*e1, e2, i*e2,
and so on, exactly as in SpinorChirality. The following isometry is built
from mathlib's actual real orthonormal basis (1,i) of each complex coordinate.
It identifies existing real orthogonal frames with the existing spin vector
model; it does not choose an unspecified orientation-preserving isomorphism.

Source: Lawson--Michelsohn, Spin Geometry, I.5, with the interleaved orientation
fixed in this project's explicit exterior spinor realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The actual interleaved real isometry into the original complex spin vector model. -/
def realSpinorCoordinateIsometry (m : ℕ) :
    EuclideanSpace ℝ (Fin (2 * m)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin m) :=
  ((Pi.orthonormalBasis (fun _ : Fin m ↦ Complex.orthonormalBasisOneI)).reindex
    ((Equiv.sigmaEquivProd (Fin m) (Fin 2)).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))))).repr.symm

end AtiyahSinger
