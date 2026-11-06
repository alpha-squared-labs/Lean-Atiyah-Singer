/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.Basic

/-!
# The original total space of a real rank-zero vector bundle

Public module ID: M1516.

The native projection and zero section are inverse homeomorphisms. The
zero-dimensional model forces every actual fiber vector to be zero through
the existing continuous linear chart equivalence. No replacement topology,
chosen global frame, compactness or Hausdorff assumption is used.

This is the standard degenerate vector-bundle case needed by SC01. The
existing complex-bundle zero-section homeomorphism uses a different model
and topology API; this adapter retains the original real FiberBundle data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

variable {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]

/-- The original projection of a rank-zero real bundle, with its zero section as inverse. -/
def zeroRankBundleProjectionHomeomorph :
    TotalSpace (EuclideanSpace ℝ (Fin 0)) E ≃ₜ B where
  toFun := π (EuclideanSpace ℝ (Fin 0)) E
  invFun := zeroSection (EuclideanSpace ℝ (Fin 0)) E
  left_inv z := by
    -- The native chart identifies this actual fiber with the zero-dimensional model.
    have hv : z.snd = 0 :=
      (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin 0)) E z.proj).injective
        (Subsingleton.elim _ _)
    -- Projection followed by the zero section therefore retains the original vector.
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq hv.symm
  right_inv _ := rfl
  continuous_toFun := FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin 0)) E
  continuous_invFun := Bundle.Trivialization.continuous_zeroSection ℝ

end AtiyahSinger
