/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm
public import AtiyahSinger.Topology.KZeroFunctor

/-!
# The point index and the specified K⁰(point) normalization

Public module ID: M0856.

P09, SG III.13, Property 1. On a zero-dimensional point there is no nonzero cotangent
direction imposing a symbol invertibility condition. Every finite-dimensional linear
map has index equal to the virtual rank of its domain minus its codomain. This module
links that analytic statement to the actual K₀ presentation and its rank isomorphism.
Comparison with a global analytic-index homomorphism is a separate construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Point normalization for every operator between the displayed finite-dimensional fibers. -/
theorem index_on_point_eq_kZero_rank (r s : ℕ)
    (T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)) :
    T.index = complexKZeroPointEquivInt
      (kZeroClass C(PUnit, ℂ) (IdempotentMatrix.identity C(PUnit, ℂ) r) -
        kZeroClass C(PUnit, ℂ) (IdempotentMatrix.identity C(PUnit, ℂ) s)) := by
  /- First apply finite-dimensional rank-nullity to T: its rank cancels from the
  kernel-minus-cokernel dimension, leaving r−s. Independently, the specified K₀ rank
  isomorphism sends the two identity-matrix presentations to r and s. Their difference
  is therefore the same integer. The argument includes zero-rank fibers and requires
  neither injectivity nor surjectivity of T. -/
  -- Both normalizations evaluate to the same virtual dimension of the given fibers.
  rw [index_on_point, complexKZeroPointEquivInt_sub_identity]

end AtiyahSinger
