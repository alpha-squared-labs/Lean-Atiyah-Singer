/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact approximation by projections from a prescribed dense subspace

Public module ID: M0356.

A compact operator into an inner product space is approximated in operator norm by
postcomposition with finite-dimensional orthogonal projections. The spanning
vectors are chosen from the given dense pre-Hilbert subspace. In the geometric
application that subspace consists of the original smooth sections, so the
projections have the actual smooth kernels already constructed in
`SmoothFiniteRankProjection`.

This standard compactness argument is the functional-analytic supplement for
the smoothing remainders in SG III.13.5's product regularization. A smoothing
operator in one factor tensored with the identity is not itself asserted to be
a smoothing operator on the product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Metric

variable {D E F : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A compact operator is approximated by orthogonal projections spanned by
prescribed dense data. -/
theorem exists_finite_projection_approximation (j : D →ₗᵢ[ℂ] F) (hj : DenseRange j)
    (A : E →L[ℂ] F) (hA : IsCompactOperator A) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset D,
      ‖A - ((Submodule.span ℂ (s : Set D)).map j.toLinearMap).starProjection.comp A‖ < ε := by
  classical
  let K := closure (A '' closedBall 0 1)
  have hK : IsCompact K := hA.isCompact_closure_image_closedBall 1
  have hhalf : 0 < ε / 2 := half_pos hε
  -- A finite cover of the compact image uses actual vectors from the prescribed dense subspace.
  have hcover : K ⊆ ⋃ v : D, ball (j v) (ε / 2) := by
    intro y _
    obtain ⟨v, hv⟩ := hj.exists_dist_lt y hhalf
    exact mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun v : D ↦ ball (j v) (ε / 2))
    (fun _ ↦ isOpen_ball) hcover
  let W := (Submodule.span ℂ (s : Set D)).map j.toLinearMap
  have hbound : ‖A - W.starProjection.comp A‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hhalf.le
    intro x hx
    have hxK : A x ∈ K := subset_closure ⟨x, by
      simp only [mem_closedBall, dist_zero_right, hx, le_refl], rfl⟩
    obtain ⟨v, hv, hdist⟩ := mem_iUnion₂.mp (hs hxK)
    have hvW : j v ∈ W :=
      Submodule.mem_map.mpr ⟨v, Submodule.subset_span hv, rfl⟩
    -- Orthogonal projection is at least as close as this one covering vector.
    change ‖A x - W.starProjection (A x)‖ ≤ ε / 2
    calc
      ‖A x - W.starProjection (A x)‖ = dist (A x) (W.starProjection (A x)) :=
        (dist_eq_norm _ _).symm
      _ = infDist (A x) W := W.dist_starProjection_eq_infDist (A x)
      _ ≤ dist (A x) (j v) := infDist_le_dist_of_mem hvW
      _ ≤ ε / 2 := hdist.le
  exact ⟨s, hbound.trans_lt (half_lt_self hε)⟩

end AtiyahSinger
