/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps

/-!
# Smooth projection onto a clopen bundle summand

Public module ID: M1125.

Multiplication by the characteristic function of a clopen base subset is a
smooth bundle endomorphism in the original native atlas. It is locally the
identity or zero, so no smoothing or replacement of the original bundle is
needed. This projection is used both to restrict an actual PDO and to remove
its off-diagonal blocks over a finite clopen decomposition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

open scoped Classical in
/-- The characteristic projection onto a clopen base subset is smooth in the original atlas. -/
theorem isSmoothBundleMap_clopenIndicator (U : Opens M) (hclosed : IsClosed (U : Set M)) :
    IsSmoothBundleMap (n := n) (r := r) (q := r)
      (fun x ↦ if x ∈ U then LinearMap.id (R := ℂ) (M := E x) else 0) := by
  classical
  intro e he f hf j x hx
  -- Within the clopen set, the projection is locally the original identity bundle map.
  by_cases hxU : x ∈ U
  · let ev := ((ContinuousLinearMap.apply ℂ
      (EuclideanSpace ℂ (Fin r)) (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ)
    have hcoord := ev.contMDiff.comp_contMDiffOn
      (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E) e f)
    apply ContMDiffAt.contMDiffWithinAt
    apply (hcoord.contMDiffAt
      ((e.open_baseSet.inter f.open_baseSet).mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds hxU,
      (e.open_baseSet.inter f.open_baseSet).mem_nhds hx] with y hy hye
    rw [show (if y ∈ U then LinearMap.id (R := ℂ) (M := E y) else 0) =
      LinearMap.id from ite_eq_left hy, LinearMap.id_apply, e.symmL_apply hye.1]
    exact (e.coordChangeL_apply f hye (EuclideanSpace.single j (1 : ℂ))).symm
  · -- Closedness supplies an open neighborhood on which the same projection vanishes.
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_const
      (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [hclosed.isOpen_compl.mem_nhds hxU,
      f.open_baseSet.mem_nhds hx.2] with y hy hyf
    rw [show (if y ∈ U then LinearMap.id (R := ℂ) (M := E y) else 0) = 0 from
      ite_eq_right hy]
    exact (f.linearEquivAt ℂ y hyf).map_zero

end AtiyahSinger
