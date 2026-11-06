/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothComplexBundleAtlas

/-!
# Linear fiber coordinates in a smooth bundle atlas

Public module ID: M1094.

Implementation adapter for D01/D05. The original trivialization supplies both
directions of this linear equivalence. The phantom model `Unit` in the original
total space prevents direct use of mathlib's fixed-model `linearEquivAt` API.
Neither fiber norms nor replacement bundle fibers are introduced here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- The actual fiber coordinates and inverse of an atlas trivialization on its base set. -/
def frameLinearEquiv (A : SmoothComplexBundleAtlas (n := n) E) (i : A.Index)
    (x : M) (hx : x ∈ (A.chart i).baseSet) : E x ≃ₗ[ℂ] (Fin (A.rank i) → ℂ) where
  toFun v := (A.chart i ⟨x, v⟩).2
  invFun v := cast (congrArg E ((A.chart i).proj_symm_apply' hx))
    ((A.chart i).toOpenPartialHomeomorph.symm (x, v)).2
  left_inv := by
    intro v
    -- The chart inverse returns the original total-space point and hence its fiber vector.
    dsimp only
    rw [cast_eq_iff_heq]
    exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.2)
      ((A.chart i).symm_apply_mk_proj (x := ⟨x, v⟩)
        ((A.chart i).mem_source.mpr hx))
  right_inv := by
    intro v
    -- Projection transport does not change the inverse total-space point.
    dsimp only
    have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
      ((A.chart i).proj_symm_apply' (x := v) hx)
      ((A.chart i).toOpenPartialHomeomorph.symm (x, v)).2
    exact (congrArg (fun z : TotalSpace Unit E ↦ (A.chart i z).2) hpoint).trans
      (congrArg Prod.snd ((A.chart i).apply_symm_apply' hx))
  map_add' := (A.linear i x hx).map_add
  map_smul' := (A.linear i x hx).map_smul

end AtiyahSinger.SmoothComplexBundleAtlas
