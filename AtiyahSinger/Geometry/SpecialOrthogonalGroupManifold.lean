/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Geometry.OrthogonalGroupManifold

/-!
# The original special orthogonal group as an open Lie subgroup

Public module ID: M1420.

Inside the original orthogonal group, positive determinant is equivalent to
unit determinant. The native special orthogonal matrix group is homeomorphic
to this actual open subset. Transport its restricted Cayley atlas, retaining
the same skew-adjoint model and matrix operations. The resulting inclusion is
smooth and the native group is compact, including dimension zero.

This is the standard open-subgroup construction needed for full analytic-index
restriction to the original SO(2), without changing the underlying group.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology TopologicalSpace Set
open scoped Manifold ContDiff Matrix.Norms.L2Operator

section Transport

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace E M]

/-- Pull back the chosen charts through the displayed homeomorphism, with explicit transitions. -/
@[instance_reducible]
private def homeomorphPullbackChartedSpace (e : N ≃ₜ M) : ChartedSpace E N where
  atlas := e.transOpenPartialHomeomorph '' atlas E M
  chartAt x := e.transOpenPartialHomeomorph (chartAt E (e x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt E (e x), chart_mem_atlas E (e x), rfl⟩

private theorem isManifold_transported (e : N ≃ₜ M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    letI := homeomorphPullbackChartedSpace (E := E) e
    IsManifold 𝓘(ℝ, E) ∞ N := by
  let := homeomorphPullbackChartedSpace (E := E) e
  refine { compatible := ?_ }
  intro c d hc hd
  obtain ⟨c, hc, rfl⟩ := hc
  obtain ⟨d, hd, rfl⟩ := hd
  rw [e.transOpenPartialHomeomorph_symm_trans]
  exact (contDiffGroupoid ∞ 𝓘(ℝ, E)).compatible hc hd

private def transportedDiffeomorph (e : N ≃ₜ M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    letI := homeomorphPullbackChartedSpace (E := E) e
    N ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M := by
  let := homeomorphPullbackChartedSpace (E := E) e
  let := isManifold_transported (E := E) e
  have hc (x : N) : chartAt E x = e.transOpenPartialHomeomorph (chartAt E (e x)) := rfl
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · rw [contMDiff_iff]
    refine ⟨e.continuous, ?_⟩
    intro x y
    have h := contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (n := ∞) y (e x)
    simpa [extChartAt, hc, mfld_simps, ← Set.preimage_comp, Function.comp_def] using h
  · rw [contMDiff_iff]
    refine ⟨e.symm.continuous, ?_⟩
    intro x y
    have h := contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (n := ∞) (e y) x
    simpa [extChartAt, hc, mfld_simps, ← Set.preimage_comp, Function.comp_def] using h

end Transport

/-- The positive-determinant open subset of the original orthogonal group. -/
def specialOrthogonalOpen (r : ℕ) : Opens (Matrix.orthogonalGroup (Fin r) ℝ) :=
  ⟨{A | 0 < A.val.det}, isOpen_lt continuous_const continuous_subtype_val.matrix_det⟩

/-- The native special orthogonal matrices are precisely this actual open subgroup. -/
def specialOrthogonalOpenHomeomorph (r : ℕ) :
    Matrix.specialOrthogonalGroup (Fin r) ℝ ≃ₜ specialOrthogonalOpen r where
  toFun A := ⟨specialOrthogonalGroupInclusion r A, by
    change 0 < A.val.det
    have hdet : A.val.det = 1 := A.property.2
    rw [hdet]
    norm_num⟩
  invFun B := ⟨B.val.val, B.val.property, by
    have h := congrArg Matrix.det
      ((Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).mp B.val.property)
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    have hb : 0 < B.val.val.det := B.property
    change B.val.val.det = 1
    nlinarith⟩
  left_inv A := rfl
  right_inv B := rfl
  continuous_toFun := (specialOrthogonalGroupInclusion r).continuous.subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Restrict the original Cayley atlas to the native special orthogonal group. -/
instance specialOrthogonalGroupChartedSpace (r : ℕ) :
    ChartedSpace (OrthogonalGroupModel r) (Matrix.specialOrthogonalGroup (Fin r) ℝ) where
  atlas := (specialOrthogonalOpenHomeomorph r).transOpenPartialHomeomorph ''
    atlas (OrthogonalGroupModel r) (specialOrthogonalOpen r)
  chartAt x := (specialOrthogonalOpenHomeomorph r).transOpenPartialHomeomorph
    (chartAt (OrthogonalGroupModel r) (specialOrthogonalOpenHomeomorph r x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨_, chart_mem_atlas _ _, rfl⟩

/-- The actual special orthogonal inclusion is smooth for the inherited native atlas. -/
theorem contMDiff_specialOrthogonalGroupInclusion (r : ℕ) :
    ContMDiff 𝓘(ℝ, OrthogonalGroupModel r) 𝓘(ℝ, OrthogonalGroupModel r) ∞
      (specialOrthogonalGroupInclusion r) := by
  let := lieGroup_orthogonalGroup r
  let e := transportedDiffeomorph (E := OrthogonalGroupModel r)
    (specialOrthogonalOpenHomeomorph r)
  exact contMDiff_subtype_val.comp e.contMDiff

/-- The same original special orthogonal matrix operations are smooth. -/
theorem lieGroup_specialOrthogonalGroup (r : ℕ) :
    LieGroup 𝓘(ℝ, OrthogonalGroupModel r) ∞ (Matrix.specialOrthogonalGroup (Fin r) ℝ) := by
  let := lieGroup_orthogonalGroup r
  let e := transportedDiffeomorph (E := OrthogonalGroupModel r)
    (specialOrthogonalOpenHomeomorph r)
  let := isManifold_transported (E := OrthogonalGroupModel r)
    (specialOrthogonalOpenHomeomorph r)
  let φ := specialOrthogonalGroupInclusion r
  have hφ := contMDiff_specialOrthogonalGroupInclusion r
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · -- Test the same multiplication through the open-subgroup diffeomorphism and inclusion.
    apply (e.contMDiff_diffeomorph_comp_iff le_rfl).mp
    apply (ContMDiff.subtypeVal_comp_iff (specialOrthogonalOpen r) _).mp
    change ContMDiff
      (𝓘(ℝ, OrthogonalGroupModel r).prod 𝓘(ℝ, OrthogonalGroupModel r))
      𝓘(ℝ, OrthogonalGroupModel r) ∞
      (fun p : Matrix.specialOrthogonalGroup (Fin r) ℝ ×
        Matrix.specialOrthogonalGroup (Fin r) ℝ ↦ φ (p.1 * p.2))
    exact ((hφ.comp contMDiff_fst).mul (hφ.comp contMDiff_snd)).congr
      (fun p ↦ (map_mul φ p.1 p.2).symm)
  · apply (e.contMDiff_diffeomorph_comp_iff le_rfl).mp
    apply (ContMDiff.subtypeVal_comp_iff (specialOrthogonalOpen r) _).mp
    change ContMDiff 𝓘(ℝ, OrthogonalGroupModel r) 𝓘(ℝ, OrthogonalGroupModel r) ∞
      (fun A : Matrix.specialOrthogonalGroup (Fin r) ℝ ↦ φ A⁻¹)
    simpa only [map_inv] using hφ.inv

/-- The native special orthogonal group is closed in the original compact orthogonal group. -/
theorem compactSpace_specialOrthogonalGroup (r : ℕ) :
    CompactSpace (Matrix.specialOrthogonalGroup (Fin r) ℝ) := by
  let := compactSpace_orthogonalGroup r
  have hc : IsCompact (Matrix.orthogonalGroup (Fin r) ℝ :
      Set (Matrix (Fin r) (Fin r) ℝ)) := isCompact_iff_compactSpace.mpr inferInstance
  have hd : IsClosed {A : Matrix (Fin r) (Fin r) ℝ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  exact isCompact_iff_compactSpace.mp (hc.inter_right hd)

end AtiyahSinger
