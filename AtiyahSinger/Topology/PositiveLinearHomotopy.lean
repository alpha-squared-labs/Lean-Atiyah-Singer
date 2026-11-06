/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalHomologyLinearization
public import AtiyahSinger.Topology.PositiveMatrixPath
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Positive linear changes preserve local homology

Public module ID: M1995.

Transport the actual positive-determinant matrix path through the given finite
basis. Every intermediate matrix is invertible, so this is a homotopy of the
original punctured pair. Relative homotopy invariance proves identity of the
induced map before choosing a local homology generator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A positive-determinant real linear change acts as the identity on the original local pair. -/
theorem relativeSingularHomologyMap_eq_id_of_det_pos
    (R : Type) [CommRing R] {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) (e : V ≃L[ℝ] V)
    (he : 0 < LinearMap.det e.toLinearMap) (k : ℕ) :
    relativeSingularHomologyMap R (⟨e, e.continuous⟩ : C(V, V))
      (A := {v : V | v ≠ 0}) (B := {v : V | v ≠ 0})
      (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) k = 𝟙 _ := by
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let c : V ≃L[ℝ] (Fin r → ℝ) := b.equivFun.toContinuousLinearEquiv
  let A := LinearMap.toMatrix b b e.toLinearMap
  have hA : 0 < A.det := by simpa only [A, LinearMap.det_toMatrix] using he
  obtain ⟨p, hp⟩ := exists_matrix_path_of_det_pos A hA
  let f : C(V, V) := ⟨e, e.continuous⟩
  -- Fixed basis coordinates turn this actual matrix path into a continuous linear homotopy.
  let H : (ContinuousMap.id V).Homotopy f :=
    { toFun z := c.symm ((p z.1).mulVec (c z.2))
      continuous_toFun := c.symm.continuous.comp
        ((p.continuous.comp continuous_fst).matrix_mulVec (c.continuous.comp continuous_snd))
      map_zero_left := by
        intro v
        change c.symm ((p 0).mulVec (c v)) = v
        rw [p.source, Matrix.one_mulVec, c.symm_apply_apply]
      map_one_left := by
        intro v
        change c.symm ((p 1).mulVec (c v)) = e v
        rw [p.target]
        apply c.injective
        rw [c.apply_symm_apply]
        exact LinearMap.toMatrix_mulVec_repr b b e.toLinearMap v }
  have hH (t : unitInterval) (v : V) (hv : v ≠ 0) : H (t, v) ≠ 0 := by
    intro hzero
    have hcoords := congrArg c hzero
    change c (c.symm ((p t).mulVec (c v))) = c 0 at hcoords
    rw [c.apply_symm_apply, map_zero] at hcoords
    have hz : (p t).mulVec (c v) = (p t).mulVec 0 := by
      simpa only [Matrix.mulVec_zero] using hcoords
    apply hv
    apply c.injective
    exact ((Matrix.mulVec_injective_of_det_ne_zero (hp t).ne') hz).trans (map_zero c).symm
  have hf : Set.MapsTo f {v : V | v ≠ 0} {v : V | v ≠ 0} :=
    fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))
  have hid : Set.MapsTo (ContinuousMap.id V) {v : V | v ≠ 0} {v : V | v ≠ 0} :=
    fun _ hv ↦ hv
  have hmap := relativeSingularHomologyMap_eq_of_homotopy R hid hf H hH k
  refine hmap.symm.trans ?_
  simp [relativeSingularHomologyMap, relativeSingularChainsMap, cokernel.map]

end AtiyahSinger
