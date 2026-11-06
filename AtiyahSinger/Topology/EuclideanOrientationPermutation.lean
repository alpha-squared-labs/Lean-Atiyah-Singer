/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationCycleNaturality
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The local orientation cycle under an actual coordinate permutation

Public module ID: M1823.

The matrix of the original coordinate permutation has its standard permutation
sign. Basis independence of the geometric simplex therefore gives the same
sign on local integral homology. This includes the empty permutation.

Source: the standard orientation comparison in Milnor--Stasheff, section 9.
The result relates the native coordinate map and the existing geometric cycle;
no Thom or duality normalization enters its proof.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Permuting Euclidean coordinates acts on the geometric local cycle by its actual sign. -/
theorem realOrientationCycle_piLpCongrLeft (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    let e := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toContinuousLinearEquiv
    let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    relativeSingularHomologyMap ℤ
      (⟨e, e.continuous⟩ : C(EuclideanSpace ℝ (Fin k), EuclideanSpace ℝ (Fin k)))
      (A := {v : EuclideanSpace ℝ (Fin k) | v ≠ 0})
      (B := {v : EuclideanSpace ℝ (Fin k) | v ≠ 0})
      (fun _ hv heq ↦ hv (e.injective (heq.trans e.map_zero.symm))) k
      (realOrientationCycle b b.orientation) =
        (σ.sign : ℤ) • realOrientationCycle b b.orientation := by
  classical
  dsimp only
  let e := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toContinuousLinearEquiv
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  -- The native permutation sends each standard basis vector to its indexed image.
  have he (i : Fin k) : e (b i) = b (σ i) := by
    change LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
      ((EuclideanSpace.basisFun (Fin k) ℝ) i) = (EuclideanSpace.basisFun (Fin k) ℝ) (σ i)
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single,
      EuclideanSpace.basisFun_apply]
  have hm : LinearMap.toMatrix b b e.toLinearMap =
      (1 : Matrix (Fin k) (Fin k) ℝ).submatrix id σ := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (e (b j)) i = _
    rw [he, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, Matrix.submatrix_apply, id_eq, Matrix.one_apply, eq_comm]
  have hd : LinearMap.det e.toLinearMap = (σ.sign : ℤ) := by
    rw [← LinearMap.det_toMatrix b, hm, Matrix.det_permute', Matrix.det_one, mul_one]
  -- Basis independence converts the determinant orientation into the original cycle sign.
  rw [realOrientationCycle_map_basis]
  rcases Int.units_eq_one_or σ.sign with hs | hs
  · have hpos : 0 < LinearMap.det e.toLinearMap := by rw [hd, hs]; norm_num
    have ho : (b.map e.toLinearEquiv).orientation = b.orientation :=
      (b.orientation_comp_linearEquiv_eq_iff_det_pos e.toLinearEquiv).mpr hpos
    rw [ho, realOrientationCycle_basis_independent (b.map e.toLinearEquiv) b, hs]
    simp only [Units.val_one, one_smul]
    rfl
  · have hneg : LinearMap.det e.toLinearMap < 0 := by rw [hd, hs]; norm_num
    have ho : (b.map e.toLinearEquiv).orientation = -b.orientation :=
      (b.orientation_comp_linearEquiv_eq_neg_iff_det_neg e.toLinearEquiv).mpr hneg
    rw [ho, realOrientationCycle_basis_independent (b.map e.toLinearEquiv) b, hs]
    simp only [Units.val_neg, Units.val_one]
    change realOrientationCycle b (-b.orientation) = (-1 : ℤ) • realOrientationCycle b b.orientation
    rw [neg_one_zsmul]
    unfold realOrientationCycle
    rw [← map_neg]
    congr 1
    apply Subtype.ext
    change realOrientationRelativeChain b (-b.orientation) =
      -realOrientationRelativeChain b b.orientation
    simp only [realOrientationRelativeChain, Module.Ray.ne_neg_self, ite_false, ite_true]
    erw [← map_neg, ← map_neg]
    rfl

end AtiyahSinger
