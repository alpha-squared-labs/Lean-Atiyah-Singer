/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# The original orthogonal action on the common Euclidean chart

Public module ID: M1329.

The matrix representation used by the sphere pole charts is a jointly smooth
Euclidean action for the same Cayley Lie-group atlas. This supplies the actual
common-open source of analytic excision in all dimensions, including zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Matrix.Norms.L2Operator

/-- The original orthogonal isometries act on their Euclidean representation space. -/
@[instance_reducible]
def orthogonalEuclideanMulAction (r : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℝ (Fin r)) where
  smul A u := orthogonalEuclideanIsometry r A u
  one_smul u := by
    change orthogonalEuclideanIsometry r 1 u = u
    rw [map_one]
    rfl
  mul_smul A B u := by
    change orthogonalEuclideanIsometry r (A * B) u =
      orthogonalEuclideanIsometry r A (orthogonalEuclideanIsometry r B u)
    rw [map_mul]
    rfl

/-- The matrix action is jointly smooth in the same original group and Euclidean models. -/
theorem contMDiffSMul_orthogonalEuclidean (r : ℕ) :
    letI := orthogonalEuclideanMulAction r
    ContMDiffSMul 𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞
      (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℝ (Fin r)) := by
  let := orthogonalEuclideanMulAction r
  let := lieGroup_orthogonalGroup r
  have hEntries := (contMDiff_orthogonalGroup_iff
    𝓘(ℝ, OrthogonalGroupModel r) r ∞ id).mp contMDiff_id
  constructor
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℝ)
  have hcoord : ContMDiff (𝓘(ℝ, OrthogonalGroupModel r).prod (𝓡 r))
      𝓘(ℝ, Fin r → ℝ) ∞
      (fun z : Matrix.orthogonalGroup (Fin r) ℝ × EuclideanSpace ℝ (Fin r) ↦
        fun i ↦ ∑ j, z.1.val i j * z.2 j) := by
    apply contMDiff_pi_space.mpr
    intro i
    apply ContMDiff.sum
    intro j _
    exact contDiff_mul.contMDiff.comp
      (((hEntries i j).comp contMDiff_fst).prodMk_space
        (((contDiff_apply ℝ (fun _ : Fin r ↦ ℝ) j).contMDiff.comp
          e.contDiff.contMDiff).comp contMDiff_snd))
  exact e.symm.contDiff.contMDiff.comp hcoord

end AtiyahSinger
