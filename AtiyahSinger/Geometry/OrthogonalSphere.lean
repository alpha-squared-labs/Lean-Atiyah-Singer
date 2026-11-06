/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The orthogonal action on the sphere of a vector space plus a line

Public module ID: M1334.

SG, Chapter III, page 251, uses the action of `O(r)` on `S^r` induced by
`(x, t) ↦ (A x, t)`. The ambient product below has its genuine Euclidean
`L²` norm. Its north pole is fixed, including when `r = 0` and the sphere
consists of two points. No orientation, spin structure, or positive-rank
assumption is imposed.

The action uses mathlib's matrix orthogonal group and native sphere manifold.
Smoothness is asserted for each fixed group element; a Lie-group atlas on
the orthogonal group is not supplied by this interface.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

/-- The Euclidean direct sum underlying the fiberwise sphere compactification. -/
abbrev OrthogonalSphereAmbient (r : ℕ) : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin r) × ℝ)

/-- The unit sphere `S^r` in `ℝ^r ⊕ ℝ`, including the rank-zero case. -/
abbrev OrthogonalSphere (r : ℕ) : Type :=
  Metric.sphere (0 : OrthogonalSphereAmbient r) 1

/-- The standard orthogonal matrix representation on Euclidean space. -/
def orthogonalEuclideanIsometry (r : ℕ) :
    Matrix.orthogonalGroup (Fin r) ℝ →*
      (EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    (Unitary.map
      (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)))).toMonoidHom

/-- The actual block representation `diag(A, 1)` on the Euclidean direct sum. -/
def orthogonalSphereBlockIsometry (r : ℕ) :
    Matrix.orthogonalGroup (Fin r) ℝ →*
      (OrthogonalSphereAmbient r ≃ₗᵢ[ℝ] OrthogonalSphereAmbient r) where
  toFun A := LinearIsometryEquiv.withLpProdCongr 2
    (orthogonalEuclideanIsometry r A) (LinearIsometryEquiv.refl ℝ ℝ)
  map_one' := by
    ext x
    change WithLp.toLp 2 ((orthogonalEuclideanIsometry r 1) x.fst, x.snd) = x
    rw [map_one]
    rfl
  map_mul' A B := by
    ext x
    change WithLp.toLp 2 ((orthogonalEuclideanIsometry r (A * B)) x.fst, x.snd) =
      WithLp.toLp 2
        ((orthogonalEuclideanIsometry r A) ((orthogonalEuclideanIsometry r B) x.fst),
          x.snd)
    rw [map_mul]
    rfl

/-- Restriction of the specified block representation to the actual unit sphere. -/
instance orthogonalSphereMulAction (r : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ) (OrthogonalSphere r) where
  smul A z := ⟨orthogonalSphereBlockIsometry r A z.val, by
    simpa only [Metric.mem_sphere, dist_zero_right,
      (orthogonalSphereBlockIsometry r A).norm_map] using z.property⟩
  one_smul z := by
    apply Subtype.ext
    change orthogonalSphereBlockIsometry r 1 z.val = z.val
    rw [map_one]
    rfl
  mul_smul A B z := by
    apply Subtype.ext
    change orthogonalSphereBlockIsometry r (A * B) z.val =
      orthogonalSphereBlockIsometry r A (orthogonalSphereBlockIsometry r B z.val)
    rw [map_mul]
    rfl

/-- The distinguished north pole, whose orbit gives the infinity section. -/
def orthogonalSphereNorth (r : ℕ) : OrthogonalSphere r :=
  ⟨WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin r)), (1 : ℝ)), by simp⟩

/-- Dimension certificate selecting mathlib's native `r`-sphere manifold instances. -/
instance orthogonalSphereAmbientFinrank (r : ℕ) :
    Fact (Module.finrank ℝ (OrthogonalSphereAmbient r) = r + 1) where
  out := by
    rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin r) × ℝ)).finrank_eq]
    simp [Module.finrank_prod]

/-- The orthogonal action is jointly continuous for the native matrix and sphere topologies. -/
theorem continuousSMul_orthogonalSphere (r : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ) (OrthogonalSphere r) := by
  /- First use Matrix.continuous_uncurry_toEuclideanCLM on the matrix and
  horizontal coordinates. Pair this with the unchanged last coordinate in the
  L²-product topology. The norm-preserving block representation maps the sphere
  into itself, so the continuous ambient action restricts to the sphere subtype. -/
  -- First establish joint continuity of the specified ambient block action.
  have hPair : Continuous
      (fun p : Matrix.orthogonalGroup (Fin r) ℝ × OrthogonalSphere r ↦
        (p.1.val, p.2.val.fst)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((WithLp.continuous_fst 2 _ _).comp (continuous_subtype_val.comp continuous_snd))
  have hHorizontal :=
    (Matrix.continuous_uncurry_toEuclideanCLM (n := Fin r) (𝕜 := ℝ)).comp hPair
  have hVertical : Continuous
      (fun p : Matrix.orthogonalGroup (Fin r) ℝ × OrthogonalSphere r ↦ p.2.val.snd) :=
    (WithLp.continuous_snd 2 _ _).comp (continuous_subtype_val.comp continuous_snd)
  constructor
  -- Restriction to the sphere leaves its native subtype topology unchanged.
  exact ((WithLp.prod_continuous_toLp 2 _ _).comp
    (hHorizontal.prodMk hVertical)).subtype_mk _

/-- The block action fixes the north pole used for fiberwise compactification. -/
theorem smul_orthogonalSphereNorth (r : ℕ) (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    A • orthogonalSphereNorth r = orthogonalSphereNorth r := by
  /- The matrix representation sends the zero horizontal coordinate to zero
  and the trivial line representation leaves the last coordinate equal to one.
  Subtype extensionality then gives equality of the actual sphere points. -/
  apply Subtype.ext
  change WithLp.toLp 2 ((orthogonalEuclideanIsometry r A) 0, (1 : ℝ)) =
    WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin r)), (1 : ℝ))
  rw [map_zero]

/-- Each fixed orthogonal transformation acts smoothly on mathlib's native sphere manifold. -/
theorem contMDiff_orthogonalSphere_smul (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    ContMDiff (𝓡 r) (𝓡 r) ∞ (fun z : OrthogonalSphere r ↦ A • z) := by
  /- Compose the smooth sphere inclusion with the continuous linear block
  isometry. The resulting smooth ambient map lands in the sphere because the
  block map preserves norms. Apply ContMDiff.codRestrict_sphere for the same
  native atlas. This asserts fixed-element smoothness, not a joint Lie action. -/
  -- Compose in the ambient Euclidean direct sum using the original block isometry.
  have hAmbient : ContMDiff (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ∞
      (fun z : OrthogonalSphere r ↦ orthogonalSphereBlockIsometry r A z.val) :=
    (orthogonalSphereBlockIsometry r A).toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_coe_sphere
  -- Restrict to the same native sphere atlas, using its norm preservation.
  exact hAmbient.codRestrict_sphere (fun z ↦ (A • z).property)

end AtiyahSinger
