/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSphere

/-!
# Equivariant stereographic coordinates for the orthogonal sphere

Public module ID: M1337.

This is the fixed-pole coordinate comparison needed for the sphere construction
in SG III.13, page 251. It uses mathlib's original `stereographic` map and the
explicit horizontal isometry `(x, 0) ↦ x`, rather than a coordinate isometry
chosen solely from dimension. Thus its equivariance refers to precisely the
block action from `OrthogonalSphere`.

Mathlib normalizes stereographic projection as `2 x / (1 - t)`. Multiplication
by this scalar factor commutes with the orthogonal action; no alternative
normalization is silently substituted. The north pole is excluded from the
chart source, and the zero vector corresponds to the opposite pole.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The explicit horizontal-coordinate isometry at the specified north pole. -/
def orthogonalSphereHorizontalIsometry (r : ℕ) :
    (ℝ ∙ (orthogonalSphereNorth r : OrthogonalSphereAmbient r))ᗮ ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin r) where
  toFun z := z.val.fst
  invFun x := ⟨WithLp.toLp 2 (x, (0 : ℝ)), by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    simp [orthogonalSphereNorth, WithLp.prod_inner_apply]⟩
  left_inv z := by
    -- Orthogonality to (0, 1) makes the final coordinate vanish.
    have hz : z.val.snd = 0 := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property
      simpa [orthogonalSphereNorth, WithLp.prod_inner_apply, RCLike.inner_apply] using h
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext rfl hz.symm
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl
  norm_map' z := by
    -- On this hyperplane the L² norm is exactly the norm of the first coordinate.
    have hz : z.val.snd = 0 := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property
      simpa [orthogonalSphereNorth, WithLp.prod_inner_apply, RCLike.inner_apply] using h
    have heq : z.val = WithLp.toLp 2 (z.val.fst, (0 : ℝ)) :=
      WithLp.ofLp_injective 2 (Prod.ext rfl hz)
    change ‖z.val.fst‖ = ‖z.val‖
    rw [heq]
    simp

/-- Stereographic projection at the fixed north pole with actual horizontal coordinates. -/
def orthogonalSphereStereographic (r : ℕ) :
    OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)) :=
  (stereographic (norm_eq_of_mem_sphere (orthogonalSphereNorth r))).trans
    (orthogonalSphereHorizontalIsometry r).toHomeomorph.toOpenPartialHomeomorph

/-- The fixed-pole chart identifies the sphere minus north with the orthogonal representation. -/
theorem orthogonalSphereStereographic_properties (r : ℕ) :
    (orthogonalSphereStereographic r).source = {orthogonalSphereNorth r}ᶜ ∧
      (orthogonalSphereStereographic r).target = Set.univ ∧
      ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r),
        z ∈ (orthogonalSphereStereographic r).source →
        orthogonalSphereStereographic r (A • z) =
          orthogonalEuclideanIsometry r A (orthogonalSphereStereographic r z) := by
  /- Stage 1: the original stereographic source is the complement of the
  supplied north vector, and its target is the whole orthogonal hyperplane.
  Composing with the total horizontal isometry preserves the source and sends
  the target onto the whole Euclidean space.
  Stage 2: the block isometry fixes north, so both sphere points lie in the
  chart source. It commutes with orthogonal projection onto the horizontal
  hyperplane and preserves the inner product with the pole. Thus in 2x/(1-t)
  only x changes to A x. The explicit horizontal isometry identifies this
  action with the original matrix representation using the same scalar factor. -/
  let pole : OrthogonalSphereAmbient r := orthogonalSphereNorth r
  -- The original orthogonal projection retains exactly the horizontal coordinate.
  have hProjection (x : OrthogonalSphereAmbient r) :
      orthogonalSphereHorizontalIsometry r
        ((ℝ ∙ pole)ᗮ.orthogonalProjectionOnto x) = x.fst := by
    change ((ℝ ∙ pole)ᗮ.orthogonalProjectionOnto x).val.fst = x.fst
    rw [Submodule.orthogonalProjectionOnto_orthogonal]
    change (x - (ℝ ∙ pole).starProjection x).fst = x.fst
    rw [Submodule.starProjection_unit_singleton ℝ
        (norm_eq_of_mem_sphere (orthogonalSphereNorth r))]
    simp [orthogonalSphereNorth]
  have hFormula (z : OrthogonalSphere r) :
      orthogonalSphereStereographic r z = (2 / (1 - z.val.snd)) • z.val.fst := by
    change orthogonalSphereHorizontalIsometry r
      (stereographic (norm_eq_of_mem_sphere (orthogonalSphereNorth r)) z) = _
    rw [stereographic_apply, map_smul, hProjection]
    simp [orthogonalSphereNorth, WithLp.prod_inner_apply, RCLike.inner_apply]
  -- Composing with the total horizontal isometry leaves the source and target unchanged.
  refine ⟨?_, ?_, ?_⟩
  · simp [orthogonalSphereStereographic]
  · simp [orthogonalSphereStereographic]
  · intro A z _
    -- The fixed line leaves the denominator intact; linearity transports the same factor 2.
    rw [hFormula, hFormula]
    change (2 / (1 - z.val.snd)) • orthogonalEuclideanIsometry r A z.val.fst =
      orthogonalEuclideanIsometry r A ((2 / (1 - z.val.snd)) • z.val.fst)
    rw [map_smul]

end AtiyahSinger
