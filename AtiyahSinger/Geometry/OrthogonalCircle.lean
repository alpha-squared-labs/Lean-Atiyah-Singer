/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSphere
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The native orthogonal one-sphere as the complex unit circle

Public module ID: M1328.

The sphere used for the O(1) action is the unit sphere in the genuine Euclidean
product `ℝ¹ ⊕ ℝ`. Its horizontal coordinate is the real part and its height is
the imaginary part of the original `Circle`. Both manifolds retain their
native sphere atlases. Thus the north and south poles correspond to `I` and
`-I`; a reversal in a pole chart changes both normal and tangent coordinates.

This elementary coordinate comparison implements the identification of the
circle in ASI I, section 8, pp.525--526 with the sphere used in Lemma (3.2),
pp.499--500. The exact coordinate map is a project supplement. No equivariance
with the multiplicative action of Circle is asserted: O(1) acts on the original
horizontal coordinate while fixing height.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

/-- The actual horizontal-plus-imaginary-height map is a native sphere diffeomorphism. -/
theorem exists_orthogonalCircleDiffeomorph :
    ∃ e : OrthogonalSphere 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle,
      ∀ x, (e x : ℂ) = (x.val.fst 0 : ℂ) + (x.val.snd : ℂ) * Complex.I := by
  /- Stage 1: evaluation at the unique coordinate identifies the actual
  EuclideanSpace ℝ (Fin 1) isometrically with ℝ. Pairing this coordinate with
  the unchanged height identifies the ambient L² product with ℂ as real
  inner-product spaces, by (u,t) ↦ u(0)+i*t. Its inverse takes real and
  imaginary parts and inserts the former into the unique horizontal slot.
  Stage 2: equality of the original Euclidean and complex norms restricts
  these inverse maps to the two original unit spheres. Their restrictions
  are smooth in the native sphere atlases because both ambient maps are
  real linear. The same restrictions and their inverses therefore give
  a diffeomorphism with the displayed full coordinate specification. -/
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  -- Identify the ambient spaces by the specified horizontal and height coordinates.
  let horizontal : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let ambient : OrthogonalSphereAmbient 1 ≃L[ℝ] ℂ :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 1)) ℝ).trans
      (horizontal.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))).trans
      Complex.equivRealProdCLM.symm
  have hFormula (x : OrthogonalSphereAmbient 1) :
      ambient x = (x.fst 0 : ℂ) + (x.snd : ℂ) * Complex.I := by
    simp [ambient, horizontal, Complex.equivRealProdCLM_symm_apply]
  -- Equality of the genuine L² and complex norms restricts both inverse maps to spheres.
  have hNorm (x : OrthogonalSphereAmbient 1) : ‖ambient x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hFormula, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq]
    simp [pow_two]
  let sphereEquiv : OrthogonalSphere 1 ≃ Circle :=
    { toFun := fun x ↦ ⟨ambient x.val, by
        change ambient x.val ∈ Metric.sphere (0 : ℂ) 1
        simpa only [Metric.mem_sphere, dist_zero_right, hNorm] using x.property⟩
      invFun := fun z ↦ ⟨ambient.symm z.val, by
        have hz : ‖z.val‖ = 1 := Circle.norm_coe z
        simpa only [Metric.mem_sphere, dist_zero_right, ← hNorm,
          ambient.apply_symm_apply] using hz⟩
      left_inv := fun x ↦ Subtype.ext (ambient.symm_apply_apply x.val)
      right_inv := fun z ↦ Subtype.ext (ambient.apply_symm_apply z.val) }
  -- The ambient linear maps are smooth; restriction retains both native sphere atlases.
  let smoothEquiv : OrthogonalSphere 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
    { sphereEquiv with
      contMDiff_toFun := by
        apply ContMDiff.codRestrict_sphere
        exact ambient.contDiff.contMDiff.comp contMDiff_coe_sphere
      contMDiff_invFun := by
        apply ContMDiff.codRestrict_sphere
        exact ambient.symm.contDiff.contMDiff.comp contMDiff_coe_sphere }
  exact ⟨smoothEquiv, fun x ↦ hFormula x.val⟩

/-- The prescribed real-linear coordinate identification on the two original circle manifolds. -/
def orthogonalCircleDiffeomorph : OrthogonalSphere 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  exists_orthogonalCircleDiffeomorph.choose

/-- The chosen diffeomorphism retains horizontal coordinate and height in that order. -/
theorem orthogonalCircleDiffeomorph_apply (x : OrthogonalSphere 1) :
    (orthogonalCircleDiffeomorph x : ℂ) =
      (x.val.fst 0 : ℂ) + (x.val.snd : ℂ) * Complex.I := by
  /- Recover the coordinate equality from the exact existence witness used
  in orthogonalCircleDiffeomorph. This is the original real-linear map,
  not a freely chosen diffeomorphism or an orientation selected by an index. -/
  exact exists_orthogonalCircleDiffeomorph.choose_spec x

end AtiyahSinger
