/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexifiedTangentCovectors
public import AtiyahSinger.Geometry.SphereComplexifiedTangent

/-!
# The original sphere contraction covector

Public module ID: M1430.

The original conjugate-first Hermitian metric on the complexified sphere tangent
bundle pairs a real tangent vector with precisely the evaluation covector of the
specified round musical map. This fixes the contraction normalization used by
both the original Koszul symbol and the actual differential form identification.

Source: the metric exterior realization in Lawson--Michelsohn, Spin Geometry, II.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff TensorProduct

attribute [local instance] sphereComplexifiedTangentTopology

set_option backward.isDefEq.respectTransparency false in
/-- The original sphere Hermitian contraction agrees with the round musical evaluation. -/
theorem sphereComplexifiedRoundMetric_inner_one_tmul (r : ℕ) (x : OrthogonalSphere r)
    (v : TangentSpace (𝓡 r) x) (z : SphereComplexifiedTangent r x) :
    ((sphereComplexifiedRoundMetric r).toCore x).inner ((1 : ℂ) ⊗ₜ[ℝ] v) z =
      complexifiedTangentCovectorMap (orthogonalSphereRoundMetric r) x z v := by
  let V := TangentSpace (𝓡 r) x
  let g := orthogonalSphereRoundMetric r
  let u := (complexificationReIm V z).1
  let w := (complexificationReIm V z).2
  have hz : z = (1 : ℂ) ⊗ₜ[ℝ] u + Complex.I ⊗ₜ[ℝ] w :=
    ((complexificationReIm V).symm_apply_apply z).symm.trans
      ((complexificationReIm_properties V).2.1 u w)
  have hmap : complexifiedTangentCovectorMap g x z v =
      (g.inner x u v : ℂ) + Complex.I * (g.inner x w v : ℂ) := by
    rw [hz, map_add]
    change (1 : ℂ) * (g.inner x u v : ℂ) + Complex.I * (g.inner x w v : ℂ) = _
    rw [one_mul]
  rw [sphereComplexifiedRoundMetric_inner]
  change sphereComplexifiedRoundPairing r x ((1 : ℂ) ⊗ₜ[ℝ] v) z =
    complexifiedTangentCovectorMap g x z v
  rw [hmap]
  have hreal : complexificationReIm (TangentSpace (𝓡 r) x) ((1 : ℂ) ⊗ₜ[ℝ] v) = (v, 0) := by
    simpa only [Complex.one_re, Complex.one_im, one_smul, zero_smul] using
      (complexificationReIm_properties (TangentSpace (𝓡 r) x)).1 1 v
  simp only [sphereComplexifiedRoundPairing, hreal, map_zero, zero_apply, add_zero, sub_zero]
  change (g.inner x v u : ℂ) + Complex.I * (g.inner x v w : ℂ) = _
  rw [g.symm x v u, g.symm x v w]

end AtiyahSinger
