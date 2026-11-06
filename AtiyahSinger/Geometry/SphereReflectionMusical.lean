/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereMusical

/-!
# Musical naturality for the original sphere reflection

Public module ID: M1439.

The derivative lift and the inverse-dual cotangent lift of the same vertical
reflection commute with the specified round musical map. This supplies the
actual geometric square required by tangent analytic-index naturality.
The second theorem retains the native orthogonal cotangent action.

This is the usual naturality of metric duality under a Riemannian isometry,
specialized to the existing sphere, round metric, and ambient reflection.
No invariance under tangent-fiber negation is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent

/-- Inverse round metric duality intertwines the two lifts of the same vertical reflection. -/
theorem orthogonalSphereRoundMetric_flat_symm_reflection (r : ℕ)
    (z : CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :
    (orthogonalSphereRoundMetric r).flatHomeomorph.symm
        (cotangentDiffeomorph (orthogonalSphereVerticalDiffeomorph r) z) =
      orthogonalSphereVerticalTangentHomeomorph r
        ((orthogonalSphereRoundMetric r).flatHomeomorph.symm z) := by
  let g := orthogonalSphereRoundMetric r
  let D := orthogonalSphereVerticalDiffeomorph r
  -- Differentiate the actual ambient reflection before using its metric invariance.
  have hMetric (x : OrthogonalSphere r) (v w : TangentSpace (𝓡 r) x) :
      g.inner (D x) (mfderiv (𝓡 r) (𝓡 r) D x v)
        (mfderiv (𝓡 r) (𝓡 r) D x w) = g.inner x v w := by
    let ι : OrthogonalSphere r → OrthogonalSphereAmbient r := fun y ↦ y.val
    let L := (orthogonalSphereVerticalIsometry r).toContinuousLinearEquiv
    have hι : MDifferentiable (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι :=
      (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
    have hD : MDifferentiable (𝓡 r) (𝓡 r) D := D.mdifferentiable (by simp)
    have hcomm : ι ∘ D = L ∘ ι := rfl
    have hchain (u : TangentSpace (𝓡 r) x) :
        mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι (D x)
            (mfderiv (𝓡 r) (𝓡 r) D x u) =
          L (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι x u) := by
      rw [← mfderiv_comp_apply x (hι (D x)) (hD x) u, hcomm,
        mfderiv_comp_apply x L.mdifferentiableAt (hι x) u,
        ContinuousLinearEquiv.mfderiv_eq]
      rfl
    rw [orthogonalSphereRoundMetric_inner, orthogonalSphereRoundMetric_inner]
    change @inner ℝ (OrthogonalSphereAmbient r) inferInstance
      (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι (D x)
        (mfderiv (𝓡 r) (𝓡 r) D x v))
      (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι (D x)
        (mfderiv (𝓡 r) (𝓡 r) D x w)) = _
    rw [hchain v, hchain w]
    exact (orthogonalSphereVerticalIsometry r).inner_map_map _ _
  -- The derivative of the inverse acts on the exact reflected native tangent fiber.
  have hInverse (x : OrthogonalSphere r) (w : TangentSpace (𝓡 r) (D x)) :
      mfderiv (𝓡 r) (𝓡 r) D x (mfderiv (𝓡 r) (𝓡 r) D.symm (D x) w) = w := by
    have hd := mfderiv_comp (D x) (D.mdifferentiable (by simp) (D.symm (D x)))
      (D.symm.mdifferentiable (by simp) (D x))
    have he : (D : OrthogonalSphere r → OrthogonalSphere r) ∘ D.symm = id :=
      funext D.apply_symm_apply
    rw [he, mfderiv_id] at hd
    change ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin r)) =
      (mfderiv (𝓡 r) (𝓡 r) D (D.symm (D x))).comp
        (mfderiv (𝓡 r) (𝓡 r) D.symm (D x)) at hd
    rw [D.symm_apply_apply] at hd
    exact congrArg (fun f : EuclideanSpace ℝ (Fin r) →L[ℝ]
      EuclideanSpace ℝ (Fin r) ↦ f w) hd.symm
  have hForward (v : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
      g.flatHomeomorph (orthogonalSphereVerticalTangentHomeomorph r v) =
        cotangentDiffeomorph D (g.flatHomeomorph v) := by
    change (⟨D v.proj, g.inner (D v.proj) (mfderiv (𝓡 r) (𝓡 r) D v.proj v.snd)⟩ :
      CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) =
      ⟨D v.proj, (g.inner v.proj v.snd).comp (mfderiv (𝓡 r) (𝓡 r) D.symm (D v.proj))⟩
    congr 1
    ext w
    change g.inner (D v.proj) (mfderiv (𝓡 r) (𝓡 r) D v.proj v.snd) w =
      g.inner v.proj v.snd (mfderiv (𝓡 r) (𝓡 r) D.symm (D v.proj) w)
    conv_lhs => rw [← hInverse v.proj w]
    exact hMetric v.proj v.snd (mfderiv (𝓡 r) (𝓡 r) D.symm (D v.proj) w)
  -- Transfer the same commutative square through the chosen musical homeomorphism.
  apply g.flatHomeomorph.injective
  rw [g.flatHomeomorph.apply_symm_apply, hForward, g.flatHomeomorph.apply_symm_apply]

/-- The cotangent lift of vertical reflection commutes with the original orthogonal action. -/
theorem orthogonalSphereVerticalCotangent_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ)
    (z : CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :
    cotangentDiffeomorph (orthogonalSphereVerticalDiffeomorph r) (A • z) =
      A • cotangentDiffeomorph (orthogonalSphereVerticalDiffeomorph r) z := by
  -- All three maps intertwine the same native action, so their composite does too.
  apply (orthogonalSphereRoundMetric r).flatHomeomorph.symm.injective
  rw [orthogonalSphereRoundMetric_flat_symm_reflection,
    orthogonalSphereRoundMetric_flat_symm_equivariant,
    orthogonalSphereVerticalTangentHomeomorph_equivariant,
    orthogonalSphereRoundMetric_flat_symm_equivariant,
    orthogonalSphereRoundMetric_flat_symm_reflection]

end AtiyahSinger
