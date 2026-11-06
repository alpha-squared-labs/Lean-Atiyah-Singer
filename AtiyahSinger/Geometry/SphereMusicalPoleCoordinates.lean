/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereCotangentCoordinates

/-!
# Round musical transport in the actual pole coordinates

Public module ID: M1436.

The conformal pullback formula is upgraded to equality of full native
covectors. This is the metric comparison required before the common-open
analytic excision argument of ASI I Proposition (4.4), pp.504--505.
The real Riesz convention and original normalized chart are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxHeartbeats 2000000 in

/-- Round musical transport in the prescribed pole chart is the inverse-dual lift
of the Euclidean covector, multiplied by the positive conformal factor. -/
theorem orthogonalSphereNormalizedChart_roundFlat (r : ℕ) (atInfinity : Bool)
    (u v : EuclideanSpace ℝ (Fin r)) :
    (orthogonalSphereRoundMetric r).inner
        ((orthogonalSphereNormalizedChart r atInfinity).symm u)
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u v) =
      (4 / (1 + ‖u‖ ^ 2) ^ 2) •
        ((innerSL ℝ v).comp (mfderiv (𝓡 r) (𝓡 r)
          (orthogonalSphereNormalizedChart r atInfinity)
          ((orthogonalSphereNormalizedChart r atInfinity).symm u))) := by
  let e := orthogonalSphereNormalizedChart r atInfinity
  have ht : u ∈ e.target :=
    (orthogonalSphereNormalizedChart_properties r atInfinity).2.1.symm ▸ Set.mem_univ u
  have hs := orthogonalSphereNormalizedChart_smooth r atInfinity
  have hd : e.MDifferentiable (𝓡 r) (𝓡 r) :=
    ⟨hs.1.mdifferentiableOn (by simp), (hs.2.mdifferentiable (by simp)).mdifferentiableOn⟩
  -- Every native tangent vector is the image of its coordinate derivative.
  have hcancel (w : TangentSpace (𝓡 r) (e.symm u)) :
      mfderiv (𝓡 r) (𝓡 r) e.symm u (mfderiv (𝓡 r) (𝓡 r) e (e.symm u) w) = w := by
    have h := congrArg (fun L ↦ L w) (hd.symm_comp_deriv (e.map_target ht))
    rw [e.right_inv ht] at h
    exact h
  apply ContinuousLinearMap.ext
  intro w
  change (orthogonalSphereRoundMetric r).inner (e.symm u)
      (mfderiv (𝓡 r) (𝓡 r) e.symm u v) w =
    (4 / (1 + ‖u‖ ^ 2) ^ 2) * inner ℝ v (mfderiv (𝓡 r) (𝓡 r) e (e.symm u) w)
  -- Apply the conformal metric formula to the same vector, then cancel its chart derivative.
  have h := orthogonalSphereNormalizedChart_roundMetric r atInfinity u v
    (mfderiv (𝓡 r) (𝓡 r) e (e.symm u) w)
  change (orthogonalSphereRoundMetric r).inner (e.symm u)
    (mfderiv (𝓡 r) (𝓡 r) e.symm u v)
    (mfderiv (𝓡 r) (𝓡 r) e.symm u (mfderiv (𝓡 r) (𝓡 r) e (e.symm u) w)) = _ at h
  rw [hcancel] at h
  exact h

end AtiyahSinger
