/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentModelChange

/-!
# The inverse of the specified cotangent model change

Public module ID: M1154.

The inverse homeomorphism composes the entire covector with the original
linear model map. This formula retains the base point and the actual model
change, including when the linear map is not an isometry.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (e : E ≃L[ℝ] F) (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse cotangent homeomorphism retains the full covector and base point. -/
theorem cotangentLinearModelHomeomorph_symm_apply :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    ∀ z : TotalSpace (F →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ),
      (cotangentLinearModelHomeomorph e M).symm z =
        ⟨z.proj, z.snd.comp e.toContinuousLinearMap⟩ := by
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  intro z
  apply (cotangentLinearModelHomeomorph e M).injective
  rw [Homeomorph.apply_symm_apply]
  -- The forward map composes with the inverse model map, canceling the same original map.
  change z = ⟨z.proj, (z.snd.comp e.toContinuousLinearMap).comp e.symm.toContinuousLinearMap⟩
  cases z with
  | mk x ξ =>
    congr 1
    ext v
    exact congrArg ξ (e.apply_symm_apply v).symm

end AtiyahSinger
