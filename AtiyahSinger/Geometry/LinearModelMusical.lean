/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentModelChange
public import AtiyahSinger.Geometry.LinearModelTangentMetric
public import AtiyahSinger.Geometry.TangentMusicalDiffeomorph

/-!
# The actual musical square for a full linear model change

Public module ID: M1289.

The original full-model metric gives its native musical map. The specified
linear model change gives the native inverse-dual cotangent map. Pulling the
metric into the Euclidean atlas makes their composite agree with the actual
tangent map followed by that same transported metric's musical map.
The homeomorphism of tangent spaces is characterized by its exact original
pointwise linear formula, not by a dimension comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (M : Type*) [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℝ, V) ∞ M]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The native metric, its Euclidean transport, and the actual linear model maps commute. -/
theorem exists_linearModelMusical_comparison
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (TangentSpace 𝓘(ℝ, V) : M → Type _)) :
    letI : FiniteDimensional ℝ V := .of_injective e.toLinearMap e.injective
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    let d := (exists_tangentMusical_diffeomorph h).choose
    let c := cotangentLinearModelHomeomorph e M
    ∃ g : SmoothTangentMetric (n := n) (M := M),
      ∃ t : TangentBundle 𝓘(ℝ, V) M ≃ₜ TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M,
        (∀ z, t z = ⟨z.proj, e z.snd⟩) ∧
          d.toHomeomorph.trans c = t.trans g.flatHomeomorph := by
  classical
  let : FiniteDimensional ℝ V := .of_injective e.toLinearMap e.injective
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let d := (exists_tangentMusical_diffeomorph h).choose
  let c := cotangentLinearModelHomeomorph e M
  obtain ⟨g, hg⟩ := exists_linearModelTangentMetric e M h
  let t := (d.toHomeomorph.trans c).trans g.flatHomeomorph.symm
  refine ⟨g, t, ?_, ?_⟩
  · intro z
    -- The exact inverse-dual formula and the transported bilinear form recover e on tangents.
    apply g.flatHomeomorph.injective
    change g.flatHomeomorph (g.flatHomeomorph.symm (c (d z))) = _
    rw [g.flatHomeomorph.apply_symm_apply]
    rw [(exists_tangentMusical_diffeomorph h).choose_spec z]
    change (⟨z.proj, (h.inner z.proj z.snd).comp e.symm.toContinuousLinearMap⟩ :
      CotangentTotalSpace (n := n) (M := M)) = ⟨z.proj, g.inner z.proj (e z.snd)⟩
    congr 1
    apply ContinuousLinearMap.ext
    intro w
    change h.inner z.proj z.snd (e.symm w) = g.inner z.proj (e z.snd) w
    rw [hg, e.symm_apply_apply]
  · -- This square uses the very same two musical maps and cotangent model transport.
    apply Homeomorph.ext
    intro z
    change c (d z) = g.flatHomeomorph (g.flatHomeomorph.symm (c (d z)))
    exact (g.flatHomeomorph.apply_symm_apply _).symm

end AtiyahSinger
