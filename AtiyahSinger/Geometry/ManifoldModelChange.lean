/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# An explicit linear change of the full manifold model

Public module ID: M1300.

A specified continuous linear equivalence `e : E ≃L[ℝ] F` changes each old
chart `φ` to `e ∘ φ`, keeping the original manifold points and topology.
The construction reuses mathlib's singleton atlas and `ChartedSpace.comp`.
Its identity diffeomorphism has differential `e`, with inverse differential
`e.symm`, in the two specified full models.

Mathlib's `ModelWithCorners.transContinuousLinearEquiv` and
`ContinuousLinearEquiv.toTransContinuousLinearEquiv` already change the
vector model while retaining the old chart target. The present adapter is
needed when a downstream interface requires charts in `F` and the full model
`𝓘(ℝ, F)` itself. It does not infer equality of models from equal dimension.

This standard coordinate-change construction supplements the manifold
bookkeeping used in SG III.1 and III.13. No finite-dimensionality, separation,
compactness, metric or orientation premise is needed for the comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The old charts followed by the specified linear equivalence, on the same topological space. -/
@[instance_reducible]
def linearModelChartedSpace (e : E ≃L[ℝ] F) (M : Type*)
    [TopologicalSpace M] [ChartedSpace E M] : ChartedSpace F M := by
  letI : ChartedSpace F E :=
    e.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace rfl
  exact ChartedSpace.comp F E M

variable (e : E ≃L[ℝ] F) (M : Type*) [TopologicalSpace M]
  [cM : ChartedSpace E M] [hM : IsManifold 𝓘(ℝ, E) ∞ M]

include hM in
/-- Conjugating the original smooth chart transitions gives the specified full-model atlas. -/
theorem isManifold_linearModelChartedSpace :
    letI := linearModelChartedSpace e M
    IsManifold 𝓘(ℝ, F) ∞ M := by
  /- Stage 1: unfold only the two existing charted-space constructions. Every
  new chart is an original chart followed by the fixed homeomorphism e, so
  its source is unchanged and its target is the e-image of the old target.
  Stage 2: each new transition is e after an original transition after e.symm.
  Both linear maps are smooth; compose with the original transition on its
  actual overlap. Apply the standard smooth-atlas criterion. All topology
  and covering data are those supplied by the reused atlas constructions. -/
  let := linearModelChartedSpace e M
  apply isManifold_of_contDiffOn 𝓘(ℝ, F) ∞ M
  -- Every new atlas member is an old chart followed by the specified e.
  rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
  change b ∈ {e.toHomeomorph.toOpenPartialHomeomorph} at hb
  change b' ∈ {e.toHomeomorph.toOpenPartialHomeomorph} at hb'
  obtain rfl := Set.mem_singleton_iff.mp hb
  obtain rfl := Set.mem_singleton_iff.mp hb'
  have htransition := (contDiffGroupoid ∞ 𝓘(ℝ, E)).compatible ha ha'
  have hs : ContDiffOn ℝ ∞ (a' ∘ a.symm)
      (a.target ∩ a.symm ⁻¹' a'.source) := by
    simpa only [contDiffPregroupoid, mfld_simps] using htransition.1
  -- The two actual linear coordinate maps conjugate this original transition.
  simpa only [mfld_simps, Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.preimage, Set.inter_def] using
    e.contDiff.comp_contDiffOn
      (hs.comp e.symm.contDiff.contDiffOn
        (Set.mapsTo_preimage e.symm (a.target ∩ a.symm ⁻¹' a'.source)))

include hM in
set_option linter.unusedSectionVars false in
/-- Identity between the two specified atlases is smooth with the exact two linear derivatives. -/
theorem contMDiff_mfderiv_linearModelId :
    letI := linearModelChartedSpace e M
    (ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (id : M → M) ∧
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (id : M → M)) ∧
      (∀ x : M, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (id : M → M) x =
        (e : E →L[ℝ] F)) ∧
      (∀ x : M, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (id : M → M) x =
        (e.symm : F →L[ℝ] E)) := by
  /- Stage 1: use the original source atlas and exactly the target atlas
  linearModelChartedSpace e M. Near each original point x, the coordinate
  expression of the identity is e: the old chart cancels its inverse on
  their actual common domain. In the other direction it is e.symm.
  Stage 2: continuous linear maps are smooth of every order, so these local
  expressions give the two global smoothness statements. The underlying
  functions are the literal identity of the unchanged topological space.
  Stage 3: the two models are full vector spaces. Their chart targets are
  open neighborhoods, so the derivatives of the same coordinate expressions
  are the actual continuous linear maps e and e.symm. Transfer these local
  equalities to mfderiv at x. The result is not an identity matrix unless the
  specified model change itself is identity. -/
  let := linearModelChartedSpace e M
  -- In the preferred charts, the two literal identity maps are locally e and e.symm.
  have hforward (x : M) :
      writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x (id : M → M) =ᶠ[
        𝓝 (extChartAt 𝓘(ℝ, E) x x)] e := by
    filter_upwards [(chartAt E x).open_target.mem_nhds
      ((chartAt E x).map_source (mem_chart_source E x))] with z hz
    change e ((chartAt E x) ((chartAt E x).symm z)) = e z
    rw [(chartAt E x).right_inv hz]
  have hreverse (x : M) :
      writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, E) x (id : M → M) =ᶠ[
        𝓝 (extChartAt 𝓘(ℝ, F) x x)] e.symm := by
    have hmem : e.symm (extChartAt 𝓘(ℝ, F) x x) ∈ (chartAt E x).target := by
      change e.symm (e ((chartAt E x) x)) ∈ (chartAt E x).target
      rw [e.symm_apply_apply]
      exact (chartAt E x).map_source (mem_chart_source E x)
    filter_upwards [((chartAt E x).open_target.preimage e.symm.continuous).mem_nhds hmem]
      with z hz
    change (chartAt E x) ((chartAt E x).symm (e.symm z)) = e.symm z
    exact (chartAt E x).right_inv hz
  constructor
  · -- The unchanged underlying point map is continuous; its coordinate expressions are smooth.
    constructor
    · intro x
      exact contMDiffAt_iff.mpr ⟨continuousAt_id,
        (e.contDiff.contDiffAt.congr_of_eventuallyEq (hforward x)).contDiffWithinAt⟩
    · intro x
      exact contMDiffAt_iff.mpr ⟨continuousAt_id,
        (e.symm.contDiff.contDiffAt.congr_of_eventuallyEq (hreverse x)).contDiffWithinAt⟩
  · constructor
    · intro x
      -- The derivative is computed in these same full charts, without a model identification.
      apply HasMFDerivAt.mfderiv
      refine ⟨continuousAt_id, ?_⟩
      exact (e.toContinuousLinearMap.hasFDerivAt.congr_of_eventuallyEq
        (hforward x)).hasFDerivWithinAt
    · intro x
      apply HasMFDerivAt.mfderiv
      refine ⟨continuousAt_id, ?_⟩
      exact (e.symm.toContinuousLinearMap.hasFDerivAt.congr_of_eventuallyEq
        (hreverse x)).hasFDerivWithinAt

/-- The identity of points between the original atlas and its specified linear recharting. -/
def linearModelDiffeomorph :
    letI := linearModelChartedSpace e M
    M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ M := by
  letI := linearModelChartedSpace e M
  exact
    { toEquiv := Equiv.refl M
      contMDiff_toFun := (contMDiff_mfderiv_linearModelId e M).1.1
      contMDiff_invFun := (contMDiff_mfderiv_linearModelId e M).1.2 }

end AtiyahSinger
