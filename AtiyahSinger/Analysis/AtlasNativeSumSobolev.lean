/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasNativeSobolevEquivalence
public import AtiyahSinger.Analysis.SmoothSectionBundleSum
public import AtiyahSinger.Analysis.SobolevBundleSum

/-!
# The original atlas domains in a specified native sum

Public module ID: M0267.

Compose the two actual atlas-to-native completion maps with the supplied
smooth bundle sum. The resulting coordinates retain both original atlas
presentations and the same smooth sum, at every real Sobolev order. The
intermediate native presentations are specified, so both parity components
of the cutoff construction can use exactly the same choices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {E₁ E₂ : M → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace Unit E₂)]

include μ

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the specified native sum and its two exact atlas Sobolev
-- coordinates.
/-- The specified native sum has the two original atlas Sobolev spaces as its exact coordinates. -/
theorem exists_sobolevEquiv_of_atlas_native_sum
    (A₁ : SmoothComplexBundleAtlas (n := n) E₁) (L₁ : AtlasBundlePresentation A₁)
    (A₂ : SmoothComplexBundleAtlas (n := n) E₂) (L₂ : AtlasBundlePresentation A₂)
    (N₁ N₂ N : SmoothFiniteComplexBundle (n := n) M)
    (K₁ : SmoothBundlePresentation (n := n) (r := N₁.rank) N₁.Fiber)
    (K₂ : SmoothBundlePresentation (n := n) (r := N₂.rank) N₂.Fiber)
    (K : SmoothBundlePresentation (n := n) (r := N.rank) N.Fiber) (s : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    ∀ (e₁ : Iso E₁ N₁.Fiber)
      (he₁ : IsSmoothAtlasBundleMap A₁ (nativeSmoothComplexBundleAtlas N₁.Fiber)
        e₁.toHom.linearMap)
      (hi₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁.Fiber) A₁
        e₁.symm.toHom.linearMap)
      (e₂ : Iso E₂ N₂.Fiber)
      (he₂ : IsSmoothAtlasBundleMap A₂ (nativeSmoothComplexBundleAtlas N₂.Fiber)
        e₂.toHom.linearMap)
      (hi₂ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₂.Fiber) A₂
        e₂.symm.toHom.linearMap)
      (e : ∀ x, (N₁.Fiber x × N₂.Fiber x) ≃ₗ[ℂ] N.Fiber x)
      (h₁ : IsSmoothBundleMap (n := n) (r := N₁.rank) (q := N.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (N₁.Fiber x) (N₂.Fiber x))))
      (h₂ : IsSmoothBundleMap (n := n) (r := N₂.rank) (q := N.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (N₁.Fiber x) (N₂.Fiber x)))),
      let S₁ := (atlasSmoothSectionEquiv A₁ (nativeSmoothComplexBundleAtlas N₁.Fiber)
        e₁ he₁ hi₁).trans (nativeSmoothSectionLinearEquiv N₁.Fiber)
      let S₂ := (atlasSmoothSectionEquiv A₂ (nativeSmoothComplexBundleAtlas N₂.Fiber)
        e₂ he₂ hi₂).trans (nativeSmoothSectionLinearEquiv N₂.Fiber)
      let S := smoothSectionSumEquiv e h₁ h₂
      ∃ Φ : K.SobolevSpace s ≃L[ℂ] WithLp 2 (L₁.SobolevSpace s × L₂.SobolevSpace s),
        ∀ u v, Φ (K.smoothToSobolev s (S (S₁ u, S₂ v))) =
          WithLp.toLp 2 (L₁.smoothToSobolev s u, L₂.smoothToSobolev s v) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  intro e₁ he₁ hi₁ e₂ he₂ hi₂ e h₁ h₂ S₁ S₂ S
  -- First complete the two supplied atlas isomorphisms, preserving their smooth values.
  obtain ⟨Φ₁, hΦ₁⟩ := A₁.exists_sobolev_equiv_native L₁ N₁ K₁ s e₁ he₁ hi₁
  obtain ⟨Φ₂, hΦ₂⟩ := A₂.exists_sobolev_equiv_native L₂ N₂ K₂ s e₂ he₂ hi₂
  obtain ⟨U, hU⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ) e h₁ h₂ K₁ K₂ K s
  let c := WithLp.prodContinuousLinearEquiv 2 ℂ (L₁.SobolevSpace s) (L₂.SobolevSpace s)
  let Φ := (U.trans (Φ₁.symm.prodCongr Φ₂.symm)).trans c.symm
  refine ⟨Φ, ?_⟩
  intro u v
  -- The inverse projections are those of the original smooth sum, before completion.
  have hsum := S.symm_apply_apply (S₁ u, S₂ v)
  have h₁proj := congrArg Prod.fst hsum
  have h₂proj := congrArg Prod.snd hsum
  have hsumU : U (K.smoothToSobolev s (S (S₁ u, S₂ v))) =
      (K₁.smoothToSobolev s (S₁ u), K₂.smoothToSobolev s (S₂ v)) := by
    rw [hU]
    exact Prod.ext (congrArg (K₁.smoothToSobolev s) h₁proj)
      (congrArg (K₂.smoothToSobolev s) h₂proj)
  change c.symm ((Φ₁.symm.prodCongr Φ₂.symm)
    (U (K.smoothToSobolev s (S (S₁ u, S₂ v))))) = _
  rw [hsumU]
  change c.symm (Φ₁.symm (K₁.smoothToSobolev s (S₁ u)),
    Φ₂.symm (K₂.smoothToSobolev s (S₂ v))) = _
  rw [← hΦ₁, ← hΦ₂, Φ₁.symm_apply_apply, Φ₂.symm_apply_apply]
  rfl

end AtiyahSinger
