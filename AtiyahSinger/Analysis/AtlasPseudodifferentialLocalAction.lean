/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev
public import AtiyahSinger.Analysis.AtlasSobolevEmbedding
public import AtiyahSinger.Analysis.AtlasSobolevLocalization

/-!
# Continuous local Schwartz inputs for the original atlas PDO

Public module ID: M0287.

Extending a Schwartz input by a specified original chart cutoff and applying
the entire original PDO is continuous into every finite-order section space.
The input Sobolev estimate, the actual PDO extension and Sobolev embedding
retain their specified presentations and pointwise smooth-input identities.
In particular, the smoothing remainder of the PDO is included.

These maps supply continuous local functionals for the two-variable pairing
argument and finite-order controls for joint parameter regularity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set Topology
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E} {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasPseudodifferentialOperator

set_option maxSynthPendingDepth 30 in
/-- The full original PDO on an original cutoff extension is continuous into every C^k space. -/
theorem exists_localActionCk {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (D : AtlasChartCutoff A c) (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (k : ℕ) :
    ∃ T : 𝓢(EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℂ (Fin (A.rank D.frameIndex))) →L[ℂ] K.CkSectionSpace k,
      ∀ v, T v = K.smoothToCk k (P.toLinearMap (D.extend hc v)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank D.frameIndex))
  let s : ℝ := m + (n : ℝ) / 2 + k + 1
  have hs : (n : ℝ) / 2 + k < s - m := by dsimp [s]; linarith
  let J : 𝓢(X, V) →L[ℝ] Lp V 2 (volume : Measure X) :=
    (SchwartzMap.toLpCLM ℝ V 2 volume).comp
      (SchwartzMap.fourierMultiplierCLM V (fun ξ : X ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)))
  let e : 𝓢(X, V) →ₗ[ℂ] L.SobolevSpace s :=
    (L.smoothToSobolev s).comp (D.extendLinearMap hc)
  obtain ⟨C, _, hbound⟩ := D.exists_norm_extend_sobolev_le hc L s
  have he : Continuous e := by
    -- The original Sobolev bound is dominated by a continuous Schwartz Bessel coordinate.
    apply continuous_of_tendsto_nhds_zero e
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (g := fun v : 𝓢(X, V) ↦ C * ‖J v‖)
      (fun v ↦ norm_nonneg (e v)) ?_ ?_
    · intro v
      exact hbound v
    · have h := (J.continuous.norm.const_mul C).tendsto (0 : 𝓢(X, V))
      simpa only [map_zero, norm_zero, mul_zero] using h
  let eC : 𝓢(X, V) →L[ℂ] L.SobolevSpace s := { e with cont := he }
  let T := (K.sobolevToCk k (s - m) hs).comp ((P.sobolevExtension L K s).comp eC)
  refine ⟨T, ?_⟩
  intro v
  -- Each of the three maps agrees with its original smooth section operation.
  change K.sobolevToCk k (s - m) hs
    (P.sobolevExtension L K s (L.smoothToSobolev s (D.extend hc v))) = _
  rw [P.sobolevExtension_smoothToSobolev L K s, K.sobolevToCk_smoothToSobolev]

end AtlasPseudodifferentialOperator

end AtiyahSinger
