/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Pseudolocal
public import AtiyahSinger.Analysis.SobolevLocalization

/-!
# The original cutoff maps on Sobolev completions

Public module ID: M0994.

The existing localize and extend maps have bounded realizations at every real
Sobolev order. Each realization retains the actual original chart, frame and
cutoff, and is fixed before any parameter-dependent local operator is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.BundleChartCutoff

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (D : BundleChartCutoff (r := r) E c)
  (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
  (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The same compact cutoff localization extends to every real Sobolev completion. -/
theorem exists_sobolev_localization (s : ℝ) :
    ∃ L : A.SobolevSpace s →L[ℂ] Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ u : smoothSections (n := n) (r := r) E,
        L (A.smoothToSobolev s u) = schwartzSobolevCoordinate s (D.localize hc u) := by
  obtain ⟨C, _, hbound⟩ := D.exists_norm_localize_sobolev_le hc A s
  let F := (schwartzSobolevCoordinateLinearMap n r s).comp (D.localizeLinearMap hc)
  refine ⟨F.extendOfNorm (A.smoothToSobolev s), ?_⟩
  intro u
  exact LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨C, hbound⟩ u

/-- The same compact cutoff extension acts boundedly on the local Bessel coordinates. -/
theorem exists_sobolev_extension (s : ℝ) :
    ∃ L : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ] A.SobolevSpace s,
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        L (schwartzSobolevCoordinate s u) = A.smoothToSobolev s (D.extend hc u) := by
  obtain ⟨C, _, hbound⟩ := D.exists_norm_extend_sobolev_le hc A s
  let F := (A.smoothToSobolev s).comp (D.extendLinearMap hc)
  refine ⟨F.extendOfNorm (schwartzSobolevCoordinateLinearMap n r s), ?_⟩
  intro u
  exact LinearMap.extendOfNorm_eq (denseRange_schwartzSobolevCoordinate n r s) ⟨C, hbound⟩ u

end AtiyahSinger.BundleChartCutoff
