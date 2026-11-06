/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricSobolev
public import AtiyahSinger.Analysis.SmoothingOperator

/-!
# Smooth finite-rank orthogonal projections

Public module ID: M0968.

The orthogonal projection onto a finite-dimensional space of original smooth
sections is a smoothing operator for the same positive density and Hermitian
metric. Its finite orthonormal expansion extends between arbitrary Sobolev
orders using the existing geometric duality. This standard finite-rank
correction removes the kernel of a symmetric elliptic operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]


variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (W : Submodule ℂ (h.SmoothL2Section μ)) [FiniteDimensional ℂ W]

/-- The original metric orthogonal projection, acting on the original smooth sections. -/
def smoothOrthogonalProjection :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
  W.starProjection.toLinearMap

/-- A finite-dimensional smooth projection has an actual smooth integral kernel. -/
theorem isSmoothingOperator_smoothOrthogonalProjection :
    IsSmoothingOperator μ (smoothOrthogonalProjection μ h W) := by
  classical
  obtain ⟨S⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  apply (isSmoothingOperator_iff_sobolevExtensions μ _ S S).mpr
  intro s t
  let b := stdOrthonormalBasis ℂ W
  let v (i : Fin (Module.finrank ℂ W)) : smoothSections (n := n) (r := r) E :=
    (b i).val
  let f (i : Fin (Module.finrank ℂ W)) : StrongDual ℂ (S.SobolevSpace s) :=
    h.sobolevDuality S μ s (S.smoothToSobolev (-s) (v i))
  let T : S.SobolevSpace s →L[ℂ] S.SobolevSpace t :=
    ∑ i, (f i).smulRight (S.smoothToSobolev t (v i))
  refine ⟨T, ?_⟩
  intro u
  -- The exact orthonormal expansion uses the same metric integral in each coefficient.
  have hprojection : smoothOrthogonalProjection μ h W u =
      ∑ i, h.sectionPairing μ (v i) u • v i := by
    let u' : h.SmoothL2Section μ := u
    have heq := congrArg (fun T : h.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ ↦ T u')
      b.starProjection_eq_sum_rankOne
    simp only [sum_apply, InnerProductSpace.rankOne_apply] at heq
    exact heq
  rw [hprojection, map_sum]
  change (∑ i, (f i).smulRight (S.smoothToSobolev t (v i)))
    (S.smoothToSobolev s u) = _
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  change h.sobolevPairing S μ s (S.smoothToSobolev (-s) (v i))
      (S.smoothToSobolev s u) • S.smoothToSobolev t (v i) = _
  rw [h.sobolevPairing_smooth]

end AtiyahSinger
