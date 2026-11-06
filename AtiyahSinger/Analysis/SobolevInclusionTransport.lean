/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SobolevMaps

/-!
# Equal-order Sobolev inclusions as transport of bounded maps

Public module ID: M0997.

An inclusion between equal exponents is the identity after transporting its
codomain. Compare the complete bounded maps by density before evaluating any
dependent cast. This retains the specified Sobolev completions and their actual
smooth-section embeddings, including transports of elliptic realizations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothBundlePresentation

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- Equal-order Sobolev inclusion is precisely codomain transport of any bounded input map. -/
theorem sobolevInclusion_comp_eq_cast (S : SmoothBundlePresentation (n := n) (r := r) E)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (s t : ℝ) (hst : s = t) (U : X →L[ℂ] S.SobolevSpace s) :
    (S.sobolevInclusion s t hst.ge).comp U =
      Eq.mp (congrArg (fun q : ℝ ↦ X →L[ℂ] S.SobolevSpace q) hst) U := by
  subst t
  -- The original smooth embeddings are dense, and same-order inclusion fixes all of them.
  have hinclusion : S.sobolevInclusion s s (le_refl s) =
      ContinuousLinearMap.id ℂ (S.SobolevSpace s) := by
    apply DFunLike.coe_injective
    apply (S.denseRange_smoothToSobolev s).equalizer
      (S.sobolevInclusion s s (le_refl s)).continuous (ContinuousLinearMap.id ℂ _).continuous
    funext u
    exact S.sobolevInclusion_smoothToSobolev s s (le_refl s) u
  rw [hinclusion]
  rfl

end AtiyahSinger.SmoothBundlePresentation
