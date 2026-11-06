/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoSobolev
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The specified atlas and native Sobolev domains

Public module ID: M0266.

Extend the original smooth fiber isomorphism using its two actual Sobolev
bounds. The inverse uses the original smooth inverse on its dense core.
The result retains both supplied presentations at every real order, including
the actual H1 domain used in the graded Fredholm comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the smooth conjugation on both completed Sobolev domains.
/-- The actual smooth conjugation extends between the two specified Sobolev domains. -/
theorem exists_sobolev_equiv_native
    (A : SmoothComplexBundleAtlas (n := n) E) (L : AtlasBundlePresentation A)
    (N : SmoothFiniteComplexBundle (n := n) M)
    (K : SmoothBundlePresentation (n := n) (r := N.rank) N.Fiber) (s : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    ∀ (e : Iso E N.Fiber)
      (he : IsSmoothAtlasBundleMap A (nativeSmoothComplexBundleAtlas N.Fiber)
        e.toHom.linearMap)
      (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) A
        e.symm.toHom.linearMap),
      let S := (atlasSmoothSectionEquiv A (nativeSmoothComplexBundleAtlas N.Fiber)
        e he hi).trans (nativeSmoothSectionLinearEquiv N.Fiber)
      ∃ Φ : L.SobolevSpace s ≃L[ℂ] K.SobolevSpace s,
        ∀ u : A.smoothSections, Φ (L.smoothToSobolev s u) = K.smoothToSobolev s (S u) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  intro e he hi S
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber
  let Sa := atlasSmoothSectionEquiv A B e he hi
  obtain ⟨C, _, hC⟩ := exists_atlasSmoothSectionEquiv_sobolev_comparison
    A B e he hi L K.toAtlasBundlePresentation s
  have hforward : ∃ c, ∀ u,
      ‖K.toAtlasBundlePresentation.smoothToSobolev s (Sa u)‖ ≤
        c * ‖L.smoothToSobolev s u‖ := ⟨C, fun u ↦ (hC u).1⟩
  have hbackward : ∃ c, ∀ v,
      ‖L.smoothToSobolev s (Sa.symm v)‖ ≤
        c * ‖K.toAtlasBundlePresentation.smoothToSobolev s v‖ := by
    refine ⟨C, ?_⟩
    intro v
    simpa only [Sa, LinearEquiv.apply_symm_apply] using (hC (Sa.symm v)).2
  -- Complete these same mutually inverse smooth maps, then use the original native completion.
  let Φa := Sa.extend (L.smoothToSobolev s) (K.toAtlasBundlePresentation.smoothToSobolev s)
    (L.denseRange_smoothToSobolev s) hforward
    (K.toAtlasBundlePresentation.denseRange_smoothToSobolev s) hbackward
  let Φ := Φa.trans (K.nativeAtlasSobolevEquiv s).symm.toContinuousLinearEquiv
  refine ⟨Φ, ?_⟩
  intro u
  apply (K.nativeAtlasSobolevEquiv s).injective
  change Φa (L.smoothToSobolev s u) =
    K.nativeAtlasSobolevEquiv s (K.smoothToSobolev s (S u))
  rw [K.nativeAtlasSobolevEquiv_smoothToSobolev]
  have h := Sa.extend_eq (L.smoothToSobolev s)
    (K.toAtlasBundlePresentation.smoothToSobolev s) (L.denseRange_smoothToSobolev s) hforward
    (K.toAtlasBundlePresentation.denseRange_smoothToSobolev s) hbackward u
  simpa only [S, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

end AtiyahSinger.SmoothComplexBundleAtlas
