/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasMetricL2Comparison
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The original atlas H0 completion and its specified native metric L2 space

Public module ID: M0260.

Extend the identity on the same smooth atlas sections through the two given
completion maps. The existing two-sided norm comparison and the actual native
section equivalence supply the inverse completion map and its dense range.
The resulting equivalence keeps the prescribed fiber isomorphism and metric.
Composing it with the original H1-to-H0 inclusion gives the injective domain
inclusion required by the original graded closed-graph comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

set_option maxSynthPendingDepth 40 in
/-- The specified metric completion identifies atlas H0 and retains the original H1 inclusion. -/
theorem exists_sobolevZero_equiv_nativeL2
    (A : SmoothComplexBundleAtlas (n := n) E)
    (L : AtlasBundlePresentation A) (h : ContinuousHermitianMetric E)
    (hh : A.IsSmoothHermitianMetric h) (N : SmoothFiniteComplexBundle (n := n) M)
    (k : SmoothHermitianMetric (n := n) (r := N.rank) N.Fiber)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    ∀ (e : Iso E N.Fiber)
      (he : IsSmoothAtlasBundleMap A (nativeSmoothComplexBundleAtlas N.Fiber)
        e.toHom.linearMap)
      (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) A
        e.symm.toHom.linearMap),
      (∀ (x : M) (v w : E x),
        k.pairing x (e.linearEquiv x v) (e.linearEquiv x w) = (h.toCore x).inner v w) →
      let S := (atlasSmoothSectionEquiv A (nativeSmoothComplexBundleAtlas N.Fiber)
        e he hi).trans (nativeSmoothSectionLinearEquiv N.Fiber)
      let i := (k.smoothToL2 μ).comp S.toLinearMap
      ∃ Φ : L.SobolevSpace 0 ≃L[ℂ] k.L2SectionSpace μ,
        (∀ u : A.smoothSections, Φ (L.smoothToSobolev 0 u) = i u) ∧
        let J := Φ.toContinuousLinearMap.comp (L.sobolevInclusion 1 0 (by norm_num))
        Function.Injective J ∧ ∀ u : A.smoothSections, J (L.smoothToSobolev 1 u) = i u := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  intro e he hi hk S i
  obtain ⟨C, D, _hC, _hD, hcompare⟩ := A.exists_sobolevZero_l2_comparison
    L h hh N k μ e he hi hk
  -- The same smooth section equivalence reaches every native smooth section in the L2 core.
  have hdense : DenseRange i := by
    apply (k.denseRange_smoothToL2 μ).mono
    rintro _ ⟨u, rfl⟩
    exact ⟨S.symm u, congrArg (k.smoothToL2 μ) (S.apply_symm_apply u)⟩
  let f := LinearEquiv.refl ℂ A.smoothSections
  have hforward : ∃ c, ∀ u, ‖i (f u)‖ ≤ c * ‖L.smoothToSobolev 0 u‖ :=
    ⟨D, fun u ↦ (hcompare u).2⟩
  have hbackward : ∃ c, ∀ u, ‖L.smoothToSobolev 0 (f.symm u)‖ ≤ c * ‖i u‖ :=
    ⟨C, fun u ↦ (hcompare u).1⟩
  -- The standard two-sided completion construction preserves both actual completion maps.
  let Φ := f.extend (L.smoothToSobolev 0) i
    (L.denseRange_smoothToSobolev 0) hforward hdense hbackward
  have hΦ (u : A.smoothSections) : Φ (L.smoothToSobolev 0 u) = i u :=
    f.extend_eq (L.smoothToSobolev 0) i
      (L.denseRange_smoothToSobolev 0) hforward hdense hbackward u
  refine ⟨Φ, hΦ, ?_⟩
  -- Injectivity comes from the original Sobolev inclusion followed by this same equivalence.
  refine ⟨Φ.injective.comp (L.sobolevInclusion_injective 1 0 (by norm_num)), ?_⟩
  intro u
  change Φ (L.sobolevInclusion 1 0 (by norm_num) (L.smoothToSobolev 1 u)) = i u
  exact (congrArg Φ (L.sobolevInclusion_smoothToSobolev 1 0 (by norm_num) u)).trans (hΦ u)

end AtiyahSinger.SmoothComplexBundleAtlas
