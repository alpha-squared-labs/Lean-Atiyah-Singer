/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Native metric bounds in the original atlas Sobolev spaces

Public module ID: M0797.

A bounded map on the original smooth integral metric spaces extends to their
completions. The actual native-to-atlas H⁰ isometries and the specified metric
comparisons transport this same action to the original atlas presentations.
The Green map and both kernel projections use this common transport.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

/-- A given bounded smooth metric map acts on the original atlas H⁰ completions. -/
theorem exists_nativeAtlasSobolevZeroRealization
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (G : h.SmoothL2Section μ →L[ℂ] k.SmoothL2Section μ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
    let f := nativeSmoothSectionLinearEquiv (n := n) (r := q) F
    ∃ T : A.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        B.toAtlasBundlePresentation.SobolevSpace 0,
      ∀ u, T (A.toAtlasBundlePresentation.smoothToSobolev 0 u) =
        B.toAtlasBundlePresentation.smoothToSobolev 0 (f.symm (G (e u))) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  intro e f
  let a := A.nativeAtlasSobolevEquiv 0
  let b := B.nativeAtlasSobolevEquiv 0
  let em := h.sobolevZeroEquivL2 (μ := μ) A
  let fm := k.sobolevZeroEquivL2 (μ := μ) B
  -- Complete the original bounded action, then conjugate by the four specified comparisons.
  let T := b.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fm.symm.toContinuousLinearMap.comp (G.completion.comp
      (em.toContinuousLinearMap.comp a.symm.toContinuousLinearEquiv.toContinuousLinearMap)))
  refine ⟨T, ?_⟩
  intro u
  have hin : a.symm (A.toAtlasBundlePresentation.smoothToSobolev 0 u) =
      A.smoothToSobolev 0 (e u) := by
    apply a.injective
    rw [a.apply_symm_apply]
    exact ((A.nativeAtlasSobolevEquiv_smoothToSobolev 0 (e u)).trans
      (congrArg (A.toAtlasBundlePresentation.smoothToSobolev 0)
        (e.symm_apply_apply u))).symm
  have hcompletion (v : smoothSections (n := n) (r := r) E) :
      G.completion (h.smoothToL2 μ v) = k.smoothToL2 μ (G v) :=
    G.completion_apply_coe (show h.SmoothL2Section μ from v)
  have hout (v : smoothSections (n := n) (r := q) F) :
      fm.symm (k.smoothToL2 μ v) = B.smoothToSobolev 0 v := by
    rw [← k.sobolevZeroEquivL2_smooth B v]
    exact fm.symm_apply_apply _
  -- Each smooth input has exactly the original atlas output, including its native section map.
  change b (fm.symm (G.completion (em
    (a.symm (A.toAtlasBundlePresentation.smoothToSobolev 0 u))))) = _
  rw [hin, h.sobolevZeroEquivL2_smooth]
  exact (congrArg (fun v ↦ b (fm.symm v)) (hcompletion (e u))).trans
    ((congrArg b (hout (G (e u)))).trans
      (B.nativeAtlasSobolevEquiv_smoothToSobolev 0 (G (e u))))

end AtiyahSinger
