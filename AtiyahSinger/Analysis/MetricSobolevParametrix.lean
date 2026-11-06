/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Realization

/-!
# Bounded metric Sobolev reconstruction from an elliptic graph

Public module ID: M0798.

The actual smooth-kernel left parametrix gives bounded maps from the metric
L2 value and metric L2 operator image back to the original first Sobolev space.
The reconstruction keeps the original section and is suitable for Hilbert
amplification; a scalar elliptic estimate alone does not give that amplification.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

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

namespace PseudodifferentialOperator

variable (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)

/-- An elliptic first-order graph admits bounded metric-L2 reconstruction into actual H1. -/
theorem exists_metricSobolev_left_parametrix (hP : P.IsElliptic)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    ∃ R : k.L2SectionSpace μ →L[ℂ] A.SobolevSpace 1,
    ∃ S : h.L2SectionSpace μ →L[ℂ] A.SobolevSpace 1,
      ∀ u : smoothSections (n := n) (r := r) E,
        A.smoothToSobolev 1 u =
          R (k.smoothToL2 μ (P.toLinearMap u)) + S (h.smoothToL2 μ u) := by
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  obtain ⟨K, hK⟩ := hQ.1
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  let f := k.sobolevZeroEquivL2 (μ := μ) B
  let R := (Q.sobolevRealization B A 0 1 (by norm_num)).comp
    f.symm.toContinuousLinearMap
  let S := -(K.sobolevExtension μ A A 0 1).comp e.symm.toContinuousLinearMap
  refine ⟨R, S, ?_⟩
  intro u
  -- The two inverse L2 identifications recover the same original smooth inputs.
  have he (v : smoothSections (n := n) (r := r) E) :
      e.symm (h.smoothToL2 μ v) = A.smoothToSobolev 0 v := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (h.sobolevZeroEquivL2_smooth A v).symm
  have hf (v : smoothSections (n := n) (r := q) F) :
      f.symm (k.smoothToL2 μ v) = B.smoothToSobolev 0 v := by
    apply f.injective
    rw [f.apply_symm_apply]
    exact (k.sobolevZeroEquivL2_smooth B v).symm
  -- Subtract the actual smooth-kernel error QP - id, retaining its sign.
  change A.smoothToSobolev 1 u =
    Q.sobolevRealization B A 0 1 (by norm_num) (f.symm (k.smoothToL2 μ (P.toLinearMap u))) +
      -(K.sobolevExtension μ A A 0 1 (e.symm (h.smoothToL2 μ u)))
  rw [he, hf, Q.sobolevRealization_smoothToSobolev,
    K.sobolevExtension_smoothToSobolev, hK, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub]
  abel

end PseudodifferentialOperator

end AtiyahSinger
