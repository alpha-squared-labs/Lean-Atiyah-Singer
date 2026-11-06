/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialRegularity
public import AtiyahSinger.Analysis.SobolevFormalAdjointBound

/-!
# Norm approximation of the literal metric formal adjoint

The same original forward error from order zero to order minus one controls
the actual metric adjoint PDO on the fixed order-one domain. Formal pairing
identifies its smooth error with the supplied reverse map, and density bounds
the operator norm of its given Sobolev realization. The uniform constant is
chosen before the original maps, the PDO and the error size.

This is the paired approximation step for the associated graded construction.
It does not choose a separate regularization of the reverse operator or infer
a common graph domain. Those geometric inputs remain explicit.
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

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hT2 hSC hE

variable {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- A forward negative-order error bounds the literal adjoint error on the fixed domain. -/
theorem exists_metricFormalAdjoint_sobolevRealization_sub_bound
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ (T : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
        (S : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E)
        (Sb : B.SobolevSpace 1 →L[ℂ] A.SobolevSpace 0)
        (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1),
        IsMetricFormalAdjoint h k μ T S →
        (∀ v, Sb (B.smoothToSobolev 1 v) = A.smoothToSobolev 0 (S v)) →
        (∀ u, ‖B.smoothToSobolev (-1) (P.toLinearMap u - T u)‖ ≤
          δ * ‖A.smoothToSobolev 0 u‖) →
        ‖(P.metricFormalAdjoint h k).sobolevRealization B A 1 0 (by norm_num) - Sb‖ ≤
          C * δ := by
  -- The fixed metrics and presentations determine the constant before the approximating PDO.
  obtain ⟨C, hC, hdual⟩ := exists_sobolev_formalAdjoint_bound μ h k A B 0 (-1)
  refine ⟨C, hC, ?_⟩
  intro δ hδ T S Sb P hpair hSb hbound
  let Pa := P.metricFormalAdjoint h k
  let R := Pa.sobolevRealization B A 1 0 (by norm_num)
  have herror : IsMetricFormalAdjoint h k μ (P.toLinearMap - T) (Pa.toLinearMap - S) := by
    have h := (P.isMetricFormalAdjoint_metricFormalAdjoint h k).add (hpair.smul (-1))
    simpa only [map_neg, map_one, neg_one_smul, sub_eq_add_neg] using h
  have hsmooth (v : smoothSections (n := n) (r := q) F) :
      ‖A.smoothToSobolev 0 (Pa.toLinearMap v - S v)‖ ≤ C * δ * ‖B.smoothToSobolev 1 v‖ := by
    have h := hdual δ hδ (P.toLinearMap - T) (Pa.toLinearMap - S) herror hbound v
    rw [show -(0 : ℝ) = 0 from neg_zero,
      show -(-1 : ℝ) = 1 from neg_neg 1] at h
    exact h
  -- Density extends the bound for this exact adjoint realization, on the given order-one domain.
  apply (R - Sb).opNorm_le_bound (mul_nonneg hC hδ)
  intro v
  refine (B.denseRange_smoothToSobolev 1).induction_on v
    (isClosed_le ((R - Sb).continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro u
  change ‖R (B.smoothToSobolev 1 u) - Sb (B.smoothToSobolev 1 u)‖ ≤ _
  rw [hSb, Pa.sobolevRealization_smoothToSobolev B A 1 0 (by norm_num)]
  rw [← map_sub]
  exact hsmooth u

end AtiyahSinger

