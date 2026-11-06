/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.PseudodifferentialAdjointApproximation
public import AtiyahSinger.Analysis.SobolevFormalAdjointBound

/-!
# Adjoint approximation with the same bounded residual

Public module ID: M0924.

A negative-order bound for the forward error corrected by a bounded L2 residual
controls the literal adjoint error corrected by that residual's Hilbert adjoint.
Testing on the original dense smooth core gives the estimate without assuming
that the residual adjoint preserves smooth sections. The metrics, Sobolev
presentations, original maps and residual are all retained. This is the paired
norm estimate required for compact perturbation of the associated cutoff family.
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

set_option maxHeartbeats 1200000 in
-- Retain both Sobolev completions and their metric pairings in the dense-core estimate.
/-- A corrected forward error controls the adjoint corrected by the same bounded residual. -/
theorem exists_residual_metricFormalAdjoint_sub_bound
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    let Φ := h.sobolevZeroEquivL2 (μ := μ) A
    let Ψ := k.sobolevZeroEquivL2 (μ := μ) B
    let J := Ψ.toContinuousLinearMap.comp (B.sobolevInclusion 1 0 (by norm_num))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ (T W : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
        (S : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E)
        (Sb : B.SobolevSpace 1 →L[ℂ] A.SobolevSpace 0)
        (R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
        (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1),
        IsMetricFormalAdjoint h k μ T S →
        (∀ u, R (h.smoothToL2 μ u) = k.smoothToL2 μ (W u)) →
        (∀ v, Sb (B.smoothToSobolev 1 v) = A.smoothToSobolev 0 (S v)) →
        (∀ u, ‖B.smoothToSobolev (-1) (P.toLinearMap u - T u + W u)‖ ≤
          δ * ‖A.smoothToSobolev 0 u‖) →
        ‖Φ.toContinuousLinearMap.comp
          ((P.metricFormalAdjoint h k).sobolevRealization B A 1 0 (by norm_num) - Sb) +
            R.adjoint.comp J‖ ≤ C * δ := by
  intro Φ Ψ J
  let dual := k.sobolevDuality B μ (-1)
  refine ⟨‖Φ.symm.toContinuousLinearMap‖ * ‖dual.toContinuousLinearMap‖,
    mul_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  intro δ hδ T W S Sb R P hpair hR hSb hbound
  let Pa := P.metricFormalAdjoint h k
  let Err := Φ.toContinuousLinearMap.comp
    (Pa.sobolevRealization B A 1 0 (by norm_num) - Sb) + R.adjoint.comp J
  have herror : IsMetricFormalAdjoint h k μ (P.toLinearMap - T) (Pa.toLinearMap - S) := by
    have hp := (P.isMetricFormalAdjoint_metricFormalAdjoint h k).add (hpair.smul (-1))
    simpa only [map_neg, map_one, neg_one_smul, sub_eq_add_neg] using hp
  -- Pair the completed reverse error with the original smooth source core.
  have hsmooth (v : smoothSections (n := n) (r := q) F) :
      ‖Err (B.smoothToSobolev 1 v)‖ ≤
        (‖Φ.symm.toContinuousLinearMap‖ * ‖dual.toContinuousLinearMap‖) * δ *
          ‖B.smoothToSobolev 1 v‖ := by
    let w := Err (B.smoothToSobolev 1 v)
    let ℓ := (innerSL ℂ w).comp Φ.toContinuousLinearMap
    let z := dual (B.smoothToSobolev (-(-1 : ℝ)) v)
    have hw : w = h.smoothToL2 μ (Pa.toLinearMap v - S v) +
        R.adjoint (k.smoothToL2 μ v) := by
      change Φ (Pa.sobolevRealization B A 1 0 (by norm_num)
        (B.smoothToSobolev 1 v) - Sb (B.smoothToSobolev 1 v)) +
          R.adjoint (Ψ (B.sobolevInclusion 1 0 (by norm_num) (B.smoothToSobolev 1 v))) = _
      rw [Pa.sobolevRealization_smoothToSobolev B A 1 0 (by norm_num), hSb,
        ← map_sub, B.sobolevInclusion_smoothToSobolev]
      rw [h.sobolevZeroEquivL2_smooth, k.sobolevZeroEquivL2_smooth]
    have hvalue (u : smoothSections (n := n) (r := r) E) :
        ℓ (A.smoothToSobolev 0 u) =
          z (B.smoothToSobolev (-1) (P.toLinearMap u - T u + W u)) := by
      change inner ℂ w (Φ (A.smoothToSobolev 0 u)) = _
      rw [h.sobolevZeroEquivL2_smooth, hw, inner_add_left,
        R.adjoint_inner_left, hR, h.inner_smoothToL2, k.inner_smoothToL2]
      change _ = k.sobolevPairing B μ (-1) _ _
      rw [k.sobolevPairing_smooth]
      have hadd : k.sectionPairing μ v (P.toLinearMap u - T u + W u) =
          k.sectionPairing μ v (P.toLinearMap u - T u) + k.sectionPairing μ v (W u) := by
        rw [← k.inner_smoothToL2 μ, map_add, inner_add_right,
          k.inner_smoothToL2, k.inner_smoothToL2]
      rw [hadd]
      have hc := congrArg conj (herror u v)
      rw [k.sectionPairing_conj_symm, h.sectionPairing_conj_symm] at hc
      exact congrArg (· + k.sectionPairing μ v (W u)) hc.symm
    have hℓ : ‖ℓ‖ ≤ ‖z‖ * δ := by
      apply ℓ.opNorm_le_bound (mul_nonneg (norm_nonneg _) hδ)
      intro x
      refine (A.denseRange_smoothToSobolev 0).induction_on x
        (isClosed_le (ℓ.continuous.norm) (continuous_const.mul continuous_norm)) ?_
      intro u
      rw [hvalue]
      calc
        _ ≤ ‖z‖ * ‖B.smoothToSobolev (-1) (P.toLinearMap u - T u + W u)‖ := z.le_opNorm _
        _ ≤ ‖z‖ * (δ * ‖A.smoothToSobolev 0 u‖) :=
          mul_le_mul_of_nonneg_left (hbound u) (norm_nonneg _)
        _ = _ := (mul_assoc _ _ _).symm
    have hrecover : innerSL ℂ w = ℓ.comp Φ.symm.toContinuousLinearMap := by
      ext x
      change inner ℂ w x = inner ℂ w (Φ (Φ.symm x))
      rw [Φ.apply_symm_apply]
    calc
      ‖w‖ = ‖innerSL ℂ w‖ := (innerSL_apply_norm ℂ w).symm
      _ = ‖ℓ.comp Φ.symm.toContinuousLinearMap‖ := congrArg norm hrecover
      _ ≤ ‖ℓ‖ * ‖Φ.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖z‖ * δ) * ‖Φ.symm.toContinuousLinearMap‖ :=
        mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
      _ ≤ (‖dual.toContinuousLinearMap‖ * ‖B.smoothToSobolev 1 v‖ * δ) *
          ‖Φ.symm.toContinuousLinearMap‖ := by
        gcongr
        have hd := dual.toContinuousLinearMap.le_opNorm
          (B.smoothToSobolev (-(-1 : ℝ)) v)
        have hn : ‖B.smoothToSobolev (-(-1 : ℝ)) v‖ = ‖B.smoothToSobolev 1 v‖ :=
          congrArg (fun t : ℝ ↦ ‖B.smoothToSobolev t v‖) (neg_neg (1 : ℝ))
        exact hd.trans_eq (congrArg (‖dual.toContinuousLinearMap‖ * ·) hn)
      _ = _ := by ring
  -- Density gives the norm of this exact corrected adjoint on the fixed order-one domain.
  apply Err.opNorm_le_bound (by positivity)
  intro x
  exact (B.denseRange_smoothToSobolev 1).induction_on x
    (isClosed_le (Err.continuous.norm) (continuous_const.mul continuous_norm)) hsmooth

end AtiyahSinger

