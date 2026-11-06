/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricSobolev

/-!
# Opposite Sobolev bounds for the actual formal adjoint (M2317)

The given two Hermitian metrics identify opposite-order completions with
continuous duals. For any formally paired smooth-section maps, an estimate
from order s to order t transfers to the actual reverse map from order -t
to order -s. The loss depends only on the specified metrics and presentations,
so it remains uniform through cutoff approximations. No PDO or maximal-domain
hypothesis is needed for this estimate on the original smooth maps.
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

/-- The original metric formal pairing transfers a uniform bound to the opposite orders. -/
theorem exists_sobolev_formalAdjoint_bound
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (s t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ (T : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
        (S : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E),
        (∀ u v, k.sectionPairing μ (T u) v = h.sectionPairing μ u (S v)) →
        (∀ u, ‖B.smoothToSobolev t (T u)‖ ≤ δ * ‖A.smoothToSobolev s u‖) →
        ∀ v, ‖A.smoothToSobolev (-s) (S v)‖ ≤ C * δ * ‖B.smoothToSobolev (-t) v‖ := by
  let e := h.sobolevDuality A μ s
  let f := k.sobolevDuality B μ t
  refine ⟨‖e.symm.toContinuousLinearMap‖ * ‖f.toContinuousLinearMap‖, by positivity, ?_⟩
  intro δ hδ T S hpair hbound v
  let ℓ := e (A.smoothToSobolev (-s) (S v))
  let z := f (B.smoothToSobolev (-t) v)
  -- Hermitian symmetry puts the supplied integral pairing in the duality's argument order.
  have hvalue (u : smoothSections (n := n) (r := r) E) :
      ℓ (A.smoothToSobolev s u) = z (B.smoothToSobolev t (T u)) := by
    change h.sobolevPairing A μ s _ _ = k.sobolevPairing B μ t _ _
    rw [h.sobolevPairing_smooth, k.sobolevPairing_smooth]
    have hconj := congrArg conj (hpair u v)
    rw [k.sectionPairing_conj_symm, h.sectionPairing_conj_symm] at hconj
    exact hconj.symm
  -- A bound on the specified dense smooth core bounds the same continuous functional.
  have hnorm (x : A.SobolevSpace s) : ‖ℓ x‖ ≤ (‖z‖ * δ) * ‖x‖ := by
    refine (A.denseRange_smoothToSobolev s).induction_on x
      (isClosed_le (ℓ.continuous.norm) (continuous_const.mul continuous_norm)) ?_
    intro u
    rw [hvalue]
    calc
      ‖z (B.smoothToSobolev t (T u))‖ ≤ ‖z‖ * ‖B.smoothToSobolev t (T u)‖ := z.le_opNorm _
      _ ≤ ‖z‖ * (δ * ‖A.smoothToSobolev s u‖) :=
        mul_le_mul_of_nonneg_left (hbound u) (norm_nonneg z)
      _ = _ := (mul_assoc _ _ _).symm
  have hℓ : ‖ℓ‖ ≤ ‖z‖ * δ :=
    ℓ.opNorm_le_bound (mul_nonneg (norm_nonneg z) hδ) hnorm
  -- The two fixed dual equivalences supply the only norm losses.
  calc
    ‖A.smoothToSobolev (-s) (S v)‖ = ‖e.symm ℓ‖ := by rw [e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖ℓ‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖z‖ * δ) := by gcongr
    _ ≤ ‖e.symm.toContinuousLinearMap‖ *
        ((‖f.toContinuousLinearMap‖ * ‖B.smoothToSobolev (-t) v‖) * δ) := by
      gcongr
      exact f.toContinuousLinearMap.le_opNorm _
    _ = (‖e.symm.toContinuousLinearMap‖ * ‖f.toContinuousLinearMap‖) * δ *
        ‖B.smoothToSobolev (-t) v‖ := by ring

end AtiyahSinger
