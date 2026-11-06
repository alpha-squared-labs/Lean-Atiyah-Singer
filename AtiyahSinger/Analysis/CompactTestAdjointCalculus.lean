/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactTestFormalAdjoint
public import AtiyahSinger.Analysis.HermitianMetricDifferentialAdjoint

/-!
# Involution and principal symbols of compact-test formal adjoints

Public module ID: M0365.

D02: the differential adjoint characterized by compactly supported tests is
an involution on the original smooth section operators. Its principal symbol
is the adjoint for the same two specified Hermitian metrics at the same real
covector. On a compact base it equals the previously constructed integral
formal adjoint as an actual differential operator, including lower-order terms.

The metric and symbol conventions are SG III.5, (5.3), pp.194--195; the local
symbol calculation also appears in III.4 Remark 4.8, p.191. The noncompact
compact-test formulation is the local refinement of these arguments recorded
in CompactTestFormalAdjoint. With D_j = -i partial_j, there is no extra sign in
the principal symbol identity. No Hilbert-space operator domain or choice of
self-adjoint extension occurs in these statements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace DifferentialOperator

variable {d : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F d)

/-- Double compact-test adjunction recovers the entire original differential operator. -/
theorem compactTestMetricFormalAdjoint_compactTestMetricFormalAdjoint :
    (P.compactTestMetricFormalAdjoint (μ := μ) h k).compactTestMetricFormalAdjoint
      (μ := μ) k h = P := by
  -- Conjugation of these integrals reverses the fixed original metrics.
  have hconjE (u v : smoothSections (n := n) (r := r) E) :
      starRingEnd ℂ (h.sectionPairing μ u v) = h.sectionPairing μ v u := by
    unfold SmoothHermitianMetric.sectionPairing
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ (h.toCore x).conj_inner_symm _ _
  have hconjF (u v : smoothSections (n := n) (r := q) F) :
      starRingEnd ℂ (k.sectionPairing μ u v) = k.sectionPairing μ v u := by
    unfold SmoothHermitianMetric.sectionPairing
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ (k.toCore x).conj_inner_symm _ _
  let Q := P.compactTestMetricFormalAdjoint (μ := μ) h k
  apply (Q.existsUnique_compactTestMetricFormalAdjoint (μ := μ) k h).unique
    (Q.isCompactTestMetricFormalAdjoint_compactTestMetricFormalAdjoint k h)
  intro K L hK hL u v
  have hpair := congrArg (starRingEnd ℂ)
    (P.isCompactTestMetricFormalAdjoint_compactTestMetricFormalAdjoint
      (μ := μ) h k L K hL hK v u)
  rw [hconjE, hconjF] at hpair
  exact hpair.symm

/-- On a compact base the compact-test construction equals the original integral adjoint. -/
theorem compactTestMetricFormalAdjoint_eq_metricFormalAdjoint [CompactSpace M] :
    P.compactTestMetricFormalAdjoint (μ := μ) h k =
      P.metricFormalAdjoint (μ := μ) h k := by
  -- The compact-base identity applies in particular to each original supported test.
  apply (P.existsUnique_compactTestMetricFormalAdjoint (μ := μ) h k).unique
    (P.isCompactTestMetricFormalAdjoint_compactTestMetricFormalAdjoint h k)
  intro K L _ _ u v
  exact P.isMetricFormalAdjoint_metricFormalAdjoint h k u.val v.val

/-- At each real covector, the compact-test adjoint has the specified metric-adjoint symbol. -/
theorem principalSymbol_compactTestMetricFormalAdjoint_pairing
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (u : E x) (v : F x) :
    k.pairing x (P.principalSymbol x ξ u) v =
      h.pairing x u
        ((P.compactTestMetricFormalAdjoint (μ := μ) h k).principalSymbol x ξ v) := by
  -- The compact-test relation determines the highest-order fiber adjoint at this covector.
  exact IsCompactTestMetricFormalAdjoint.principalSymbol_pairing h k
    (P.isCompactTestMetricFormalAdjoint_compactTestMetricFormalAdjoint (μ := μ) h k)
    x ξ u v

end DifferentialOperator

end AtiyahSinger
