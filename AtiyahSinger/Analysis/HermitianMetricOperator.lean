/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm
public import AtiyahSinger.Analysis.HermitianMetricL2

/-!
# Transport of bounded realizations under a change of metric

Public module ID: M0726.

A07: canonical L² identity comparisons transport an existing bounded operator.
If it extends a specified smooth-section map, the transported operator extends
that same map and is the only bounded extension in the new metric models.
Fredholmness and index are preserved. Boundedness of a differential or
pseudodifferential operator on L² is not presumed here: the old bounded realization
is explicit input. Positive-order realizations with Sobolev domains remain separate.

These are project comparison deductions from the integral models used in Spin
Geometry III.5.2–5.3 and the standard Fredholm definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (h h' : SmoothHermitianMetric (n := n) (r := r) E)
  (k k' : SmoothHermitianMetric (n := n) (r := q) F)

/-- Conjugate a bounded operator by the identity comparisons of the two metric models. -/
def l2MetricTransport (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ) :
    h'.L2SectionSpace μ →L[ℂ] k'.L2SectionSpace μ :=
  (k.l2Equiv μ k').toContinuousLinearMap.comp
    (T.comp (h'.l2Equiv μ h).toContinuousLinearMap)

/-- Transport intertwines the original and new metric realizations on every L² input. -/
theorem l2MetricTransport_apply (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
    (u : h.L2SectionSpace μ) :
    l2MetricTransport μ h h' k k' T (h.l2Equiv μ h' u) = k.l2Equiv μ k' (T u) := by
  /- Expand the conjugation formula and cancel the inverse input comparison.
  The output comparison then acts on exactly the original value T u. -/
  change k.l2Equiv μ k' (T (h'.l2Equiv μ h (h.l2Equiv μ h' u))) = _
  rw [← h.l2Equiv_symm μ h', ContinuousLinearEquiv.symm_apply_apply]

/-- A bounded realization of a smooth-section map still realizes that map after transport. -/
theorem l2MetricTransport_smoothToL2
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
    (hT : ∀ u, T (h.smoothToL2 μ u) = k.smoothToL2 μ (P u))
    (u : smoothSections (n := n) (r := r) E) :
    l2MetricTransport μ h h' k k' T (h'.smoothToL2 μ u) = k'.smoothToL2 μ (P u) := by
  /- The input identity comparison preserves u on the dense smooth subspace.
  Apply the given extension identity, then the corresponding output comparison. -/
  change k.l2Equiv μ k' (T (h'.l2Equiv μ h (h'.smoothToL2 μ u))) = _
  rw [h'.l2Equiv_smoothToL2 μ h, hT, k.l2Equiv_smoothToL2 μ k']

/-- Agreement with the same smooth operator identifies two bounded metric realizations. -/
theorem eq_l2MetricTransport_of_smoothToL2
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
    (T' : h'.L2SectionSpace μ →L[ℂ] k'.L2SectionSpace μ)
    (hT : ∀ u, T (h.smoothToL2 μ u) = k.smoothToL2 μ (P u))
    (hT' : ∀ u, T' (h'.smoothToL2 μ u) = k'.smoothToL2 μ (P u)) :
    T' = l2MetricTransport μ h h' k k' T := by
  /- The preceding calculation gives agreement on every smooth input. Both maps
  are continuous and the smooth inputs are dense in the new domain, so they agree. -/
  apply ContinuousLinearMap.ext
  have heq : (T' : h'.L2SectionSpace μ → k'.L2SectionSpace μ) =
      l2MetricTransport μ h h' k k' T := by
    apply (h'.denseRange_smoothToL2 μ).equalizer T'.continuous
      (l2MetricTransport μ h h' k k' T).continuous
    funext u
    exact (hT' u).trans (l2MetricTransport_smoothToL2 μ h h' k k' P T hT u).symm
  exact congrFun heq

/-- The reverse metric transport recovers the entire bounded operator. -/
theorem l2MetricTransport_reverse (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ) :
    l2MetricTransport μ h' h k' k (l2MetricTransport μ h h' k k' T) = T := by
  /- Expand both transports and cancel the input and output inverse pairs.
  This is an identity of bounded maps on the completions, not just on smooth vectors. -/
  apply ContinuousLinearMap.ext
  intro u
  change k'.l2Equiv μ k
    (k.l2Equiv μ k' (T (h'.l2Equiv μ h (h.l2Equiv μ h' u)))) = T u
  rw [← h.l2Equiv_symm μ h', ← k.l2Equiv_symm μ k']
  simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- Bounded metric comparisons preserve Fredholmness in both directions. -/
theorem isFredholm_l2MetricTransport_iff
    (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ) :
    (l2MetricTransport μ h h' k k' T).IsFredholm ↔ T.IsFredholm := by
  /- The input equivalence identifies kernels, and the output equivalence
  identifies ranges and quotient cokernels. They preserve closedness and both
  finite dimensions. Apply the Hilbert-space Fredholm characterization; the
  reverse transport gives the converse. -/
  simp only [l2MetricTransport, ContinuousLinearMap.isFredholm_equiv_comp,
    ContinuousLinearMap.isFredholm_comp_equiv]

/-- The index of a Fredholm realization is independent of the chosen smooth fiber metrics. -/
theorem index_l2MetricTransport (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
    (hT : T.IsFredholm) :
    (l2MetricTransport μ h h' k k' T).index = T.index := by
  /- The two metric comparison equivalences are Fredholm of index zero. Apply
  index additivity to the exact composite B ∘ T ∘ A, then cancel the two
  zero indices. The supplied Fredholm hypothesis applies to the middle map. -/
  let A := h'.l2Equiv μ h
  let B := k.l2Equiv μ k'
  -- The same two comparison maps are Fredholm of index zero, since they are bijective.
  have hA : A.toContinuousLinearMap.index = 0 := LinearMap.index_of_bijective A.bijective
  have hB : B.toContinuousLinearMap.index = 0 := LinearMap.index_of_bijective B.bijective
  change (B.toContinuousLinearMap.comp (T.comp A.toContinuousLinearMap)).index = T.index
  -- Apply index additivity to this exact conjugation, then cancel the two zero indices.
  rw [B.isFredholm.index_comp (hT.comp A.isFredholm), hT.index_comp A.isFredholm]
  rw [hA, hB, zero_add, add_zero]

end AtiyahSinger
