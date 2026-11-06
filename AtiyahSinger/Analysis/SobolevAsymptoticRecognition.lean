/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialAsymptotics

/-!
# Recognition of an actual operator from Sobolev asymptotic remainders

Public module ID: M0989.

Ordinary PDO Borel summation is enough when a prescribed smooth-section action
has arbitrarily regular Sobolev remainders after finite truncation. The finite
remainders need not have PDO certificates: one asymptotic sum is formed from
the genuine PDO terms, and the all-order Sobolev criterion identifies the
difference from the prescribed action as a smooth-kernel operator.

This is a supporting analytic interface for the finite-resolvent approach to A09.
It does not assert that the specified spectral power meets its hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

/-- Arbitrarily regular finite Sobolev remainders identify an actual PDO expansion. -/
theorem has_pseudodifferential_expansion_of_sobolev_remainders
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (m : ℕ → ℝ) (hm : StrictAnti m) (hlim : Tendsto m atTop atBot)
    (terms : ℕ → (smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F))
    (hterms : ∀ j : ℕ, IsPseudodifferentialOperator E F μ (m j) (terms j))
    (T : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (hremainder : ∀ s t : ℝ, ∃ N : ℕ, m N ≤ s - t ∧
      ∃ V : A.SobolevSpace s →L[ℂ] B.SobolevSpace t,
        ∀ u : smoothSections (n := n) (r := r) E,
          V (A.smoothToSobolev s u) =
            B.smoothToSobolev t ((T - ∑ j ∈ Finset.range N, terms j) u)) :
    ∀ N : ℕ, IsPseudodifferentialOperator E F μ (m N)
      (T - ∑ j ∈ Finset.range N, terms j) := by
  /- First sum only the known PDO terms. At any two Sobolev orders, use the
  same truncation for this Borel sum and for the prescribed operator. Their
  finite sums cancel, giving a bounded realization of the fixed difference.
  The all-order criterion then produces one actual smooth kernel. -/
  obtain ⟨Q, hQ⟩ := exists_pseudodifferential_expansion μ m hm hlim terms hterms
  have hsmoothing : IsSmoothingOperator μ (T - Q.toLinearMap) := by
    apply (isSmoothingOperator_iff_sobolevExtensions μ (T - Q.toLinearMap) A B).mpr
    intro s t
    obtain ⟨N, hN, V, hV⟩ := hremainder s t
    let R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m N) :=
      ⟨Q.toLinearMap - ∑ j ∈ Finset.range N, terms j, hQ N⟩
    have ht : t ≤ s - m N := by linarith
    refine ⟨V - R.sobolevRealization A B s t ht, ?_⟩
    intro u
    change V (A.smoothToSobolev s u) -
      R.sobolevRealization A B s t ht (A.smoothToSobolev s u) = _
    rw [hV u, R.sobolevRealization_smoothToSobolev A B s t ht u, ← map_sub]
    apply congrArg (B.smoothToSobolev t)
    change (T u - (∑ j ∈ Finset.range N, terms j) u) -
      (Q.toLinearMap u - (∑ j ∈ Finset.range N, terms j) u) = T u - Q.toLinearMap u
    abel
  -- Adding that same smoothing difference recovers every exact PDO remainder of T.
  intro N
  have hs := IsSmoothingOperator.isPseudodifferentialOperator (m N)
    (T - Q.toLinearMap) hsmoothing
  have hsum := IsPseudodifferentialOperator.add (m N) _ _ hs (hQ N)
  have heq : (T - Q.toLinearMap) +
      (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) =
        T - ∑ j ∈ Finset.range N, terms j := by abel
  rwa [heq] at hsum

end AtiyahSinger
