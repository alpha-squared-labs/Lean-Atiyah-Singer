/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticKernel
public import AtiyahSinger.Analysis.HermitianMetricAdjointKernel
public import AtiyahSinger.Analysis.SmoothFiniteRankProjection

/-!
# Removing the smooth kernel of a symmetric elliptic operator

Public module ID: M0957.

Add the orthogonal projection onto the actual smooth kernel. The correction
has a smooth kernel, hence preserves the original principal class. Symmetry
identifies the cokernel with the same zero kernel after correction. All-order
Sobolev comparison gives the specified bounded isomorphisms.

This is a standard Fredholm correction argument for constructing invertible
elliptic representatives; it does not identify a particular spectral power.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]



variable (h : SmoothHermitianMetric (n := n) (r := r) E)

namespace PseudodifferentialOperator

/-- A symmetric elliptic operator has a smoothing correction invertible at every Sobolev order. -/
theorem exists_bijective_of_isMetricFormalAdjoint {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m)
    (hP : P.IsElliptic) (hself : IsMetricFormalAdjoint h h μ P.toLinearMap P.toLinearMap) :
    ∃ J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m,
      J.principalSymbol = P.principalSymbol ∧ J.IsElliptic ∧
      Function.Bijective J.toLinearMap ∧
      ∀ (S : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ),
        Function.Bijective (J.sobolevExtension S S s) := by
  classical
  obtain ⟨S₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  let W : Submodule ℂ (h.SmoothL2Section μ) := P.toLinearMap.ker
  let : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isParametrix S₀ S₀ Q hQ
  let K := smoothOrthogonalProjection μ h W
  have hK := isSmoothingOperator_smoothOrthogonalProjection μ h W
  let KP : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m :=
    ⟨K, hK.isPseudodifferentialOperator m K⟩
  let J := P.add KP
  -- The projection is smoothing, so the original principal class and ellipticity are retained.
  have hKclass : KP.principalSymbol = 0 :=
    KP.principalSymbol_eq_zero_iff.mpr (hK.isPseudodifferentialOperator (m - 1) K)
  have hclass : J.principalSymbol = P.principalSymbol := by
    rw [principalSymbol_add, hKclass, add_zero]
  have hJ : J.IsElliptic := (P.isElliptic_iff_of_principalSymbol_eq_operator J hclass.symm).mp hP
  have hKself : IsMetricFormalAdjoint h h μ K K := by
    intro u v
    exact W.inner_starProjection_left_eq_right u v
  have hJself : IsMetricFormalAdjoint h h μ J.toLinearMap J.toLinearMap := hself.add hKself
  have hJadj : J.metricFormalAdjoint h h = J := J.metricFormalAdjoint_eq h h J hJself
  -- Any corrected zero is orthogonal to its own projection into the original kernel.
  have hinj : Function.Injective J.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    have heq : P.toLinearMap u + K u = 0 := hu
    have hKu : P.toLinearMap (K u) = 0 := W.starProjection_apply_mem u
    have hpair : h.sectionPairing μ (K u) (P.toLinearMap u) = 0 := by
      rw [← hself, hKu]
      exact inner_zero_left (𝕜 := ℂ) (E := h.SmoothL2Section μ) u
    have hKzero : K u = 0 := by
      apply (h.sectionPairing_self_eq_zero_iff μ _).mp
      have hneg : P.toLinearMap u = -K u := eq_neg_of_add_eq_zero_left heq
      rw [hneg] at hpair
      have hn : h.sectionPairing μ (K u) (-K u) = -h.sectionPairing μ (K u) (K u) :=
        inner_neg_right (𝕜 := ℂ) (E := h.SmoothL2Section μ) (K u) (K u)
      rw [hn] at hpair
      exact neg_eq_zero.mp hpair
    have hPu : P.toLinearMap u = 0 := by simpa only [hKzero, add_zero] using heq
    have hfix : K u = u := W.starProjection_eq_self_iff.mpr hPu
    exact hfix.symm.trans hKzero
  -- The actual smooth Fredholm alternative now gives surjectivity without closing the range.
  obtain ⟨R, hR⟩ := J.exists_parametrix_of_isElliptic hJ
  have hsurj : Function.Surjective J.toLinearMap := by
    intro v
    apply (J.mem_range_iff_pairing_metricFormalAdjoint_eq_zero h h S₀ S₀ R hR v).mpr
    intro w
    have hw : J.toLinearMap w.val = 0 := by
      exact (congrArg (fun L : PseudodifferentialOperator (n := n) (r := r) (q := r)
        E E μ m ↦ L.toLinearMap w.val) hJadj).symm.trans w.property
    have hwzero : w.val = 0 := hinj (by simpa using hw)
    rw [hwzero]
    exact inner_zero_left (𝕜 := ℂ) (E := h.SmoothL2Section μ) v
  refine ⟨J, hclass, hJ, ⟨hinj, hsurj⟩, ?_⟩
  intro S s
  -- Natural smooth-to-Sobolev kernel and cokernel comparisons retain this same corrected map.
  let T := J.sobolevExtension S S s
  have hTfred := J.isFredholm_sobolevExtension_of_isParametrix R S S hR s
  have hfinite := (isFredholm_iff_closed_range_finite T).mp hTfred
  let : FiniteDimensional ℂ T.ker := hfinite.2.1
  let : FiniteDimensional ℂ (S.SobolevSpace (s - m) ⧸ T.range) := hfinite.2.2
  have hker : Module.finrank ℂ T.ker = 0 := by
    rw [J.finrank_ker_sobolevExtension_of_isSmoothingOperator S S R hR.1 s,
      LinearMap.ker_eq_bot.mpr hinj]
    simp
  have hcoker : Module.finrank ℂ (S.SobolevSpace (s - m) ⧸ T.range) = 0 := by
    rw [J.finrank_coker_sobolevExtension_of_isParametrix S S R hR s]
    let : Subsingleton (smoothSections (n := n) (r := r) E ⧸ J.toLinearMap.range) :=
      Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hsurj)
    exact Module.finrank_zero_of_subsingleton
  let : Subsingleton T.ker := Module.finrank_zero_iff.mp hker
  exact ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton,
    LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp
      (Module.finrank_zero_iff.mp hcoker))⟩

end PseudodifferentialOperator

end AtiyahSinger
