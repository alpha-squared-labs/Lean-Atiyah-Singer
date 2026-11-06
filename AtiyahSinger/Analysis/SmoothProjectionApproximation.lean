/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactProjectionApproximation
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.SmoothFiniteRankProjection

/-!
# Smooth contraction approximations of the actual Sobolev inclusion

Public module ID: M0975.

Finite-dimensional spaces of the original smooth sections give actual smooth
integral operators that are contractions on the prescribed metric L2 space.
Their compositions with the same H1 inclusion approximate that inclusion in
operator norm. No eigenbasis, spectral PDO identification or changed density
is needed. This regularizes the otherwise non-smoothing tensor remainder in
the global construction underlying SG III.13.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- Actual smooth-kernel contractions approximate the same geometric H1-to-L2 inclusion. -/
theorem exists_smoothProjection_sobolev_approximation
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (A : SmoothBundlePresentation (n := n) (r := r) E) (ε : ℝ) (hε : 0 < ε) :
    let I := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
    ∃ J : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E,
      IsSmoothingOperator μ J ∧
        ∃ T : h.L2SectionSpace μ →L[ℂ] h.L2SectionSpace μ,
          ‖T‖ ≤ 1 ∧
            (∀ u : smoothSections (n := n) (r := r) E,
              T (h.smoothToL2 μ u) = h.smoothToL2 μ (J u)) ∧
            ‖I - T.comp I‖ < ε := by
  let I := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  let j : h.SmoothL2Section μ →ₗᵢ[ℂ] h.L2SectionSpace μ :=
    UniformSpace.Completion.toComplₗᵢ
  -- Rellich applies to the original Sobolev inclusion; the metric comparison retains sections.
  have hI : IsCompactOperator I :=
    (A.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap
  obtain ⟨s, hs⟩ := exists_finite_projection_approximation j
    (h.denseRange_smoothToL2 μ) I hI ε hε
  let W := Submodule.span ℂ (s : Set (h.SmoothL2Section μ))
  let V := W.map j.toLinearMap
  let J := smoothOrthogonalProjection μ h W
  let T := V.starProjection
  -- The finite smooth projection already has an actual smooth kernel for this very density.
  refine ⟨J, isSmoothingOperator_smoothOrthogonalProjection μ h W,
    T, V.starProjection_norm_le, ?_, hs⟩
  intro u
  -- The canonical completion isometry intertwines the two actual orthogonal projections.
  exact (j.map_starProjection W u).symm

variable {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option backward.isDefEq.respectTransparency false in
/-- A bounded L2 operator preserving a dense smooth core is approximated on H1 by actual
smooth kernels. Only the finite chosen core vectors need smooth output representatives. -/
theorem exists_smoothing_approximation_of_smooth_core
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (D : Submodule ℂ (h.SmoothL2Section μ))
    (hD : DenseRange (fun u : D ↦ h.smoothToL2 μ u.val))
    (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
    (hT : ∀ u : D, ∃ v : smoothSections (n := n) (r := q) F,
      T (h.smoothToL2 μ u.val) = k.smoothToL2 μ v) (ε : ℝ) (hε : 0 < ε) :
    let I := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
    ∃ J : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F,
      IsSmoothingOperator μ J ∧
        ∃ R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ,
          (∀ u : smoothSections (n := n) (r := r) E,
            R (h.smoothToL2 μ u) = k.smoothToL2 μ (J u)) ∧
          ‖T.comp I - R.comp I‖ < ε := by
  classical
  let I := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  let j : D →ₗᵢ[ℂ] h.L2SectionSpace μ :=
    UniformSpace.Completion.toComplₗᵢ.comp D.subtypeₗᵢ
  have hI : IsCompactOperator I :=
    (A.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap
  have hdenom : 0 < ‖T‖ + 1 := by positivity
  -- Approximate the compact inclusion using vectors in the specified smooth core.
  obtain ⟨s, hs⟩ := exists_finite_projection_approximation j hD I hI
    (ε / (‖T‖ + 1)) (div_pos hε hdenom)
  let W := Submodule.span ℂ (s : Set D)
  let V := W.map j.toLinearMap
  let b := stdOrthonormalBasis ℂ W
  let v (i : Fin (Module.finrank ℂ W)) : h.SmoothL2Section μ := (b i).val.val
  choose w hw using fun i : Fin (Module.finrank ℂ W) ↦ hT (b i).val
  let J : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F :=
    ∑ i, (innerSL ℂ (v i)).toLinearMap.smulRight (w i)
  let R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ :=
    ∑ i, (innerSL ℂ (h.smoothToL2 μ (v i))).smulRight (k.smoothToL2 μ (w i))
  -- Every coefficient is the actual L2 pairing with a smooth input vector.
  -- Geometric duality extends the finite rank-one sum between all Sobolev orders.
  have hJ : IsSmoothingOperator μ J := by
    obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
    apply (isSmoothingOperator_iff_sobolevExtensions μ J A B).mpr
    intro a c
    let f (i : Fin (Module.finrank ℂ W)) : StrongDual ℂ (A.SobolevSpace a) :=
      h.sobolevDuality A μ a (A.smoothToSobolev (-a) (v i))
    refine ⟨∑ i, (f i).smulRight (B.smoothToSobolev c (w i)), ?_⟩
    intro u
    simp only [J, sum_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul,
      ContinuousLinearMap.smulRight_apply]
    apply Finset.sum_congr rfl
    intro i _
    change h.sobolevPairing A μ a (A.smoothToSobolev (-a) (v i))
      (A.smoothToSobolev a u) • B.smoothToSobolev c (w i) = _
    rw [h.sobolevPairing_smooth]
    rfl
  have hR (u : smoothSections (n := n) (r := r) E) :
      R (h.smoothToL2 μ u) = k.smoothToL2 μ (J u) := by
    simp only [R, J, sum_apply, LinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.smulRight_apply, map_sum, map_smul, innerSL_apply_apply,
      h.inner_smoothToL2]
    rfl
  -- The same finite sum equals T after the original orthogonal projection.
  have hRV : R = T.comp V.starProjection := by
    apply DFunLike.ext'
    apply hD.equalizer R.continuous (T.comp V.starProjection).continuous
    funext u
    change R (j u) = T (V.starProjection (j u))
    rw [← j.map_starProjection W u, b.starProjection_eq_sum_rankOne]
    simp only [sum_apply, InnerProductSpace.rankOne_apply, map_sum, map_smul]
    change (∑ i, (innerSL ℂ (h.smoothToL2 μ (v i))).smulRight
      (k.smoothToL2 μ (w i))) (j u) = _
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hi : h.smoothToL2 μ (v i) = j (b i).val := rfl
    rw [hi, j.inner_map_map]
    change _ = inner ℂ (b i).val u • T (h.smoothToL2 μ (b i).val.val)
    rw [hw i]
  refine ⟨J, hJ, R, hR, ?_⟩
  -- Only the original H1 inclusion is approximated, giving operator-norm convergence.
  rw [hRV, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_sub]
  calc
    ‖T.comp (I - V.starProjection.comp I)‖ ≤
        ‖T‖ * ‖I - V.starProjection.comp I‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖T‖ + 1) * ‖I - V.starProjection.comp I‖ := by gcongr; linarith
    _ < (‖T‖ + 1) * (ε / (‖T‖ + 1)) := mul_lt_mul_of_pos_left hs hdenom
    _ = ε := mul_div_cancel₀ ε hdenom.ne'

end AtiyahSinger
