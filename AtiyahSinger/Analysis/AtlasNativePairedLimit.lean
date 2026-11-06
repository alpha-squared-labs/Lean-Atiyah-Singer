/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasNativeResidualApproximation

/-!
# Paired norm limits for the specified native operators

Public module ID: M0263.

The original forward and reverse extensions, metric completions and one bounded
residual determine norm limits for a native PDO family and its literal adjoint.
Every smooth value remains that of the supplied family. This common interface
is used for the four corners of the associated product without changing domains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Filter
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- The extended limit accommodates both residual bounds and the paired operator-adjoint limits.
/-- Positive and negative error bounds give paired limits with R and its adjoint. -/
theorem exists_atlas_native_residual_paired_limit
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (Li : AtlasBundlePresentation A) (Lo : AtlasBundlePresentation B)
    (N₀ N₁ : SmoothFiniteComplexBundle (n := n) M)
    (h : SmoothHermitianMetric (n := n) (r := N₀.rank) N₀.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := N₁.rank) N₁.Fiber)
    (Di : SmoothBundlePresentation (n := n) (r := N₀.rank) N₀.Fiber)
    (Do : SmoothBundlePresentation (n := n) (r := N₁.rank) N₁.Fiber) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    ∀ (e : Iso E N₀.Fiber) (f : Iso F N₁.Fiber)
      (he : IsSmoothAtlasBundleMap A (nativeSmoothComplexBundleAtlas N₀.Fiber)
        e.toHom.linearMap)
      (hei : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀.Fiber) A
        e.symm.toHom.linearMap)
      (hf : IsSmoothAtlasBundleMap B (nativeSmoothComplexBundleAtlas N₁.Fiber)
        f.toHom.linearMap)
      (hfi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁.Fiber) B
        f.symm.toHom.linearMap),
      let S₀ := (atlasSmoothSectionEquiv A (nativeSmoothComplexBundleAtlas N₀.Fiber)
        e he hei).trans (nativeSmoothSectionLinearEquiv N₀.Fiber)
      let S₁ := (atlasSmoothSectionEquiv B (nativeSmoothComplexBundleAtlas N₁.Fiber)
        f hf hfi).trans (nativeSmoothSectionLinearEquiv N₁.Fiber)
      ∀ (Θi : Li.SobolevSpace 0 ≃L[ℂ] h.L2SectionSpace μ)
        (Θo : Lo.SobolevSpace 0 ≃L[ℂ] k.L2SectionSpace μ),
        (∀ u, Θi (Li.smoothToSobolev 0 u) = h.smoothToL2 μ (S₀ u)) →
        (∀ v, Θo (Lo.smoothToSobolev 0 v) = k.smoothToL2 μ (S₁ v)) →
        ∀ (T W : A.smoothSections →ₗ[ℂ] B.smoothSections)
          (S : B.smoothSections →ₗ[ℂ] A.smoothSections)
          (Tb : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)
          (Sb : Lo.SobolevSpace 1 →L[ℂ] Li.SobolevSpace 0)
          (R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ),
          (∀ u v, k.sectionPairing μ (S₁ (T u)) (S₁ v) =
            h.sectionPairing μ (S₀ u) (S₀ (S v))) →
          (∀ u, R (h.smoothToL2 μ (S₀ u)) = k.smoothToL2 μ (S₁ (W u))) →
          (∀ u, Tb (Li.smoothToSobolev 1 u) = Lo.smoothToSobolev 0 (T u)) →
          (∀ v, Sb (Lo.smoothToSobolev 1 v) = Li.smoothToSobolev 0 (S v)) →
          ∀ (Cp Cn : ℝ), 0 ≤ Cp → 0 ≤ Cn →
          ∀ {ι : Type*} (l : Filter ι) (ε : ι → ℝ),
          (∀ t, 0 ≤ ε t) → Tendsto ε l (𝓝 0) →
          ∀ (P : ι → PseudodifferentialOperator N₀.Fiber N₁.Fiber μ 1)
            (Pa : ι → A.smoothSections →ₗ[ℂ] B.smoothSections),
            (∀ t u, (P t).toLinearMap (S₀ u) = S₁ (Pa t u)) →
            (∀ t u, ‖Lo.smoothToSobolev 0 (Pa t u - T u + W u)‖ ≤
              Cp * ε t * ‖Li.smoothToSobolev 1 u‖) →
            (∀ t u, ‖Lo.smoothToSobolev (-1) (Pa t u - T u + W u)‖ ≤
              Cn * ε t * ‖Li.smoothToSobolev 0 u‖) →
            let Ji := Θi.toContinuousLinearMap.comp (Li.sobolevInclusion 1 0 (by norm_num))
            let Jo := Θo.toContinuousLinearMap.comp (Lo.sobolevInclusion 1 0 (by norm_num))
            ∃ (Ts : ι → Li.SobolevSpace 1 →L[ℂ] k.L2SectionSpace μ)
              (Ss : ι → Lo.SobolevSpace 1 →L[ℂ] h.L2SectionSpace μ),
              (∀ t u, Ts t (Li.smoothToSobolev 1 u) =
                k.smoothToL2 μ ((P t).toLinearMap (S₀ u))) ∧
              (∀ t v, Ss t (Lo.smoothToSobolev 1 v) =
                h.smoothToL2 μ (((P t).metricFormalAdjoint h k).toLinearMap (S₁ v))) ∧
              Tendsto (fun t ↦ Ts t + R.comp Ji) l (𝓝 (Θo.toContinuousLinearMap.comp Tb)) ∧
              Tendsto (fun t ↦ Ss t + R.adjoint.comp Jo) l
                (𝓝 (Θi.toContinuousLinearMap.comp Sb)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro e f he hei hf hfi S₀ S₁ Θi Θo hΘi hΘo T W S Tb Sb R hpair hR hTb hSb
    Cp Cn hCp hCn ι l ε hε hεlim P Pa hP hpos hneg Ji Jo
  -- The domain equivalences use the same smooth maps as the metric completions.
  obtain ⟨Ξi, hΞi⟩ := A.exists_sobolev_equiv_native Li N₀ Di 1 e he hei
  obtain ⟨Ξo, hΞo⟩ := B.exists_sobolev_equiv_native Lo N₁ Do 1 f hf hfi
  let Φ := h.sobolevZeroEquivL2 (μ := μ) Di
  let Ψ := k.sobolevZeroEquivL2 (μ := μ) Do
  let Ts (t : ι) := (Ψ.toContinuousLinearMap.comp
    ((P t).sobolevRealization Di Do 1 0 (by norm_num))).comp Ξi.toContinuousLinearMap
  let Ss (t : ι) := (Φ.toContinuousLinearMap.comp
    (((P t).metricFormalAdjoint h k).sobolevRealization Do Di 1 0 (by norm_num))).comp
      Ξo.toContinuousLinearMap
  have hTs (t : ι) (u : A.smoothSections) : Ts t (Li.smoothToSobolev 1 u) =
      k.smoothToL2 μ ((P t).toLinearMap (S₀ u)) := by
    change Ψ ((P t).sobolevRealization Di Do 1 0 (by norm_num)
      (Ξi (Li.smoothToSobolev 1 u))) = _
    rw [hΞi, (P t).sobolevRealization_smoothToSobolev,
      k.sobolevZeroEquivL2_smooth]
  have hSs (t : ι) (v : B.smoothSections) : Ss t (Lo.smoothToSobolev 1 v) =
      h.smoothToL2 μ (((P t).metricFormalAdjoint h k).toLinearMap (S₁ v)) := by
    change Φ (((P t).metricFormalAdjoint h k).sobolevRealization Do Di 1 0 (by norm_num)
      (Ξo (Lo.smoothToSobolev 1 v))) = _
    rw [hΞo, ((P t).metricFormalAdjoint h k).sobolevRealization_smoothToSobolev,
      h.sobolevZeroEquivL2_smooth]
  have hforward (t : ι) : ‖Ts t + R.comp Ji - Θo.toContinuousLinearMap.comp Tb‖ ≤
      (‖Θo.toContinuousLinearMap‖ * Cp) * ε t := by
    let Err := Ts t + R.comp Ji - Θo.toContinuousLinearMap.comp Tb
    apply Err.opNorm_le_bound (mul_nonneg (mul_nonneg (norm_nonneg _) hCp) (hε t))
    intro x
    refine (Li.denseRange_smoothToSobolev 1).induction_on x
      (isClosed_le (Err.continuous.norm) (continuous_const.mul continuous_norm)) ?_
    intro u
    have heq : Err (Li.smoothToSobolev 1 u) =
        Θo (Lo.smoothToSobolev 0 (Pa t u - T u + W u)) := by
      change Ts t (Li.smoothToSobolev 1 u) +
        R (Θi (Li.sobolevInclusion 1 0 (by norm_num) (Li.smoothToSobolev 1 u))) -
          Θo (Tb (Li.smoothToSobolev 1 u)) = _
      rw [hTs, hP, Li.sobolevInclusion_smoothToSobolev, hΘi, hR, hTb]
      rw [map_add, map_sub, map_add, map_sub, hΘo, hΘo, hΘo]
      abel
    rw [heq]
    exact (Θo.toContinuousLinearMap.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (hpos t u) (norm_nonneg _)).trans_eq (by ring))
  -- The same negative-order error bounds the actual adjoint with this residual's adjoint.
  obtain ⟨C, hC, hbound⟩ := exists_atlas_native_residual_adjoint_bound μ A B Li Lo
    N₀ N₁ h k Di Do e f he hei hf hfi Ξo Θi Θo hΞo hΘi hΘo
  have hreverse (t : ι) : ‖Ss t + R.adjoint.comp Jo - Θi.toContinuousLinearMap.comp Sb‖ ≤
      (C * Cn) * ε t := by
    have hb := hbound (Cn * ε t) (mul_nonneg hCn (hε t))
      T W S Sb R (P t) (Pa t) hpair hR hSb (hP t) (hneg t)
    have heq : Ss t + R.adjoint.comp Jo - Θi.toContinuousLinearMap.comp Sb =
        Ss t - Θi.toContinuousLinearMap.comp Sb + R.adjoint.comp Jo := by abel
    rw [heq]
    exact hb.trans_eq (mul_assoc _ _ _).symm
  refine ⟨Ts, Ss, hTs, hSs, ?_, ?_⟩
  · -- Both limits are in operator norm on the fixed original domain, not pointwise limits.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun t ↦ norm_nonneg _) hforward
    simpa only [mul_zero] using hεlim.const_mul (‖Θo.toContinuousLinearMap‖ * Cp)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun t ↦ norm_nonneg _) hreverse
    simpa only [mul_zero] using hεlim.const_mul (C * Cn)

end AtiyahSinger
