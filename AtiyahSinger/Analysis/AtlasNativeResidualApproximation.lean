/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasNativeSobolevEquivalence
public import AtiyahSinger.Analysis.ResidualAdjointApproximation

/-!
# Residual adjoint estimates on the atlas domain

Public module ID: M0265.

Transport a negative-order error through the supplied smooth bundle maps.
Its paired reverse error uses the given bounded residual's literal adjoint,
with the specified metric completions and order-one domain. The resulting
operator-norm bound has a constant fixed before the maps and error size.
This is the common estimate used for horizontal and vertical corners.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

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
-- The extended limit accommodates the literal adjoint and uniform atlas residual bounds.
/-- The corrected literal adjoint has a uniform bound on the specified atlas domain. -/
theorem exists_atlas_native_residual_adjoint_bound
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
      ∀ (Ξo : Lo.SobolevSpace 1 ≃L[ℂ] Do.SobolevSpace 1)
        (Θi : Li.SobolevSpace 0 ≃L[ℂ] h.L2SectionSpace μ)
        (Θo : Lo.SobolevSpace 0 ≃L[ℂ] k.L2SectionSpace μ),
        (∀ v, Ξo (Lo.smoothToSobolev 1 v) = Do.smoothToSobolev 1 (S₁ v)) →
        (∀ u, Θi (Li.smoothToSobolev 0 u) = h.smoothToL2 μ (S₀ u)) →
        (∀ v, Θo (Lo.smoothToSobolev 0 v) = k.smoothToL2 μ (S₁ v)) →
        let Φ := h.sobolevZeroEquivL2 (μ := μ) Di
        let Jo := Θo.toContinuousLinearMap.comp (Lo.sobolevInclusion 1 0 (by norm_num))
        ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
          ∀ (T W : A.smoothSections →ₗ[ℂ] B.smoothSections)
            (S : B.smoothSections →ₗ[ℂ] A.smoothSections)
            (Sb : Lo.SobolevSpace 1 →L[ℂ] Li.SobolevSpace 0)
            (R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
            (P : PseudodifferentialOperator N₀.Fiber N₁.Fiber μ 1)
            (Pa : A.smoothSections →ₗ[ℂ] B.smoothSections),
            (∀ u v, k.sectionPairing μ (S₁ (T u)) (S₁ v) =
              h.sectionPairing μ (S₀ u) (S₀ (S v))) →
            (∀ u, R (h.smoothToL2 μ (S₀ u)) = k.smoothToL2 μ (S₁ (W u))) →
            (∀ v, Sb (Lo.smoothToSobolev 1 v) = Li.smoothToSobolev 0 (S v)) →
            (∀ u, P.toLinearMap (S₀ u) = S₁ (Pa u)) →
            (∀ u, ‖Lo.smoothToSobolev (-1) (Pa u - T u + W u)‖ ≤
              δ * ‖Li.smoothToSobolev 0 u‖) →
            ‖(Φ.toContinuousLinearMap.comp
                ((P.metricFormalAdjoint h k).sobolevRealization Do Di 1 0 (by norm_num))).comp
                  Ξo.toContinuousLinearMap - Θi.toContinuousLinearMap.comp Sb +
                    R.adjoint.comp Jo‖ ≤ C * δ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro e f he hei hf hfi S₀ S₁ Ξo Θi Θo hΞo hΘi hΘo Φ Jo
  -- The two norm comparisons retain the original smooth isomorphisms.
  obtain ⟨Ξi₀, hΞi₀⟩ := A.exists_sobolev_equiv_native Li N₀ Di 0 e he hei
  obtain ⟨ΞoNeg, hΞoNeg⟩ := B.exists_sobolev_equiv_native Lo N₁ Do (-1) f hf hfi
  obtain ⟨Cd, hCd, hdual⟩ := exists_residual_metricFormalAdjoint_sub_bound μ h k Di Do
  refine ⟨Cd * (‖ΞoNeg.toContinuousLinearMap‖ * ‖Ξi₀.symm.toContinuousLinearMap‖) *
    ‖Ξo.toContinuousLinearMap‖, by positivity, ?_⟩
  intro δ hδ T W S Sb R P Pa hpair hR hSb hP hneg
  let Tn := S₁.toLinearMap.comp (T.comp S₀.symm.toLinearMap)
  let Wn := S₁.toLinearMap.comp (W.comp S₀.symm.toLinearMap)
  let Sn := S₀.toLinearMap.comp (S.comp S₁.symm.toLinearMap)
  let Sbn := Φ.symm.toContinuousLinearMap.comp
    ((Θi.toContinuousLinearMap.comp Sb).comp Ξo.symm.toContinuousLinearMap)
  have hSbn (v : smoothSections N₁.Fiber) :
      Sbn (Do.smoothToSobolev 1 v) = Di.smoothToSobolev 0 (Sn v) := by
    have hv := hΞo (S₁.symm v)
    rw [S₁.apply_symm_apply] at hv
    change Φ.symm (Θi (Sb (Ξo.symm (Do.smoothToSobolev 1 v)))) = _
    rw [← hv, Ξo.symm_apply_apply, hSb, hΘi]
    apply Φ.injective
    rw [Φ.apply_symm_apply, h.sobolevZeroEquivL2_smooth]
    rfl
  have hpairN : IsMetricFormalAdjoint h k μ Tn Sn := by
    intro u v
    have hp := hpair (S₀.symm u) (S₁.symm v)
    rw [S₀.apply_symm_apply, S₁.apply_symm_apply] at hp
    exact hp
  have hRN (u : smoothSections N₀.Fiber) :
      R (h.smoothToL2 μ u) = k.smoothToL2 μ (Wn u) := by
    simpa only [Wn, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      S₀.apply_symm_apply] using hR (S₀.symm u)
  have hnegN (u : smoothSections N₀.Fiber) :
      ‖Do.smoothToSobolev (-1) (P.toLinearMap u - Tn u + Wn u)‖ ≤
        (‖ΞoNeg.toContinuousLinearMap‖ * ‖Ξi₀.symm.toContinuousLinearMap‖ * δ) *
          ‖Di.smoothToSobolev 0 u‖ := by
    have hp := hP (S₀.symm u)
    rw [S₀.apply_symm_apply] at hp
    have hinput : Li.smoothToSobolev 0 (S₀.symm u) =
        Ξi₀.symm (Di.smoothToSobolev 0 u) := by
      apply Ξi₀.injective
      rw [hΞi₀, S₀.apply_symm_apply, Ξi₀.apply_symm_apply]
    have hvalue : P.toLinearMap u - Tn u + Wn u =
        S₁ (Pa (S₀.symm u) - T (S₀.symm u) + W (S₀.symm u)) := by
      rw [hp, map_add, map_sub]
      rfl
    rw [hvalue, ← hΞoNeg]
    calc
      _ ≤ ‖ΞoNeg.toContinuousLinearMap‖ *
          ‖Lo.smoothToSobolev (-1) (Pa (S₀.symm u) - T (S₀.symm u) + W (S₀.symm u))‖ :=
        ΞoNeg.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖ΞoNeg.toContinuousLinearMap‖ * (δ * ‖Li.smoothToSobolev 0 (S₀.symm u)‖) :=
        mul_le_mul_of_nonneg_left (hneg _) (norm_nonneg _)
      _ ≤ ‖ΞoNeg.toContinuousLinearMap‖ *
          (δ * (‖Ξi₀.symm.toContinuousLinearMap‖ * ‖Di.smoothToSobolev 0 u‖)) := by
        rw [hinput]
        gcongr
        exact Ξi₀.symm.toContinuousLinearMap.le_opNorm _
      _ = _ := by ring
  -- Apply dense-core duality, then transport its norm to the original order-one domain.
  let Ψ := k.sobolevZeroEquivL2 (μ := μ) Do
  let Jn := Ψ.toContinuousLinearMap.comp (Do.sobolevInclusion 1 0 (by norm_num))
  let ErrN := Φ.toContinuousLinearMap.comp
    ((P.metricFormalAdjoint h k).sobolevRealization Do Di 1 0 (by norm_num) - Sbn) +
      R.adjoint.comp Jn
  have hb : ‖ErrN‖ ≤ Cd *
      (‖ΞoNeg.toContinuousLinearMap‖ * ‖Ξi₀.symm.toContinuousLinearMap‖ * δ) :=
    hdual _ (by positivity) Tn Wn Sn Sbn R P hpairN hRN hSbn hnegN
  have hcoords : Jn.comp Ξo.toContinuousLinearMap = Jo := by
    apply ContinuousLinearMap.ext
    intro x
    refine (Lo.denseRange_smoothToSobolev 1).induction_on x
      (isClosed_eq (Jn.comp Ξo.toContinuousLinearMap).continuous Jo.continuous) ?_
    intro v
    change Ψ (Do.sobolevInclusion 1 0 (by norm_num)
      (Ξo (Lo.smoothToSobolev 1 v))) =
        Θo (Lo.sobolevInclusion 1 0 (by norm_num) (Lo.smoothToSobolev 1 v))
    rw [hΞo, Do.sobolevInclusion_smoothToSobolev,
      Lo.sobolevInclusion_smoothToSobolev, hΘo, k.sobolevZeroEquivL2_smooth]
  have heq : (Φ.toContinuousLinearMap.comp
      ((P.metricFormalAdjoint h k).sobolevRealization Do Di 1 0 (by norm_num))).comp
        Ξo.toContinuousLinearMap - Θi.toContinuousLinearMap.comp Sb + R.adjoint.comp Jo =
          ErrN.comp Ξo.toContinuousLinearMap := by
    ext x
    change _ = Φ ((P.metricFormalAdjoint h k).sobolevRealization Do Di 1 0
      (by norm_num) (Ξo x) - Φ.symm (Θi (Sb (Ξo.symm (Ξo x))))) + R.adjoint (Jn (Ξo x))
    rw [Ξo.symm_apply_apply, map_sub, Φ.apply_symm_apply]
    exact congrArg (fun w ↦ _ + R.adjoint w) (congrArg (fun L ↦ L x) hcoords).symm
  rw [heq]
  calc
    _ ≤ ‖ErrN‖ * ‖Ξo.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Cd * (‖ΞoNeg.toContinuousLinearMap‖ *
        ‖Ξi₀.symm.toContinuousLinearMap‖ * δ)) * ‖Ξo.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by ring

end AtiyahSinger
