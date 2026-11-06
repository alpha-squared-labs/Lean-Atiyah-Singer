/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSymbolPiece
public import AtiyahSinger.Analysis.GeometricRightTensorFiniteApproximation
public import AtiyahSinger.Analysis.RightExternalTensorSmoothingApproximation

/-!
# Geometric tensor approximation with the original order-zero remainder

Public module ID: M0927.

The positive-frequency cutoffs act on the original external tensor bundles.
Their bounded realizations converge in the fixed geometric Sobolev norms, and
the limiting operator is specified on actual pure smooth tensor sections.
The fixed input and output charts and frames are used in every comparison.

Source: the finite-atlas assembly in SG III.13.5, pp.249--250.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped ContDiff Manifold SchwartzMap TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space N] [T2Space M]
  {F₀ F₁ : N → Type*} {E : M → Type*}
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, NormedSpace ℂ (F₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [IsSmoothComplexBundle (n := m) (r := s₁) F₁]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

variable [SecondCountableTopology N] [SecondCountableTopology M]
  [CompactSpace N] [CompactSpace M]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := m) ν] [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1800000 in
-- The extended limit accommodates the second-factor representation and order-zero tensor remainder.
/-- A finite second-factor representation plus its order-zero remainder admits genuine
product PDO approximants. Their difference from the specified cutoff sum is smoothing. -/
theorem exists_rightExternalTensor_finite_sum_approximation
    (h₀ : SmoothHermitianMetric (n := m) (r := s₀) F₀)
    (h₁ : SmoothHermitianMetric (n := m) (r := s₁) F₁)
    (k : SmoothHermitianMetric (n := n) (r := r) E)
    {ℓ : ℕ} (L : Fin ℓ → PseudodifferentialPiece (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (hL : ∀ i, HasCompactSupport (L i).symbol)
    (J : smoothSections (n := m) (r := s₀) F₀ →ₗ[ℂ] smoothSections (n := m) (r := s₁) F₁)
    (hJ : IsPseudodifferentialOperator F₀ F₁ ν 0 J)
    (Q : QuantizationPresentation (n := n) (r := r) (q := r) E E) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
    letI := externalTensorTopology (r := r) (s := s₀) E F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
    letI := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
    letI := externalTensorTopology (r := r) (s := s₁) E F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let g₁ := externalTensorMetric k h₁
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r * s₀) (externalTensorFiber E F₀))
      (D : SmoothBundlePresentation (n := n + m) (r := r * s₁) (externalTensorFiber E F₁)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
        (∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := m) (r := s₀) F₀),
          T (A.smoothToSobolev 1 (externalTensorSection E F₀ u v)) =
            g₁.smoothToL2 (μ.prod ν)
              (externalTensorSection E F₁ u (((∑ i, (L i).toLinearMap) + J) v))) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r * s₀) (q := r * s₁)
              (externalTensorFiber E F₀) (externalTensorFiber E F₁) (μ.prod ν) 1,
            IsSmoothingOperator (μ.prod ν) (P.toLinearMap - ∑ i, ∑ j,
              ((L i).rightProductCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
                (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
            ‖(g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap.comp
              (P.sobolevRealization A D 1 0 (by norm_num)) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
  let := externalTensorTopology (r := r) (s := s₀) E F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
  let := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
  let := externalTensorTopology (r := r) (s := s₁) E F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  dsimp only
  let g₀ := externalTensorMetric k h₀
  let g₁ := externalTensorMetric k h₁
  intro A D
  -- Build the bounded factor action of the original order-zero remainder.
  let A₀ := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s₀) F₀)
  let A₁ := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s₁) F₁)
  let e₀ := h₀.sobolevZeroEquivL2 (μ := ν) A₀
  let e₁ := h₁.sobolevZeroEquivL2 (μ := ν) A₁
  let J₀ : PseudodifferentialOperator (n := m) (r := s₀) (q := s₁) F₀ F₁ ν 0 :=
    ⟨J, hJ⟩
  let S₀ := e₁.toContinuousLinearMap.comp
    ((J₀.sobolevRealization A₀ A₁ 0 0 (by norm_num)).comp e₀.symm.toContinuousLinearMap)
  have hS₀ (v : smoothSections (n := m) (r := s₀) F₀) :
      S₀ (h₀.smoothToL2 ν v) = h₁.smoothToL2 ν (J v) := by
    rw [← h₀.sobolevZeroEquivL2_smooth (μ := ν) A₀ v]
    change e₁ (J₀.sobolevRealization A₀ A₁ 0 0 (by norm_num)
      (e₀.symm (e₀ (A₀.smoothToSobolev 0 v)))) = _
    rw [e₀.symm_apply_apply, J₀.sobolevRealization_smoothToSobolev]
    exact h₁.sobolevZeroEquivL2_smooth (μ := ν) A₁ (J v)
  let U₀ := externalTensorL2Equiv μ ν k h₀
  let U₁ := externalTensorL2Equiv μ ν k h₁
  let Sprod := U₁.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) S₀).completion.comp
      U₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let I := (g₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  have hI (v : smoothSections (n := n + m) (r := r * s₀) (externalTensorFiber E F₀)) :
      I (A.smoothToSobolev 1 v) = g₀.smoothToL2 (μ.prod ν) v := by
    change (g₀.sobolevZeroEquivL2 (μ := μ.prod ν) A)
      (A.sobolevInclusion 1 0 (by norm_num) (A.smoothToSobolev 1 v)) = _
    rw [A.sobolevInclusion_smoothToSobolev, g₀.sobolevZeroEquivL2_smooth]
  have hpure (u : smoothSections (n := n) (r := r) E)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      Sprod (g₀.smoothToL2 (μ.prod ν) (externalTensorSection E F₀ u v)) =
        g₁.smoothToL2 (μ.prod ν) (externalTensorSection E F₁ u (J v)) := by
    rw [← externalTensorL2Equiv_smooth μ ν k h₀ u v]
    change U₁ ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) S₀).completion
      (U₀.symm (U₀ _))) = _
    rw [U₀.symm_apply_apply]
    change U₁ ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) S₀).completion
      (↑(k.smoothToL2 μ u ⊗ₜ[ℂ] h₀.smoothToL2 ν v))) = _
    simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
      ContinuousLinearMap.id_apply, hS₀]
    exact externalTensorL2Equiv_smooth μ ν k h₁ u (J v)
  -- Sum the original compact-symbol pieces in the same presentations.
  choose T hT c hc happ using fun i ↦
    (L i).exists_rightExternalTensor_approximation μ ν (hL i) Q A D
  let W := (g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap
  have hE (v : smoothSections (n := n + m) (r := r * s₁) (externalTensorFiber E F₁)) :
      W (D.smoothToSobolev 0 v) = g₁.smoothToL2 (μ.prod ν) v :=
    g₁.sobolevZeroEquivL2_smooth (μ := μ.prod ν) D v
  let R := W.comp (∑ i, T i) + Sprod.comp I
  refine ⟨R, ?_, ‖W‖ * (∑ i, c i) + 1,
    add_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ ↦ hc i))) zero_le_one, ?_⟩
  · intro u v
    have hsum : (∑ i, externalTensorSection E F₁ u ((L i).toLinearMap v)) +
        externalTensorSection E F₁ u (J v) =
          externalTensorSection E F₁ u (((∑ i, (L i).toLinearMap) + J) v) := by
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_sum, Finset.sum_apply]
      change (∑ i, u.val x.1 ⊗ₜ[ℂ] ((L i).toLinearMap v).val x.2) +
        u.val x.1 ⊗ₜ[ℂ] (J v).val x.2 = _
      rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_add]
      congr 1
      simp only [LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
        Pi.add_apply, Submodule.coe_sum, Finset.sum_apply]
    change W ((∑ i, T i) (A.smoothToSobolev 1 (externalTensorSection E F₀ u v))) +
      Sprod (I (A.smoothToSobolev 1 (externalTensorSection E F₀ u v))) = _
    rw [hI, hpure]
    simp only [sum_apply, hT]
    rw [← map_sum, hE]
    change g₁.smoothToL2 (μ.prod ν)
        (∑ i, externalTensorSection E F₁ u ((L i).toLinearMap v)) +
      g₁.smoothToL2 (μ.prod ν) (externalTensorSection E F₁ u (J v)) = _
    rw [← map_add, hsum]
  · intro ε hε hε1
    choose P hPmap hPbound using fun i ↦ happ i ε hε hε1
    obtain ⟨Jε, hJε, Sε, hSε, herror⟩ :=
      exists_rightExternalTensorL2_smoothing_approximation (μ := μ) (ν := ν)
        h₀ h₁ k J S₀ hS₀ ε hε A
    let PJ : PseudodifferentialOperator (n := n + m) (r := r * s₀) (q := r * s₁)
        (externalTensorFiber E F₀) (externalTensorFiber E F₁) (μ.prod ν) 1 :=
      ⟨Jε, hJε.isPseudodifferentialOperator 1 Jε⟩
    let Pε := pseudodifferentialOperatorOfSpace ((∑ i, (P i).toSpace) + PJ.toSpace)
    have hPε : Pε.toLinearMap = (∑ i, (P i).toLinearMap) + Jε := by
      simp only [Pε, pseudodifferentialOperatorOfSpace, Submodule.coe_add, Submodule.coe_sum,
        PseudodifferentialOperator.toSpace, PJ]
    refine ⟨Pε, ?_, ?_⟩
    · have heq : Pε.toLinearMap - ∑ i, ∑ j,
          ((L i).rightProductCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
            (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap = Jε := by
        rw [hPε]
        simp only [hPmap, add_sub_cancel_left]
      rwa [heq]
    · have hreal : W.comp (Pε.sobolevRealization A D 1 0 (by norm_num)) =
          W.comp (∑ i, (P i).sobolevRealization A D 1 0 (by norm_num)) + Sε.comp I := by
        apply DFunLike.ext'
        apply (A.denseRange_smoothToSobolev 1).equalizer
          (W.comp (Pε.sobolevRealization A D 1 0 (by norm_num))).continuous
          (W.comp (∑ i, (P i).sobolevRealization A D 1 0 (by norm_num)) + Sε.comp I).continuous
        funext v
        change W (Pε.sobolevRealization A D 1 0 (by norm_num) (A.smoothToSobolev 1 v)) =
          W ((∑ i, (P i).sobolevRealization A D 1 0 (by norm_num)) (A.smoothToSobolev 1 v)) +
            Sε (I (A.smoothToSobolev 1 v))
        rw [Pε.sobolevRealization_smoothToSobolev, hI, hSε]
        simp only [sum_apply, PseudodifferentialOperator.sobolevRealization_smoothToSobolev]
        rw [← map_sum, hE, hE]
        change g₁.smoothToL2 (μ.prod ν) (Pε.toLinearMap v) =
          g₁.smoothToL2 (μ.prod ν) (∑ i, (P i).toLinearMap v) +
            g₁.smoothToL2 (μ.prod ν) (Jε v)
        simp only [hPε, LinearMap.add_apply, LinearMap.sum_apply, map_add]
      have hdiff : W.comp (Pε.sobolevRealization A D 1 0 (by norm_num)) - R =
          W.comp (∑ i, ((P i).sobolevRealization A D 1 0 (by norm_num) - T i)) +
            (Sε.comp I - Sprod.comp I) := by
        rw [hreal]
        apply ContinuousLinearMap.ext
        intro v
        simp only [R, ContinuousLinearMap.comp_apply, add_apply, sub_apply,
          sum_apply, map_sub, map_sum, Finset.sum_sub_distrib]
        abel
      have hfirst : ‖W.comp (∑ i, ((P i).sobolevRealization A D 1 0 (by norm_num) - T i))‖ ≤
          (‖W‖ * ∑ i, c i) * ε := by
        apply (W.opNorm_comp_le _).trans
        calc
          ‖W‖ * ‖∑ i, ((P i).sobolevRealization A D 1 0 (by norm_num) - T i)‖ ≤
              ‖W‖ * ∑ i, ‖(P i).sobolevRealization A D 1 0 (by norm_num) - T i‖ := by
            gcongr
            exact norm_sum_le _ _
          _ ≤ ‖W‖ * ∑ i, c i * ε := by
            gcongr with i
            exact hPbound i
          _ = _ := by rw [← Finset.sum_mul]; ring
      have hsecond : ‖Sε.comp I - Sprod.comp I‖ ≤ ε := by
        rw [norm_sub_rev]
        exact le_of_lt herror
      rw [hdiff]
      exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end AtiyahSinger
