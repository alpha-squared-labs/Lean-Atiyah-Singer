/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricRightProductPieceApproximation
public import AtiyahSinger.Analysis.GeometricTensorFiniteApproximation

/-!
# Finite geometric tensor approximation

Public module ID: M0661.

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

set_option maxHeartbeats 1600000 in
-- Each member of the original finite partition uses the same geometric Sobolev spaces.
/-- A fixed finite first-factor partition assembles genuine tensor PDO approximants to
one original compact-symbol piece, retaining the exact finite sum of section actions. -/
theorem PseudodifferentialPiece.exists_rightExternalTensor_approximation
    (L : PseudodifferentialPiece (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (hLK : HasCompactSupport L.symbol)
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
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r * s₀) (externalTensorFiber E F₀))
      (D : SmoothBundlePresentation (n := n + m) (r := r * s₁) (externalTensorFiber E F₁)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] D.SobolevSpace 0,
        (∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := m) (r := s₀) F₀),
          T (A.smoothToSobolev 1 (externalTensorSection E F₀ u v)) =
            D.smoothToSobolev 0 (externalTensorSection E F₁ u (L.toLinearMap v))) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r * s₀) (q := r * s₁)
              (externalTensorFiber E F₀) (externalTensorFiber E F₁) (μ.prod ν) 1,
            P.toLinearMap = ∑ j, (L.rightProductCutoff hLK (Q.patch j).chart
              (Q.patch j).chart_mem_atlas (Q.patch j).input
                (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap ∧
            ‖P.sobolevRealization A D 1 0 (by norm_num) - T‖ ≤ c * ε := by
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
  intro A D
  have hpieces (j : Fin Q.size) := L.exists_rightProductCutoff_approximation μ ν hLK
    (Q.patch j).chart (Q.patch j).chart_mem_atlas (Q.patch j).input
    (Q.patch j).sameFrameOutput rfl A D
  choose T hT c hc happ using hpieces
  let V (j : Fin Q.size) (u : smoothSections (n := n) (r := r) E) :=
    (Q.patch j).sameFrameOutput.extend (Q.patch j).chart_mem_atlas
      (SchwartzMap.smulLeftCLM _ (Q.patch j).output.cutoff
        ((Q.patch j).input.localize (Q.patch j).chart_mem_atlas u))
  have hV (j : Fin Q.size) (u : smoothSections (n := n) (r := r) E) (x : M) :
      (V j u).val x = ((Q.patch j).weight x : ℂ) • u.val x := by
    let q := Q.patch j
    let := q.input.frame_mem_atlas
    have hm (y : EuclideanSpace ℝ (Fin n)) :
        SchwartzMap.smulLeftCLM _ q.output.cutoff
            (q.input.localize q.chart_mem_atlas u) y =
          q.output.cutoff y • q.input.localize q.chart_mem_atlas u y :=
      SchwartzMap.smulLeftCLM_apply_apply
        (q.output.compact_support.hasTemperateGrowth q.output.smooth_cutoff) _ y
    change q.sameFrameOutput.extendedFunction
      (SchwartzMap.smulLeftCLM _ q.output.cutoff
        (q.input.localize q.chart_mem_atlas u)) x = (q.weight x : ℂ) • u.val x
    by_cases hx : x ∈ q.chart.source
    · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx, hm,
        QuantizationPatch.sameFrameOutput]
      change (q.output.cutoff (q.chart x) : ℂ) • q.input.frame.symmL ℂ x
        (q.output.cutoff (q.chart x) • q.input.localizedFunction u (q.chart x)) = _
      have hlocal : q.input.localizedFunction u (q.chart x) =
          (q.input.cutoff (q.chart x) : ℂ) • (q.input.frame ⟨x, u.val x⟩).2 := by
        simp only [BundleChartCutoff.localizedFunction, ite_eq_left (q.chart.map_source hx),
          sectionInChart]
        rw [q.chart.left_inv hx]
      rw [hlocal]
      by_cases hw : q.input.cutoff (q.chart x) = 0
      · simp [QuantizationPatch.weight, hx, hw]
      have hf : x ∈ q.input.frame.baseSet := by
        simpa only [Set.mem_preimage, q.chart.left_inv hx] using
          (q.input.support_subset (subset_tsupport _ hw)).2
      have ho := q.output_eq_one (q.chart x) (subset_tsupport _ hw)
      rw [ho, Complex.ofReal_one, one_smul, one_smul, map_smul,
        q.input.frame.symmL_apply hf]
      change (q.input.cutoff (q.chart x) : ℂ) •
        (q.input.frame.linearEquivAt ℂ x hf).symm
          ((q.input.frame.linearEquivAt ℂ x hf) (u.val x)) = _
      rw [LinearEquiv.symm_apply_apply]
      simp only [QuantizationPatch.weight, ite_eq_left hx]
    · simp only [BundleChartCutoff.extendedFunction, ite_eq_right hx]
      simp only [QuantizationPatch.weight, ite_eq_right hx, Complex.ofReal_zero, zero_smul]
  refine ⟨∑ j, T j, ?_, ∑ j, c j, Finset.sum_nonneg (fun j _ ↦ hc j), ?_⟩
  · intro u v
    -- The same original partition reconstructs the first section exactly.
    have hsum : (∑ j, externalTensorSection E F₁ (V j u) (L.toLinearMap v)) =
        externalTensorSection E F₁ u (L.toLinearMap v) := by
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_sum, Finset.sum_apply]
      change (∑ j, (V j u).val x.1 ⊗ₜ[ℂ] (L.toLinearMap v).val x.2) =
        u.val x.1 ⊗ₜ[ℂ] (L.toLinearMap v).val x.2
      simp_rw [hV, ← TensorProduct.smul_tmul']
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, Q.sum_weight, Complex.ofReal_one, one_smul]
    simp only [sum_apply, hT]
    change (∑ j, D.smoothToSobolev 0 (externalTensorSection E F₁ (V j u) (L.toLinearMap v))) = _
    rw [← map_sum, hsum]
  · intro ε hε hε1
    choose P hPmap hPbound using fun j ↦ happ j ε hε hε1
    let R := pseudodifferentialOperatorOfSpace (∑ j, (P j).toSpace)
    have hR : R.toLinearMap = ∑ j, (P j).toLinearMap := by
      simp only [R, pseudodifferentialOperatorOfSpace, Submodule.coe_sum,
        PseudodifferentialOperator.toSpace]
    refine ⟨R, ?_, ?_⟩
    · rw [hR]
      exact Finset.sum_congr rfl (fun j _ ↦ hPmap j)
    · have heq : R.sobolevRealization A D 1 0 (by norm_num) =
          ∑ j, (P j).sobolevRealization A D 1 0 (by norm_num) := by
        apply DFunLike.ext'
        apply (A.denseRange_smoothToSobolev 1).equalizer
          (R.sobolevRealization A D 1 0 (by norm_num)).continuous
          (∑ j, (P j).sobolevRealization A D 1 0 (by norm_num)).continuous
        funext v
        simp only [Function.comp_apply, sum_apply,
          PseudodifferentialOperator.sobolevRealization_smoothToSobolev, hR,
          LinearMap.sum_apply, map_sum]
      rw [heq, ← Finset.sum_sub_distrib]
      calc
        ‖∑ j, ((P j).sobolevRealization A D 1 0 (by norm_num) - T j)‖ ≤
            ∑ j, ‖(P j).sobolevRealization A D 1 0 (by norm_num) - T j‖ := norm_sum_le _ _
        _ ≤ ∑ j, c j * ε := Finset.sum_le_sum (fun j _ ↦ hPbound j)
        _ = (∑ j, c j) * ε := (Finset.sum_mul _ _ _).symm

end AtiyahSinger
