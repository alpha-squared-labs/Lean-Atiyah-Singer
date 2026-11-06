/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricProductPieceApproximation

/-!
# Finite geometric tensor approximation

Public module ID: M0663.

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

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := m) (r := s) F]

variable [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]

/-- The same input frame with the original output plateau of an endomorphism patch. -/
def QuantizationPatch.sameFrameOutput
    (Q : QuantizationPatch (n := m) (r := s) (q := s) F F) :
    BundleChartCutoff (r := s) F Q.chart where
  frame := Q.input.frame
  frame_mem_atlas := Q.input.frame_mem_atlas
  cutoff := Q.output.cutoff
  smooth_cutoff := Q.output.smooth_cutoff
  compact_support := Q.output.compact_support
  support_subset _z hz := ⟨(Q.output.support_subset hz).1, Q.output_support_in_input_frame hz⟩

set_option maxHeartbeats 1600000 in
-- Each member of the original finite partition uses the same geometric Sobolev spaces.
/-- A fixed finite second-factor partition assembles genuine tensor PDO approximants to
one original compact-symbol piece, retaining the exact finite sum of section actions. -/
theorem PseudodifferentialPiece.exists_externalTensor_approximation
    (L : PseudodifferentialPiece (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (hLK : HasCompactSupport L.symbol)
    (Q : QuantizationPresentation (n := m) (r := s) (q := s) F F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
    letI := externalTensorTopology (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
    letI := externalTensorTopology (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F))
      (D : SmoothBundlePresentation (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] D.SobolevSpace 0,
        (∀ (u : smoothSections (n := n) (r := r₀) E₀)
          (v : smoothSections (n := m) (r := s) F),
          T (A.smoothToSobolev 1 (externalTensorSection E₀ F u v)) =
            D.smoothToSobolev 0 (externalTensorSection E₁ F (L.toLinearMap u) v)) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
              (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1,
            P.toLinearMap = ∑ j, (L.productCutoff hLK (Q.patch j).chart
              (Q.patch j).chart_mem_atlas (Q.patch j).input
                (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap ∧
            ‖P.sobolevRealization A D 1 0 (by norm_num) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
  let := externalTensorTopology (r := r₀) (s := s) E₀ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
  let := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
  let := externalTensorTopology (r := r₁) (s := s) E₁ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  intro A D
  have hpieces (j : Fin Q.size) := L.exists_productCutoff_approximation μ ν hLK
    (Q.patch j).chart (Q.patch j).chart_mem_atlas (Q.patch j).input
    (Q.patch j).sameFrameOutput rfl A D
  choose T hT c hc happ using hpieces
  let V (j : Fin Q.size) (v : smoothSections (n := m) (r := s) F) :=
    (Q.patch j).sameFrameOutput.extend (Q.patch j).chart_mem_atlas
      (SchwartzMap.smulLeftCLM _ (Q.patch j).output.cutoff
        ((Q.patch j).input.localize (Q.patch j).chart_mem_atlas v))
  have hV (j : Fin Q.size) (v : smoothSections (n := m) (r := s) F) (x : N) :
      (V j v).val x = ((Q.patch j).weight x : ℂ) • v.val x := by
    let q := Q.patch j
    let := q.input.frame_mem_atlas
    have hm (y : EuclideanSpace ℝ (Fin m)) :
        SchwartzMap.smulLeftCLM _ q.output.cutoff
            (q.input.localize q.chart_mem_atlas v) y =
          q.output.cutoff y • q.input.localize q.chart_mem_atlas v y :=
      SchwartzMap.smulLeftCLM_apply_apply
        (q.output.compact_support.hasTemperateGrowth q.output.smooth_cutoff) _ y
    change q.sameFrameOutput.extendedFunction
      (SchwartzMap.smulLeftCLM _ q.output.cutoff
        (q.input.localize q.chart_mem_atlas v)) x = (q.weight x : ℂ) • v.val x
    by_cases hx : x ∈ q.chart.source
    · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx, hm,
        QuantizationPatch.sameFrameOutput]
      change (q.output.cutoff (q.chart x) : ℂ) • q.input.frame.symmL ℂ x
        (q.output.cutoff (q.chart x) • q.input.localizedFunction v (q.chart x)) = _
      have hlocal : q.input.localizedFunction v (q.chart x) =
          (q.input.cutoff (q.chart x) : ℂ) • (q.input.frame ⟨x, v.val x⟩).2 := by
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
          ((q.input.frame.linearEquivAt ℂ x hf) (v.val x)) = _
      rw [LinearEquiv.symm_apply_apply]
      simp only [QuantizationPatch.weight, ite_eq_left hx]
    · simp only [BundleChartCutoff.extendedFunction, ite_eq_right hx]
      simp only [QuantizationPatch.weight, ite_eq_right hx, Complex.ofReal_zero, zero_smul]
  refine ⟨∑ j, T j, ?_, ∑ j, c j, Finset.sum_nonneg (fun j _ ↦ hc j), ?_⟩
  · intro u v
    -- The same original partition reconstructs the second section exactly.
    have hsum : (∑ j, externalTensorSection E₁ F (L.toLinearMap u) (V j v)) =
        externalTensorSection E₁ F (L.toLinearMap u) v := by
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_sum, Finset.sum_apply]
      change (∑ j, (L.toLinearMap u).val x.1 ⊗ₜ[ℂ] (V j v).val x.2) =
        (L.toLinearMap u).val x.1 ⊗ₜ[ℂ] v.val x.2
      simp_rw [hV, TensorProduct.tmul_smul]
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, Q.sum_weight, Complex.ofReal_one, one_smul]
    simp only [sum_apply, hT]
    change (∑ j, D.smoothToSobolev 0 (externalTensorSection E₁ F (L.toLinearMap u) (V j v))) = _
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
        funext u
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
