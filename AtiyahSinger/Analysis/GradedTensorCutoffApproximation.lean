/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricTensorDomain
public import AtiyahSinger.Analysis.GradedBlockOperator
public import AtiyahSinger.Analysis.QuantizationFrameTransport
public import AtiyahSinger.Analysis.RightTensorSymbolQuantizationApproximation
public import AtiyahSinger.Analysis.TensorSymbolQuantizationApproximation

/-!
# Simultaneous canonical cutoffs of the original graded product

Public module ID: M0711.

The four actual product PDO blocks use canonical pieces of the same two
symbols and their metric adjoints, with paired frames and a common epsilon.
Their ℓ² direct-sum matrix converges to the specified geometric H1
extension, with its original signs and Sobolev/metric witnesses. Each block
retains its exact cutoff sum modulo a genuine smoothing operator.

Source: the finite-atlas product construction in SG III.13.5, pp.249--250.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {n m r₀ r₁ s₀ s₁ : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hTM : T2Space M] [hTN : T2Space N]
  [hSCM : SecondCountableTopology M] [hSCN : SecondCountableTopology N]
  [hCM : CompactSpace M] [hCN : CompactSpace N]
  [MeasurableSpace M] [hBM : BorelSpace M]
  [MeasurableSpace N] [hBN : BorelSpace N]
  {μ : Measure M} {ν : Measure N}
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := m) ν]
  {E₀ : M → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [hE₀ : IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  {E₁ : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [hE₁ : IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  {F₀ : N → Type*}
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, NormedSpace ℂ (F₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [hF₀ : IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  {F₁ : N → Type*}
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [hF₁ : IsSmoothComplexBundle (n := m) (r := s₁) F₁]

include hM hN hTM hTN hSCM hSCN hCM hCN hBM hBN hμ hν hE₀ hE₁ hF₀ hF₁

variable (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
  (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
  (k₀ : SmoothHermitianMetric (n := m) (r := s₀) F₀)
  (k₁ : SmoothHermitianMetric (n := m) (r := s₁) F₁)
  (P : PseudodifferentialOperator (n := n) (r := r₀) (q := r₁) E₀ E₁ μ 1)
  (Q : PseudodifferentialOperator (n := m) (r := s₀) (q := s₁) F₀ F₁ ν 1)

set_option maxHeartbeats 2000000 in
-- The extended limit accommodates the canonical product blocks and original graded H1 extension.
/-- Canonical product cutoff PDO blocks converge to the actual graded H1 extension. -/
theorem exists_gradedProductH1_cutoff_approximation
    (p : globalSymbolSpace (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (q : globalSymbolSpace (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E₀ E₁ 1 p)
    (hq : Q.principalSymbol = globalPrincipalSymbolClass F₀ F₁ 1 q)
    (C : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (D : QuantizationPresentation (n := m) (r := s₀) (q := s₁) F₀ F₁) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorTopology (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorTopology (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorTopology (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorTopology (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    let pa := h₀.symbolSpaceAdjoint h₁ p
    let qa := k₀.symbolSpaceAdjoint k₁ q
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
        (externalTensorFiber E₀ F₀))
      (B : SmoothBundlePresentation (n := n + m) (r := r₁ * s₁)
        (externalTensorFiber E₁ F₁))
      (H : SmoothBundlePresentation (n := n + m) (r := r₁ * s₀)
        (externalTensorFiber E₁ F₀))
      (J : SmoothBundlePresentation (n := n + m) (r := r₀ * s₁)
        (externalTensorFiber E₀ F₁)),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
        ∃ (U : PseudodifferentialOperator (n := n + m) (r := r₀ * s₀) (q := r₁ * s₀)
            (externalTensorFiber E₀ F₀) (externalTensorFiber E₁ F₀) (μ.prod ν) 1)
          (V : PseudodifferentialOperator (n := n + m) (r := r₀ * s₀) (q := r₀ * s₁)
            (externalTensorFiber E₀ F₀) (externalTensorFiber E₀ F₁) (μ.prod ν) 1)
          (W : PseudodifferentialOperator (n := n + m) (r := r₁ * s₁) (q := r₁ * s₀)
            (externalTensorFiber E₁ F₁) (externalTensorFiber E₁ F₀) (μ.prod ν) 1)
          (Z : PseudodifferentialOperator (n := n + m) (r := r₁ * s₁) (q := r₀ * s₁)
            (externalTensorFiber E₁ F₁) (externalTensorFiber E₀ F₁) (μ.prod ν) 1),
          IsSmoothingOperator (μ.prod ν) (U.toLinearMap - ∑ i, ∑ j,
            (((C.patch i).toPiece p).productCutoff ((C.patch i).hasCompactSupport_localSymbol p.val)
              (D.inputEndomorphism.patch j).chart (D.inputEndomorphism.patch j).chart_mem_atlas
              (D.inputEndomorphism.patch j).input (D.inputEndomorphism.patch j).sameFrameOutput
              rfl ε hε).toLinearMap) ∧
          IsSmoothingOperator (μ.prod ν) (V.toLinearMap - ∑ i, ∑ j,
            (((D.patch i).toPiece q).rightProductCutoff
              ((D.patch i).hasCompactSupport_localSymbol q.val)
              (C.inputEndomorphism.patch j).chart (C.inputEndomorphism.patch j).chart_mem_atlas
              (C.inputEndomorphism.patch j).input (C.inputEndomorphism.patch j).sameFrameOutput
              rfl ε hε).toLinearMap) ∧
          IsSmoothingOperator (μ.prod ν) (W.toLinearMap - ∑ i, ∑ j,
            (((D.reverseFrames.patch i).toPiece qa).rightProductCutoff
              ((D.reverseFrames.patch i).hasCompactSupport_localSymbol qa.val)
              (C.reverseFrames.inputEndomorphism.patch j).chart
              (C.reverseFrames.inputEndomorphism.patch j).chart_mem_atlas
              (C.reverseFrames.inputEndomorphism.patch j).input
              (C.reverseFrames.inputEndomorphism.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
          IsSmoothingOperator (μ.prod ν) (Z.toLinearMap - ∑ i, ∑ j,
            (((C.reverseFrames.patch i).toPiece pa).productCutoff
              ((C.reverseFrames.patch i).hasCompactSupport_localSymbol pa.val)
              (D.reverseFrames.inputEndomorphism.patch j).chart
              (D.reverseFrames.inputEndomorphism.patch j).chart_mem_atlas
              (D.reverseFrames.inputEndomorphism.patch j).input
              (D.reverseFrames.inputEndomorphism.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
          let o₀ := (g₁₀.sobolevZeroEquivL2 (μ := μ.prod ν) H).toContinuousLinearMap
          let o₁ := (g₀₁.sobolevZeroEquivL2 (μ := μ.prod ν) J).toContinuousLinearMap
          ‖gradedBlockOperator
            (o₀.comp (U.sobolevRealization A H 1 0 (by norm_num)))
            (o₁.comp (V.sobolevRealization A J 1 0 (by norm_num)))
            (o₀.comp (W.sobolevRealization B H 1 0 (by norm_num)))
            (o₁.comp (Z.sobolevRealization B J 1 0 (by norm_num))) -
              gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberNormedSpace (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorTopology (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorFiberNormedSpace (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorTopology (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₁) E₁ F₁
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorFiberNormedSpace (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorTopology (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s₀) E₁ F₀
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorFiberNormedSpace (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorTopology (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₁) E₀ F₁
  dsimp only
  intro A B H J
  let g₁₀ := externalTensorMetric h₁ k₀
  let g₀₁ := externalTensorMetric h₀ k₁
  let pa := h₀.symbolSpaceAdjoint h₁ p
  let qa := k₀.symbolSpaceAdjoint k₁ q
  have hpa : (P.metricFormalAdjoint h₀ h₁).principalSymbol =
      globalPrincipalSymbolClass E₁ E₀ 1 pa := by
    rw [P.principalSymbol_metricFormalAdjoint, hp, h₀.principalSymbolAdjoint_class]
  have hqa : (Q.metricFormalAdjoint k₀ k₁).principalSymbol =
      globalPrincipalSymbolClass F₁ F₀ 1 qa := by
    rw [Q.principalSymbol_metricFormalAdjoint, hq, k₀.principalSymbolAdjoint_class]
  -- All four canonical constructions use the original paired scalar cutoffs.
  obtain ⟨U, hU, cU, hcU, appU⟩ := P.exists_externalTensor_symbol_approximation
    μ ν h₀ h₁ k₀ p hp C D.inputEndomorphism A H
  obtain ⟨V, hV, cV, hcV, appV⟩ := Q.exists_rightExternalTensor_symbol_approximation
    μ ν k₀ k₁ h₀ q hq D C.inputEndomorphism A J
  obtain ⟨W, hW, cW, hcW, appW⟩ :=
    (Q.metricFormalAdjoint k₀ k₁).exists_rightExternalTensor_symbol_approximation
      μ ν k₁ k₀ h₁ qa hqa D.reverseFrames C.reverseFrames.inputEndomorphism B H
  obtain ⟨Z, hZ, cZ, hcZ, appZ⟩ :=
    (P.metricFormalAdjoint h₀ h₁).exists_externalTensor_symbol_approximation
      μ ν h₁ h₀ k₁ pa hpa C.reverseFrames D.reverseFrames.inputEndomorphism B J
  let T := gradedBlockOperator U V W Z
  -- Uniqueness on the same two pure smooth tensor families identifies the original extension.
  have hT : T = gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B := by
    have hspec := (existsUnique_gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B)
    apply hspec.unique ?_ hspec.exists.choose_spec
    constructor
    · intro u v
      change WithLp.toLp 2
        (U (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) + -(W 0),
          V (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) + Z 0) = _
      simp only [map_zero, neg_zero, add_zero, hU, hV]
    · intro u v
      change WithLp.toLp 2
        (U 0 + -(W (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))),
          V 0 + Z (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) = _
      simp only [map_zero, zero_add, hW, hZ]
  let I := (WithLp.prodContinuousLinearEquiv 2 ℂ (A.SobolevSpace 1)
    (B.SobolevSpace 1)).toContinuousLinearMap
  let O := (WithLp.prodContinuousLinearEquiv 2 ℂ (g₁₀.L2SectionSpace (μ.prod ν))
    (g₀₁.L2SectionSpace (μ.prod ν))).symm.toContinuousLinearMap
  refine ⟨‖O‖ * (cU + cV + cW + cZ) * ‖I‖, by positivity, ?_⟩
  intro ε hε hε₁
  obtain ⟨Uε, hUs, hUε⟩ := appU ε hε hε₁
  obtain ⟨Vε, hVs, hVε⟩ := appV ε hε hε₁
  obtain ⟨Wε, hWs, hWε⟩ := appW ε hε hε₁
  obtain ⟨Zε, hZs, hZε⟩ := appZ ε hε hε₁
  refine ⟨Uε, Vε, Wε, Zε, hUs, hVs, hWs, hZs, ?_⟩
  let o₀ := (g₁₀.sobolevZeroEquivL2 (μ := μ.prod ν) H).toContinuousLinearMap
  let o₁ := (g₀₁.sobolevZeroEquivL2 (μ := μ.prod ν) J).toContinuousLinearMap
  let U' := o₀.comp (Uε.sobolevRealization A H 1 0 (by norm_num))
  let V' := o₁.comp (Vε.sobolevRealization A J 1 0 (by norm_num))
  let W' := o₀.comp (Wε.sobolevRealization B H 1 0 (by norm_num))
  let Z' := o₁.comp (Zε.sobolevRealization B J 1 0 (by norm_num))
  change ‖gradedBlockOperator U' V' W' Z' - gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B‖ ≤ _
  have hdiff : gradedBlockOperator U' V' W' Z' - T =
      gradedBlockOperator (U' - U) (V' - V) (W' - W) (Z' - Z) := by
    apply ContinuousLinearMap.ext
    intro z
    apply WithLp.ofLp_injective
    change (U' (WithLp.ofLp z).1 + -(W' (WithLp.ofLp z).2),
      V' (WithLp.ofLp z).1 + Z' (WithLp.ofLp z).2) -
      (U (WithLp.ofLp z).1 + -(W (WithLp.ofLp z).2),
      V (WithLp.ofLp z).1 + Z (WithLp.ofLp z).2) =
      ((U' (WithLp.ofLp z).1 - U (WithLp.ofLp z).1) +
        -(W' (WithLp.ofLp z).2 - W (WithLp.ofLp z).2),
      (V' (WithLp.ofLp z).1 - V (WithLp.ofLp z).1) +
        (Z' (WithLp.ofLp z).2 - Z (WithLp.ofLp z).2))
    apply Prod.ext <;> dsimp only [Prod.fst_sub, Prod.snd_sub] <;> abel
  rw [← hT, hdiff]
  -- The same epsilon controls every block before the fixed ℓ²-sum norm comparison.
  calc
    _ ≤ ‖O‖ * (‖U' - U‖ + ‖V' - V‖ + ‖W' - W‖ + ‖Z' - Z‖) * ‖I‖ :=
      norm_gradedBlockOperator_le _ _ _ _
    _ ≤ ‖O‖ * (cU * ε + cV * ε + cW * ε + cZ * ε) * ‖I‖ := by
      gcongr
    _ = (‖O‖ * (cU + cV + cW + cZ) * ‖I‖) * ε := by ring

end AtiyahSinger
