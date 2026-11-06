/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Analysis.FinitePrincipalRepresentation
public import AtiyahSinger.Analysis.GradedBundleGlobalSymbol
public import AtiyahSinger.Analysis.HermitianMetricSymbol
public import AtiyahSinger.Analysis.QuantizationFrameTransport
public import AtiyahSinger.Analysis.RightTensorCutoffGlobalSymbol
public import AtiyahSinger.Analysis.TensorCutoffGlobalSymbol

/-!
# The exact graded product-cutoff principal symbol of the specified native PDO

Public module ID: M0710.

The four original finite local representations give one full principal
representative of the same native operator K. Its formula retains both patch
indices, both reverse-frame weights, both metric adjoints, the original
cotangent splitting and the upper-right minus sign. No averaging or choice
of an alternative operator occurs in this comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {ν : Measure N} [IsSmoothPositiveMeasure (n := m) ν]
  (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)

set_option maxHeartbeats 2500000 in
-- Reindex the actual four patch products, then compare their native graded symbol.
/-- The same graded cutoff PDO has the exact weighted full-factor principal symbol. -/
theorem exists_gradedProductCutoff_globalSymbol
    (C : QuantizationPresentation (n := n) (r := E₀.rank) (q := E₁.rank)
      E₀.Fiber E₁.Fiber)
    (D : QuantizationPresentation (n := m) (r := F₀.rank) (q := F₁.rank)
      F₀.Fiber F₁.Fiber)
    (p : globalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber 1)
    (q : globalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber 1)
    (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
    (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
    (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
    (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
    (ε : ℝ) (hε : 0 < ε) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let pa := h₀.symbolSpaceAdjoint h₁ p
    let qa := k₀.symbolSpaceAdjoint k₁ q
    let L₀₀ (z : Fin C.size × Fin D.inputEndomorphism.size) :=
      ((C.patch z.1).toPiece p).productCutoff ((C.patch z.1).hasCompactSupport_localSymbol p.val)
        (D.inputEndomorphism.patch z.2).chart
        (D.inputEndomorphism.patch z.2).chart_mem_atlas
        (D.inputEndomorphism.patch z.2).input
        (D.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
    let L₁₀ (z : Fin D.size × Fin C.inputEndomorphism.size) :=
      ((D.patch z.1).toPiece q).rightProductCutoff
        ((D.patch z.1).hasCompactSupport_localSymbol q.val)
        (C.inputEndomorphism.patch z.2).chart
        (C.inputEndomorphism.patch z.2).chart_mem_atlas
        (C.inputEndomorphism.patch z.2).input
        (C.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
    let L₀₁ (z : Fin D.reverseFrames.size × Fin C.reverseFrames.inputEndomorphism.size) :=
      ((D.reverseFrames.patch z.1).toPiece qa).rightProductCutoff
        ((D.reverseFrames.patch z.1).hasCompactSupport_localSymbol qa.val)
        (C.reverseFrames.inputEndomorphism.patch z.2).chart
        (C.reverseFrames.inputEndomorphism.patch z.2).chart_mem_atlas
        (C.reverseFrames.inputEndomorphism.patch z.2).input
        (C.reverseFrames.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
    let L₁₁ (z : Fin C.reverseFrames.size × Fin D.reverseFrames.inputEndomorphism.size) :=
      ((C.reverseFrames.patch z.1).toPiece pa).productCutoff
        ((C.reverseFrames.patch z.1).hasCompactSupport_localSymbol pa.val)
        (D.reverseFrames.inputEndomorphism.patch z.2).chart
        (D.reverseFrames.inputEndomorphism.patch z.2).chart_mem_atlas
        (D.reverseFrames.inputEndomorphism.patch z.2).input
        (D.reverseFrames.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
    ∀ (S T : SmoothFiniteComplexBundle (n := n + m) (M × N))
      (e : ∀ x : M × N, ((externalTensorFiber E₀.Fiber F₀.Fiber x) ×
        (externalTensorFiber E₁.Fiber F₁.Fiber x)) ≃ₗ[ℂ] S.Fiber x)
      (f : ∀ x : M × N, ((externalTensorFiber E₁.Fiber F₀.Fiber x) ×
        (externalTensorFiber E₀.Fiber F₁.Fiber x)) ≃ₗ[ℂ] T.Fiber x)
      (he₀ : IsSmoothBundleMap (n := n + m) (r := E₀.rank * F₀.rank) (q := S.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ
          (externalTensorFiber E₀.Fiber F₀.Fiber x)
          (externalTensorFiber E₁.Fiber F₁.Fiber x))))
      (he₁ : IsSmoothBundleMap (n := n + m) (r := E₁.rank * F₁.rank) (q := S.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ
          (externalTensorFiber E₀.Fiber F₀.Fiber x)
          (externalTensorFiber E₁.Fiber F₁.Fiber x))))
      (hf₀ : IsSmoothBundleMap (n := n + m) (r := E₁.rank * F₀.rank) (q := T.rank)
        (fun x ↦ (f x).toLinearMap.comp (LinearMap.inl ℂ
          (externalTensorFiber E₁.Fiber F₀.Fiber x)
          (externalTensorFiber E₀.Fiber F₁.Fiber x))))
      (hf₁ : IsSmoothBundleMap (n := n + m) (r := E₀.rank * F₁.rank) (q := T.rank)
        (fun x ↦ (f x).toLinearMap.comp (LinearMap.inr ℂ
          (externalTensorFiber E₁.Fiber F₀.Fiber x)
          (externalTensorFiber E₀.Fiber F₁.Fiber x))))
      (U : PseudodifferentialOperator (n := n + m) (r := E₀.rank * F₀.rank)
        (q := E₁.rank * F₀.rank) (externalTensorFiber E₀.Fiber F₀.Fiber)
        (externalTensorFiber E₁.Fiber F₀.Fiber) (μ.prod ν) 1)
      (V : PseudodifferentialOperator (n := n + m) (r := E₀.rank * F₀.rank)
        (q := E₀.rank * F₁.rank) (externalTensorFiber E₀.Fiber F₀.Fiber)
        (externalTensorFiber E₀.Fiber F₁.Fiber) (μ.prod ν) 1)
      (W : PseudodifferentialOperator (n := n + m) (r := E₁.rank * F₁.rank)
        (q := E₁.rank * F₀.rank) (externalTensorFiber E₁.Fiber F₁.Fiber)
        (externalTensorFiber E₁.Fiber F₀.Fiber) (μ.prod ν) 1)
      (Z : PseudodifferentialOperator (n := n + m) (r := E₁.rank * F₁.rank)
        (q := E₀.rank * F₁.rank) (externalTensorFiber E₁.Fiber F₁.Fiber)
        (externalTensorFiber E₀.Fiber F₁.Fiber) (μ.prod ν) 1)
      (K : PseudodifferentialOperator (n := n + m) (r := S.rank) (q := T.rank)
        S.Fiber T.Fiber (μ.prod ν) 1),
      (∀ u v, K.toLinearMap (smoothSectionSumEquiv e he₀ he₁ (u, v)) =
        smoothSectionSumEquiv f hf₀ hf₁
          (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v)) →
      IsSmoothingOperator (μ.prod ν) (U.toLinearMap - ∑ z, (L₀₀ z).toLinearMap) →
      IsSmoothingOperator (μ.prod ν) (V.toLinearMap - ∑ z, (L₁₀ z).toLinearMap) →
      IsSmoothingOperator (μ.prod ν) (W.toLinearMap - ∑ z, (L₀₁ z).toLinearMap) →
      IsSmoothingOperator (μ.prod ν) (Z.toLinearMap - ∑ z, (L₁₁ z).toLinearMap) →
      ∃ a : globalSymbolSpace (n := n + m) (r := S.rank) (q := T.rank) S.Fiber T.Fiber 1,
        K.principalSymbol = globalPrincipalSymbolClass S.Fiber T.Fiber 1 a ∧
        ∀ (x : M × N) (ξ : CotangentFiber (n := n + m) x) u v,
          let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
          let ξ₁ := (ξ.comp c.symm.toContinuousLinearMap).comp
            (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
          let ξ₂ := (ξ.comp c.symm.toContinuousLinearMap).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
          let α := ∑ i, ∑ j, (C.patch i).productCutoffWeight
            (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
          let β := ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight
            (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
          a.val x ξ (e x (u, v)) = f x (reciprocalTensorSymbol
            ((α : ℂ) • (p.val x.1 ξ₁).toLinearMap)
            ((α : ℂ) • (pa.val x.1 ξ₁).toLinearMap)
            ((β : ℂ) • (q.val x.2 ξ₂).toLinearMap)
            ((β : ℂ) • (qa.val x.2 ξ₂).toLinearMap) (u, v)) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorTopology (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorTopology (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorTopology (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorTopology (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let pa := h₀.symbolSpaceAdjoint h₁ p
  let qa := k₀.symbolSpaceAdjoint k₁ q
  let L₀₀ (z : Fin C.size × Fin D.inputEndomorphism.size) :=
    ((C.patch z.1).toPiece p).productCutoff ((C.patch z.1).hasCompactSupport_localSymbol p.val)
      (D.inputEndomorphism.patch z.2).chart
      (D.inputEndomorphism.patch z.2).chart_mem_atlas
      (D.inputEndomorphism.patch z.2).input
      (D.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
  let L₁₀ (z : Fin D.size × Fin C.inputEndomorphism.size) :=
    ((D.patch z.1).toPiece q).rightProductCutoff ((D.patch z.1).hasCompactSupport_localSymbol q.val)
      (C.inputEndomorphism.patch z.2).chart
      (C.inputEndomorphism.patch z.2).chart_mem_atlas
      (C.inputEndomorphism.patch z.2).input
      (C.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
  let L₀₁ (z : Fin D.reverseFrames.size × Fin C.reverseFrames.inputEndomorphism.size) :=
    ((D.reverseFrames.patch z.1).toPiece qa).rightProductCutoff
      ((D.reverseFrames.patch z.1).hasCompactSupport_localSymbol qa.val)
      (C.reverseFrames.inputEndomorphism.patch z.2).chart
      (C.reverseFrames.inputEndomorphism.patch z.2).chart_mem_atlas
      (C.reverseFrames.inputEndomorphism.patch z.2).input
      (C.reverseFrames.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
  let L₁₁ (z : Fin C.reverseFrames.size × Fin D.reverseFrames.inputEndomorphism.size) :=
    ((C.reverseFrames.patch z.1).toPiece pa).productCutoff
      ((C.reverseFrames.patch z.1).hasCompactSupport_localSymbol pa.val)
      (D.reverseFrames.inputEndomorphism.patch z.2).chart
      (D.reverseFrames.inputEndomorphism.patch z.2).chart_mem_atlas
      (D.reverseFrames.inputEndomorphism.patch z.2).input
      (D.reverseFrames.inputEndomorphism.patch z.2).sameFrameOutput rfl ε hε
  dsimp only
  intro S T e f he₀ he₁ hf₀ hf₁ U V W Z K hK hU hV hW hZ
  let A₀₀ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
    rank := E₀.rank * F₀.rank
    Fiber := externalTensorFiber E₀.Fiber F₀.Fiber }
  let A₁₁ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
    rank := E₁.rank * F₁.rank
    Fiber := externalTensorFiber E₁.Fiber F₁.Fiber }
  let B₁₀ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
    rank := E₁.rank * F₀.rank
    Fiber := externalTensorFiber E₁.Fiber F₀.Fiber }
  let B₀₁ : SmoothFiniteComplexBundle (n := n + m) (M × N) := {
    rank := E₀.rank * F₁.rank
    Fiber := externalTensorFiber E₀.Fiber F₁.Fiber }
  let A : Fin 2 → SmoothFiniteComplexBundle (n := n + m) (M × N) := ![A₀₀, A₁₁]
  let B : Fin 2 → SmoothFiniteComplexBundle (n := n + m) (M × N) := ![B₁₀, B₀₁]
  let s₀₀ := ∑ z, (L₀₀ z).globalSymbol
  let s₁₀ := ∑ z, (L₁₀ z).globalSymbol
  let s₀₁ := ∑ z, (L₀₁ z).globalSymbol
  let s₁₁ := ∑ z, (L₁₁ z).globalSymbol
  obtain ⟨a, ha, hclass⟩ := exists_globalSymbol_of_gradedBundlePseudodifferentialOperator
    S T A B e f he₀ he₁ hf₀ hf₁ U V W Z K hK s₀₀ s₁₀ s₀₁ s₁₁
    (U.principalSymbol_eq_of_finite_representation L₀₀ hU)
    (V.principalSymbol_eq_of_finite_representation L₁₀ hV)
    (W.principalSymbol_eq_of_finite_representation L₀₁ hW)
    (Z.principalSymbol_eq_of_finite_representation L₁₁ hZ)
  refine ⟨a, hclass, ?_⟩
  intro x ξ u v
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let ξ₁ := (ξ.comp c.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp c.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let α := ∑ i, ∑ j, (C.patch i).productCutoffWeight
    (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
  let β := ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight
    (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
  have hL₀₀ : s₀₀.val = ∑ i, ∑ j, (L₀₀ (i, j)).globalSymbolFunction := by
    simp only [s₀₀, Submodule.coe_sum, Fintype.sum_prod_type]
    rfl
  have hs₀₀ : (s₀₀.val x ξ).toLinearMap = TensorProduct.map
      ((α : ℂ) • (p.val x.1 ξ₁).toLinearMap)
      (LinearMap.id : F₀.Fiber x.2 →ₗ[ℂ] F₀.Fiber x.2) := by
    apply TensorProduct.ext
    ext u v
    change s₀₀.val x ξ (u ⊗ₜ[ℂ] v) =
      TensorProduct.map ((α : ℂ) • (p.val x.1 ξ₁).toLinearMap)
        (LinearMap.id : F₀.Fiber x.2 →ₗ[ℂ] F₀.Fiber x.2)
        (u ⊗ₜ[ℂ] v)
    rw [hL₀₀]
    rw [C.globalSymbolFunction_sum_productCutoff D.inputEndomorphism p ε hε x.1 x.2 ξ u v]
    simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_apply,
      TensorProduct.smul_tmul']
    rfl
  have hL₁₀ : s₁₀.val = ∑ i, ∑ j, (L₁₀ (i, j)).globalSymbolFunction := by
    simp only [s₁₀, Submodule.coe_sum, Fintype.sum_prod_type]
    rfl
  have hs₁₀ : (s₁₀.val x ξ).toLinearMap = TensorProduct.map
      (LinearMap.id : E₀.Fiber x.1 →ₗ[ℂ] E₀.Fiber x.1)
      ((β : ℂ) • (q.val x.2 ξ₂).toLinearMap) := by
    apply TensorProduct.ext
    ext u v
    change s₁₀.val x ξ (u ⊗ₜ[ℂ] v) =
      TensorProduct.map
        (LinearMap.id : E₀.Fiber x.1 →ₗ[ℂ] E₀.Fiber x.1)
        ((β : ℂ) • (q.val x.2 ξ₂).toLinearMap)
        (u ⊗ₜ[ℂ] v)
    rw [hL₁₀]
    rw [D.globalSymbolFunction_sum_rightProductCutoff C.inputEndomorphism q ε hε x.2 x.1 ξ v u]
    simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_apply,
      TensorProduct.tmul_smul]
    rfl
  have hL₀₁ : s₀₁.val = ∑ i, ∑ j, (L₀₁ (i, j)).globalSymbolFunction := by
    simp only [s₀₁, Submodule.coe_sum, Fintype.sum_prod_type]
    rfl
  have hs₀₁ : (s₀₁.val x ξ).toLinearMap = TensorProduct.map
      (LinearMap.id : E₁.Fiber x.1 →ₗ[ℂ] E₁.Fiber x.1)
      ((β : ℂ) • (qa.val x.2 ξ₂).toLinearMap) := by
    apply TensorProduct.ext
    ext u v
    change s₀₁.val x ξ (u ⊗ₜ[ℂ] v) =
      TensorProduct.map
        (LinearMap.id : E₁.Fiber x.1 →ₗ[ℂ] E₁.Fiber x.1)
        ((β : ℂ) • (qa.val x.2 ξ₂).toLinearMap)
        (u ⊗ₜ[ℂ] v)
    rw [hL₀₁]
    rw [D.reverseFrames.globalSymbolFunction_sum_rightProductCutoff
      C.reverseFrames.inputEndomorphism qa ε hε x.2 x.1 ξ v u]
    simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_apply,
      TensorProduct.tmul_smul]
    rfl
  have hL₁₁ : s₁₁.val = ∑ i, ∑ j, (L₁₁ (i, j)).globalSymbolFunction := by
    simp only [s₁₁, Submodule.coe_sum, Fintype.sum_prod_type]
    rfl
  have hs₁₁ : (s₁₁.val x ξ).toLinearMap = TensorProduct.map
      ((α : ℂ) • (pa.val x.1 ξ₁).toLinearMap)
      (LinearMap.id : F₁.Fiber x.2 →ₗ[ℂ] F₁.Fiber x.2) := by
    apply TensorProduct.ext
    ext u v
    change s₁₁.val x ξ (u ⊗ₜ[ℂ] v) =
      TensorProduct.map ((α : ℂ) • (pa.val x.1 ξ₁).toLinearMap)
        (LinearMap.id : F₁.Fiber x.2 →ₗ[ℂ] F₁.Fiber x.2)
        (u ⊗ₜ[ℂ] v)
    rw [hL₁₁]
    rw [C.reverseFrames.globalSymbolFunction_sum_productCutoff
      D.reverseFrames.inputEndomorphism pa ε hε x.1 x.2 ξ u v]
    simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_apply,
      TensorProduct.smul_tmul']
    rfl
  -- The reverse frames have the same chart and scalar cutoffs, hence the paired coefficients.
  refine (ha x ξ u v).trans ?_
  apply congrArg (f x)
  change (s₀₀.val x ξ u - s₀₁.val x ξ v, s₁₀.val x ξ u + s₁₁.val x ξ v) = _
  change ((s₀₀.val x ξ).toLinearMap u - (s₀₁.val x ξ).toLinearMap v,
    (s₁₀.val x ξ).toLinearMap u + (s₁₁.val x ξ).toLinearMap v) = _
  rw [hs₀₀, hs₁₀, hs₀₁, hs₁₁]
  rfl

end AtiyahSinger
