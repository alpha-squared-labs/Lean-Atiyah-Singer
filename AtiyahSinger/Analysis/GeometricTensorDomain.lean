/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.LinearPMapGraph
public import AtiyahSinger.Analysis.ClosedMetricL2Realization
public import AtiyahSinger.Analysis.ExternalTensorH1Elliptic
public import AtiyahSinger.Analysis.ExternalTensorH1Mixed
public import AtiyahSinger.Analysis.ExternalTensorL2
public import AtiyahSinger.Analysis.GradedTensorSmoothCore
public import AtiyahSinger.Analysis.HilbertTensorDomain

/-!
# The geometric H1 domain of the elliptic graded product

Public module ID: M0662.

Transport the closed tensor matrix into the exterior-bundle integral L2 spaces
and identify its exact graph with geometric H1. The bounded H1 extension is
specified on the two pure smooth tensor families. No assertion that a factorwise
PDO is an ordinary isotropic product PDO is used.

Sources: SG III.13.5 (13.12)--(13.14), pp.249--250; III.2.14--2.15 and
III.5.2--5.3 for Sobolev estimates. Product-H1 graph comparison is the explicit
functional-analytic supplement. This module concerns the selected first-order
native elliptic representatives; arbitrary K classes are treated piecewise in
the existing finite clopen reduction, and equivariant descent is separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory UniformSpace
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

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

/-- The original closed graded tensor matrix in the actual exterior-bundle L2 spaces. -/
def gradedProductL2Operator :
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
    let g₀₀ := externalTensorMetric h₀ k₀
    let g₁₁ := externalTensorMetric h₁ k₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν)) →ₗ.[ℂ]
      WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν)) := by
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
  let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₁ k₁)
  let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₀ k₁)
  let P₀ := P.metricL2ClosedRealization h₀ h₁
  let Q₀ := Q.metricL2ClosedRealization k₀ k₁
  let D := gradedTensorOperator P₀ Q₀
  let dom := D.domain.comap Ueven.symm.toLinearMap
  exact {
    domain := dom
    toFun := Uodd.toLinearMap.comp (D.toFun.comp
      ((Ueven.symm.toLinearMap.comp dom.subtype).codRestrict D.domain
        (fun u ↦ u.property))) }

set_option maxHeartbeats 2000000 in
-- The extended limit accommodates the product Sobolev realization and closed graph comparisons.
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- The graded matrix on pure smooth tensors extends uniquely from actual product H1. -/
theorem existsUnique_gradedProductH1Extension :
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
    let g₀₀ := externalTensorMetric h₀ k₀
    let g₁₁ := externalTensorMetric h₁ k₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
        (externalTensorFiber E₀ F₀))
      (B : SmoothBundlePresentation (n := n + m) (r := r₁ * s₁)
        (externalTensorFiber E₁ F₁)),
    ∃! T : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1) →L[ℂ]
        WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν)),
      (∀ (u : smoothSections (n := n) (r := r₀) E₀)
          (v : smoothSections (n := m) (r := s₀) F₀),
        T (WithLp.toLp 2 (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v), 0)) =
          WithLp.toLp 2
            (g₁₀.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F₀ (P.toLinearMap u) v),
              g₀₁.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F₁ u (Q.toLinearMap v)))) ∧
      (∀ (u : smoothSections (n := n) (r := r₁) E₁)
          (v : smoothSections (n := m) (r := s₁) F₁),
        T (WithLp.toLp 2 (0, B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) =
          WithLp.toLp 2
            (-g₁₀.smoothToL2 (μ.prod ν)
              (externalTensorSection E₁ F₀ u ((Q.metricFormalAdjoint k₀ k₁).toLinearMap v)),
              g₀₁.smoothToL2 (μ.prod ν)
                (externalTensorSection E₀ F₁
                  ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) v))) := by
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
  intro A B
  let g₁₀ := externalTensorMetric h₁ k₀
  let g₀₁ := externalTensorMetric h₀ k₁
  let A₀ := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r₀) E₀)
  let A₁ := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r₁) E₁)
  let B₀ := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s₀) F₀)
  let B₁ := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s₁) F₁)
  let C₀₀ := externalTensorPresentation A₀ B₀
  let C₁₁ := externalTensorPresentation A₁ B₁
  -- The exact mixed embeddings control the two partial directions independently.
  obtain ⟨L₀₀, R₀₀, _, _, hL₀₀, hR₀₀⟩ := exists_externalTensorH1_mixed_maps A₀ B₀
  obtain ⟨L₁₁, R₁₁, _, _, hL₁₁, hR₁₁⟩ := exists_externalTensorH1_mixed_maps A₁ B₁
  -- The original PDOs and their original metric formal adjoints have order-one Sobolev bounds.
  let pS : A₀.SobolevSpace 1 →L[ℂ] A₁.SobolevSpace 0 :=
    P.sobolevRealization A₀ A₁ 1 0 (by norm_num)
  have hpS (u : smoothSections (n := n) (r := r₀) E₀) :
      pS (A₀.smoothToSobolev 1 u) =
        A₁.smoothToSobolev 0 (P.toLinearMap u) :=
    P.sobolevRealization_smoothToSobolev A₀ A₁ 1 0 (by norm_num) u
  let paS : A₁.SobolevSpace 1 →L[ℂ] A₀.SobolevSpace 0 :=
    (P.metricFormalAdjoint h₀ h₁).sobolevRealization A₁ A₀ 1 0 (by norm_num)
  have hpaS (u : smoothSections (n := n) (r := r₁) E₁) :
      paS (A₁.smoothToSobolev 1 u) =
        A₀.smoothToSobolev 0 ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) :=
    (P.metricFormalAdjoint h₀ h₁).sobolevRealization_smoothToSobolev A₁ A₀ 1 0 (by norm_num) u
  let qS : B₀.SobolevSpace 1 →L[ℂ] B₁.SobolevSpace 0 :=
    Q.sobolevRealization B₀ B₁ 1 0 (by norm_num)
  have hqS (u : smoothSections (n := m) (r := s₀) F₀) :
      qS (B₀.smoothToSobolev 1 u) =
        B₁.smoothToSobolev 0 (Q.toLinearMap u) :=
    Q.sobolevRealization_smoothToSobolev B₀ B₁ 1 0 (by norm_num) u
  let qaS : B₁.SobolevSpace 1 →L[ℂ] B₀.SobolevSpace 0 :=
    (Q.metricFormalAdjoint k₀ k₁).sobolevRealization B₁ B₀ 1 0 (by norm_num)
  have hqaS (u : smoothSections (n := m) (r := s₁) F₁) :
      qaS (B₁.smoothToSobolev 1 u) =
        B₀.smoothToSobolev 0 ((Q.metricFormalAdjoint k₀ k₁).toLinearMap u) :=
    (Q.metricFormalAdjoint k₀ k₁).sobolevRealization_smoothToSobolev B₁ B₀ 1 0 (by norm_num) u
  let e₀ := (h₀.sobolevZeroEquivL2 (μ := μ) A₀).toContinuousLinearMap
  let e₁ := (h₁.sobolevZeroEquivL2 (μ := μ) A₁).toContinuousLinearMap
  let f₀ := (k₀.sobolevZeroEquivL2 (μ := ν) B₀).toContinuousLinearMap
  let f₁ := (k₁.sobolevZeroEquivL2 (μ := ν) B₁).toContinuousLinearMap
  let p := e₁.comp pS
  let pa := e₀.comp paS
  let q := f₁.comp qS
  let qa := f₀.comp qaS
  have hp (u : smoothSections (n := n) (r := r₀) E₀) :
      p (A₀.smoothToSobolev 1 u) = h₁.smoothToL2 μ (P.toLinearMap u) := by
    change (h₁.sobolevZeroEquivL2 (μ := μ) A₁)
      (pS (A₀.smoothToSobolev 1 u)) = _
    rw [hpS, h₁.sobolevZeroEquivL2_smooth]
  have hpa (u : smoothSections (n := n) (r := r₁) E₁) :
      pa (A₁.smoothToSobolev 1 u) =
          h₀.smoothToL2 μ ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) := by
    change (h₀.sobolevZeroEquivL2 (μ := μ) A₀)
      (paS (A₁.smoothToSobolev 1 u)) = _
    rw [hpaS, h₀.sobolevZeroEquivL2_smooth]
  have hq (u : smoothSections (n := m) (r := s₀) F₀) :
      q (B₀.smoothToSobolev 1 u) = k₁.smoothToL2 ν (Q.toLinearMap u) := by
    change (k₁.sobolevZeroEquivL2 (μ := ν) B₁)
      (qS (B₀.smoothToSobolev 1 u)) = _
    rw [hqS, k₁.sobolevZeroEquivL2_smooth]
  have hqa (u : smoothSections (n := m) (r := s₁) F₁) :
      qa (B₁.smoothToSobolev 1 u) =
          k₀.smoothToL2 ν ((Q.metricFormalAdjoint k₀ k₁).toLinearMap u) := by
    change (k₀.sobolevZeroEquivL2 (μ := ν) B₀)
      (qaS (B₁.smoothToSobolev 1 u)) = _
    rw [hqaS, k₀.sobolevZeroEquivL2_smooth]
  have he₀ (u : smoothSections (n := n) (r := r₀) E₀) :
      e₀ (A₀.smoothToSobolev 0 u) = h₀.smoothToL2 μ u :=
    h₀.sobolevZeroEquivL2_smooth A₀ u
  have he₁ (u : smoothSections (n := n) (r := r₁) E₁) :
      e₁ (A₁.smoothToSobolev 0 u) = h₁.smoothToL2 μ u :=
    h₁.sobolevZeroEquivL2_smooth A₁ u
  have hf₀ (u : smoothSections (n := m) (r := s₀) F₀) :
      f₀ (B₀.smoothToSobolev 0 u) = k₀.smoothToL2 ν u :=
    k₀.sobolevZeroEquivL2_smooth B₀ u
  have hf₁ (u : smoothSections (n := m) (r := s₁) F₁) :
      f₁ (B₁.smoothToSobolev 0 u) = k₁.smoothToL2 ν u :=
    k₁.sobolevZeroEquivL2_smooth B₁ u
  let α := (A.sobolevEquiv C₀₀ 1).toContinuousLinearMap
  let β := (B.sobolevEquiv C₁₁ 1).toContinuousLinearMap
  have hα (u : smoothSections (n := n + m) (r := r₀ * s₀) (externalTensorFiber E₀ F₀)) :
      α (A.smoothToSobolev 1 u) = C₀₀.smoothToSobolev 1 u :=
    A.sobolevEquiv_smoothToSobolev C₀₀ 1 u
  have hβ (u : smoothSections (n := n + m) (r := r₁ * s₁) (externalTensorFiber E₁ F₁)) :
      β (B.smoothToSobolev 1 u) = C₁₁.smoothToSobolev 1 u :=
    B.sobolevEquiv_smoothToSobolev C₁₁ 1 u
  let e₁₀ : HilbertTensorProduct (h₁.L2SectionSpace μ) (k₀.L2SectionSpace ν) →L[ℂ]
      g₁₀.L2SectionSpace (μ.prod ν) :=
    (externalTensorL2Equiv μ ν h₁ k₀).toLinearIsometry.toContinuousLinearMap
  let e₀₁ : HilbertTensorProduct (h₀.L2SectionSpace μ) (k₁.L2SectionSpace ν) →L[ℂ]
      g₀₁.L2SectionSpace (μ.prod ν) :=
    (externalTensorL2Equiv μ ν h₀ k₁).toLinearIsometry.toContinuousLinearMap
  -- Assemble four bounded partial actions in the original exterior-bundle L2 spaces.
  let U : A.SobolevSpace 1 →L[ℂ] g₁₀.L2SectionSpace (μ.prod ν) :=
    e₁₀.comp ((TensorProduct.mapL p f₀).completion.comp (L₀₀.comp α))
  let V : A.SobolevSpace 1 →L[ℂ] g₀₁.L2SectionSpace (μ.prod ν) :=
    e₀₁.comp ((TensorProduct.mapL e₀ q).completion.comp (R₀₀.comp α))
  let W : B.SobolevSpace 1 →L[ℂ] g₁₀.L2SectionSpace (μ.prod ν) :=
    e₁₀.comp ((TensorProduct.mapL e₁ qa).completion.comp (R₁₁.comp β))
  let Z : B.SobolevSpace 1 →L[ℂ] g₀₁.L2SectionSpace (μ.prod ν) :=
    e₀₁.comp ((TensorProduct.mapL pa f₁).completion.comp (L₁₁.comp β))
  have hU (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      U (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) =
        g₁₀.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F₀ (P.toLinearMap u) (v)) := by
    have hinput := (congrArg L₀₀ (hα (externalTensorSection E₀ F₀ u v))).trans
      (hL₀₀ u v)
    let f := (TensorProduct.mapL p f₀).completion
    have hmap : f (↑(A₀.smoothToSobolev 1 u ⊗ₜ[ℂ] B₀.smoothToSobolev 0 v)) =
        ↑(h₁.smoothToL2 μ (P.toLinearMap u) ⊗ₜ[ℂ] k₀.smoothToL2 ν (v)) := by
      change (TensorProduct.mapL p f₀).completion
        (↑(A₀.smoothToSobolev 1 u ⊗ₜ[ℂ] B₀.smoothToSobolev 0 v)) = _
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul, hp, hf₀]
    exact (congrArg (fun z ↦ e₁₀ (f z)) hinput).trans ((congrArg e₁₀ hmap).trans
      (externalTensorL2Equiv_smooth μ ν h₁ k₀ (P.toLinearMap u) (v)))
  have hV (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      V (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) =
        g₀₁.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F₁ (u) (Q.toLinearMap v)) := by
    have hinput := (congrArg R₀₀ (hα (externalTensorSection E₀ F₀ u v))).trans
      (hR₀₀ u v)
    let f := (TensorProduct.mapL e₀ q).completion
    have hmap : f (↑(A₀.smoothToSobolev 0 u ⊗ₜ[ℂ] B₀.smoothToSobolev 1 v)) =
        ↑(h₀.smoothToL2 μ (u) ⊗ₜ[ℂ] k₁.smoothToL2 ν (Q.toLinearMap v)) := by
      change (TensorProduct.mapL e₀ q).completion
        (↑(A₀.smoothToSobolev 0 u ⊗ₜ[ℂ] B₀.smoothToSobolev 1 v)) = _
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul, he₀, hq]
    exact (congrArg (fun z ↦ e₀₁ (f z)) hinput).trans ((congrArg e₀₁ hmap).trans
      (externalTensorL2Equiv_smooth μ ν h₀ k₁ (u) (Q.toLinearMap v)))
  have hW (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := m) (r := s₁) F₁) :
      W (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v)) =
        g₁₀.smoothToL2 (μ.prod ν)
          (externalTensorSection E₁ F₀ (u) ((Q.metricFormalAdjoint k₀ k₁).toLinearMap v)) := by
    have hinput := (congrArg R₁₁ (hβ (externalTensorSection E₁ F₁ u v))).trans
      (hR₁₁ u v)
    let f := (TensorProduct.mapL e₁ qa).completion
    have hmap : f (↑(A₁.smoothToSobolev 0 u ⊗ₜ[ℂ] B₁.smoothToSobolev 1 v)) =
        ↑(h₁.smoothToL2 μ u ⊗ₜ[ℂ]
          k₀.smoothToL2 ν ((Q.metricFormalAdjoint k₀ k₁).toLinearMap v)) := by
      change (TensorProduct.mapL e₁ qa).completion
        (↑(A₁.smoothToSobolev 0 u ⊗ₜ[ℂ] B₁.smoothToSobolev 1 v)) = _
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul, he₁, hqa]
    exact (congrArg (fun z ↦ e₁₀ (f z)) hinput).trans ((congrArg e₁₀ hmap).trans
      (externalTensorL2Equiv_smooth μ ν h₁ k₀ (u) ((Q.metricFormalAdjoint k₀ k₁).toLinearMap v)))
  have hZ (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := m) (r := s₁) F₁) :
      Z (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v)) =
        g₀₁.smoothToL2 (μ.prod ν)
          (externalTensorSection E₀ F₁ ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) (v)) := by
    have hinput := (congrArg L₁₁ (hβ (externalTensorSection E₁ F₁ u v))).trans
      (hL₁₁ u v)
    let f := (TensorProduct.mapL pa f₁).completion
    have hmap : f (↑(A₁.smoothToSobolev 1 u ⊗ₜ[ℂ] B₁.smoothToSobolev 0 v)) =
        ↑(h₀.smoothToL2 μ ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) ⊗ₜ[ℂ]
          k₁.smoothToL2 ν v) := by
      change (TensorProduct.mapL pa f₁).completion
        (↑(A₁.smoothToSobolev 1 u ⊗ₜ[ℂ] B₁.smoothToSobolev 0 v)) = _
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul, hpa, hf₁]
    exact (congrArg (fun z ↦ e₀₁ (f z)) hinput).trans ((congrArg e₀₁ hmap).trans
      (externalTensorL2Equiv_smooth μ ν h₀ k₁ ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) (v)))
  let inEq := WithLp.prodContinuousLinearEquiv 2 ℂ (A.SobolevSpace 1) (B.SobolevSpace 1)
  let outEq := WithLp.prodContinuousLinearEquiv 2 ℂ
    (g₁₀.L2SectionSpace (μ.prod ν)) (g₀₁.L2SectionSpace (μ.prod ν))
  let T := outEq.symm.toContinuousLinearMap.comp
    (((U.coprod (-W)).prod (V.coprod Z)).comp inEq.toContinuousLinearMap)
  -- The two columns retain precisely the original graded matrix signs.
  have hfirst (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      T (WithLp.toLp 2 (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v), 0)) =
        WithLp.toLp 2
          (g₁₀.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F₀ (P.toLinearMap u) v),
            g₀₁.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F₁ u (Q.toLinearMap v))) := by
    change WithLp.toLp 2
      (U (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) + -(W 0),
        V (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) + Z 0) = _
    simp only [map_zero, neg_zero, add_zero, hU, hV]
  have hsecond (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := m) (r := s₁) F₁) :
      T (WithLp.toLp 2 (0, B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) =
        WithLp.toLp 2
          (-g₁₀.smoothToL2 (μ.prod ν)
            (externalTensorSection E₁ F₀ u ((Q.metricFormalAdjoint k₀ k₁).toLinearMap v)),
            g₀₁.smoothToL2 (μ.prod ν)
              (externalTensorSection E₀ F₁
                ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) v)) := by
    change WithLp.toLp 2
      (U 0 + -(W (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))),
        V 0 + Z (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) = _
    simp only [map_zero, zero_add, hW, hZ]
  refine ⟨T, ⟨hfirst, hsecond⟩, ?_⟩
  intro S hS
  -- H1 density in each column proves uniqueness on their full Hilbert direct sum.
  let iA := inEq.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (A.SobolevSpace 1) (B.SobolevSpace 1))
  let iB := inEq.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (A.SobolevSpace 1) (B.SobolevSpace 1))
  have heqA : S.comp iA = T.comp iA := by
    apply ContinuousLinearMap.ext_on (dense_span_externalTensorH1 (E := E₀) (F := F₀) A)
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change S (WithLp.toLp 2 (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v), 0)) =
      T (WithLp.toLp 2 (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v), 0))
    exact (hS.1 u v).trans (hfirst u v).symm
  have heqB : S.comp iB = T.comp iB := by
    apply ContinuousLinearMap.ext_on (dense_span_externalTensorH1 (E := E₁) (F := F₁) B)
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change S (WithLp.toLp 2 (0, B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) =
      T (WithLp.toLp 2 (0, B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v)))
    exact (hS.2 u v).trans (hsecond u v).symm
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := inEq.symm.surjective z
  have hsplit : inEq.symm (x, y) = iA x + iB y := by
    change WithLp.toLp 2 (x, y) = WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (0, y)
    rw [← WithLp.toLp_add]
    simp
  rw [hsplit, map_add, map_add]
  exact congrArg₂ (· + ·) (DFunLike.congr_fun heqA x)
    (DFunLike.congr_fun heqB y)

/-- The bounded product-H1 action selected by its two exact smooth tensor columns. -/
def gradedProductH1Extension :
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
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
        (externalTensorFiber E₀ F₀))
      (B : SmoothBundlePresentation (n := n + m) (r := r₁ * s₁)
        (externalTensorFiber E₁ F₁)),
    WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1) →L[ℂ]
      WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν)) := by
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
  exact fun A B ↦ (existsUnique_gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B).exists.choose

set_option maxHeartbeats 2500000 in
-- The extended limit accommodates the product Sobolev realization and closed graph comparisons.
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Ellipticity bounds the geometric H1 norm by the actual L2 matrix graph norm. -/
theorem gradedProductH1Extension_graph_norm (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
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
    let g₀₀ := externalTensorMetric h₀ k₀
    let g₁₁ := externalTensorMetric h₁ k₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
        (externalTensorFiber E₀ F₀))
      (B : SmoothBundlePresentation (n := n + m) (r := r₁ * s₁)
        (externalTensorFiber E₁ F₁)),
    let J₀ := (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
    let J₁ := (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).toContinuousLinearMap.comp
      (B.sobolevInclusion 1 0 (by norm_num))
    let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
      ((J₀.prodMap J₁).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
    let T := gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B
    ∃ C : ℝ, 0 < C ∧ ∀ w : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1),
      ‖w‖ ≤ C * (‖J w‖ + ‖T w‖) := by
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
  intro A B
  let g₀₀ := externalTensorMetric h₀ k₀
  let g₁₁ := externalTensorMetric h₁ k₁
  let g₁₀ := externalTensorMetric h₁ k₀
  let g₀₁ := externalTensorMetric h₀ k₁
  let J₀ := (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  let J₁ := (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).toContinuousLinearMap.comp
    (B.sobolevInclusion 1 0 (by norm_num))
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    ((J₀.prodMap J₁).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
  let T := gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B
  change ∃ C : ℝ, 0 < C ∧ ∀ w, ‖w‖ ≤ C * (‖J w‖ + ‖T w‖)
  let X := WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1)
  let iA : A.SobolevSpace 1 →L[ℂ] X :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ _ _)
  let iB : B.SobolevSpace 1 →L[ℂ] X :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℂ _ _)
  let SE₀ := smoothSections (n := n) (r := r₀) E₀
  let SE₁ := smoothSections (n := n) (r := r₁) E₁
  let SF₀ := smoothSections (n := m) (r := s₀) F₀
  let SF₁ := smoothSections (n := m) (r := s₁) F₁
  let B₀ : SE₀ →ₗ[ℂ] SF₀ →ₗ[ℂ]
      smoothSections (n := n + m) (r := r₀ * s₀) (externalTensorFiber E₀ F₀) :=
    LinearMap.mk₂ ℂ (externalTensorSection E₀ F₀)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.add_tmul _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact (TensorProduct.smul_tmul' _ _ _).symm)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_add _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_smul _ _ _)
  let U₀ : SE₀ ⊗[ℂ] SF₀ →ₗ[ℂ] A.SobolevSpace 1 :=
    (A.smoothToSobolev 1).comp (TensorProduct.lift B₀)
  have hU₀ (u : SE₀) (v : SF₀) :
      U₀ (u ⊗ₜ[ℂ] v) = A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v) := rfl
  let B₁ : SE₁ →ₗ[ℂ] SF₁ →ₗ[ℂ]
      smoothSections (n := n + m) (r := r₁ * s₁) (externalTensorFiber E₁ F₁) :=
    LinearMap.mk₂ ℂ (externalTensorSection E₁ F₁)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.add_tmul _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact (TensorProduct.smul_tmul' _ _ _).symm)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_add _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_smul _ _ _)
  let U₁ : SE₁ ⊗[ℂ] SF₁ →ₗ[ℂ] B.SobolevSpace 1 :=
    (B.smoothToSobolev 1).comp (TensorProduct.lift B₁)
  have hU₁ (u : SE₁) (v : SF₁) :
      U₁ (u ⊗ₜ[ℂ] v) = B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v) := rfl
  -- Each parity component has its own actual two-factor elliptic estimate.
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_externalTensorH1_elliptic_estimate
    h₀ h₁ k₀ k₁ P Q hP hQ A U₀ hU₀
  let Pa := P.metricFormalAdjoint h₀ h₁
  let Qa := Q.metricFormalAdjoint k₀ k₁
  have hPa : Pa.IsElliptic := (P.isElliptic_metricFormalAdjoint_iff h₀ h₁).mpr hP
  have hQa : Qa.IsElliptic := (Q.isElliptic_metricFormalAdjoint_iff k₀ k₁).mpr hQ
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_externalTensorH1_elliptic_estimate
    h₁ h₀ k₁ k₀ Pa Qa hPa hQa B U₁ hU₁
  let j₀ := TensorProduct.map (h₀.smoothToL2 μ) (k₀.smoothToL2 ν)
  let j₁ := TensorProduct.map (h₁.smoothToL2 μ) (k₁.smoothToL2 ν)
  let a := TensorProduct.map ((h₁.smoothToL2 μ).comp P.toLinearMap) (k₀.smoothToL2 ν)
  let b := TensorProduct.map (h₀.smoothToL2 μ) ((k₁.smoothToL2 ν).comp Q.toLinearMap)
  let c := TensorProduct.map ((h₀.smoothToL2 μ).comp Pa.toLinearMap) (k₁.smoothToL2 ν)
  let d := TensorProduct.map (h₁.smoothToL2 μ) ((k₀.smoothToL2 ν).comp Qa.toLinearMap)
  let e₀₀ := externalTensorL2Equiv μ ν h₀ k₀
  let e₁₁ := externalTensorL2Equiv μ ν h₁ k₁
  let e₁₀ := externalTensorL2Equiv μ ν h₁ k₀
  let e₀₁ := externalTensorL2Equiv μ ν h₀ k₁
  have hspec := (existsUnique_gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B).exists.choose_spec
  -- The original selected extension and inclusion retain their exact smooth tensor columns.
  have hJ₀ (x : SE₀ ⊗[ℂ] SF₀) : J₀ (U₀ x) = e₀₀ (↑(j₀ x)) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      rw [hU₀]
      change (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A)
        (A.sobolevInclusion 1 0 (by norm_num)
          (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v))) = _
      rw [A.sobolevInclusion_smoothToSobolev, g₀₀.sobolevZeroEquivL2_smooth]
      exact (externalTensorL2Equiv_smooth μ ν h₀ k₀ u v).symm
    | add x y hx hy => simp only [map_add, Completion.coe_add, hx, hy]
  have hJ₁ (y : SE₁ ⊗[ℂ] SF₁) : J₁ (U₁ y) = e₁₁ (↑(j₁ y)) := by
    induction y using TensorProduct.inductionOn with
    | tmul u v =>
      rw [hU₁]
      change (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B)
        (B.sobolevInclusion 1 0 (by norm_num)
          (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) = _
      rw [B.sobolevInclusion_smoothToSobolev, g₁₁.sobolevZeroEquivL2_smooth]
      exact (externalTensorL2Equiv_smooth μ ν h₁ k₁ u v).symm
    | add x y hx hy => simp only [map_add, Completion.coe_add, hx, hy]
  have hT₀ (x : SE₀ ⊗[ℂ] SF₀) :
      T (iA (U₀ x)) = WithLp.toLp 2 (e₁₀ (↑(a x)), e₀₁ (↑(b x))) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      rw [hU₀]
      have hs : T (iA (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v))) =
          WithLp.toLp 2
            (g₁₀.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F₀ (P.toLinearMap u) v),
              g₀₁.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F₁ u (Q.toLinearMap v))) :=
        hspec.1 u v
      refine hs.trans ?_
      congr 1
      apply Prod.ext
      · exact (externalTensorL2Equiv_smooth μ ν h₁ k₀ (P.toLinearMap u) v).symm
      · exact (externalTensorL2Equiv_smooth μ ν h₀ k₁ u (Q.toLinearMap v)).symm
    | add x y hx hy =>
      simp only [map_add, Completion.coe_add, hx, hy, ← WithLp.toLp_add, Prod.mk_add_mk]
  have hT₁ (y : SE₁ ⊗[ℂ] SF₁) :
      T (iB (U₁ y)) = WithLp.toLp 2 (-e₁₀ (↑(d y)), e₀₁ (↑(c y))) := by
    induction y using TensorProduct.inductionOn with
    | tmul u v =>
      rw [hU₁]
      have hs : T (iB (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) =
          WithLp.toLp 2
            (-g₁₀.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F₀ u (Qa.toLinearMap v)),
              g₀₁.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F₁ (Pa.toLinearMap u) v)) :=
        hspec.2 u v
      refine hs.trans ?_
      congr 1
      apply Prod.ext
      · exact congrArg Neg.neg
          (externalTensorL2Equiv_smooth μ ν h₁ k₀ u (Qa.toLinearMap v)).symm
      · exact (externalTensorL2Equiv_smooth μ ν h₀ k₁ (Pa.toLinearMap u) v).symm
    | add x y hx hy =>
      simp only [map_add, Completion.coe_add, hx, hy, ← WithLp.toLp_add, Prod.mk_add_mk,
        neg_add_rev]
      congr 2
      abel
  -- Integral adjunction cancels the two cross terms with the original negative top-right sign.
  have hadjP (u : SE₀) (v : SE₁) :
      inner ℂ (h₁.smoothToL2 μ (P.toLinearMap u)) (h₁.smoothToL2 μ v) =
        inner ℂ (h₀.smoothToL2 μ u) (h₀.smoothToL2 μ (Pa.toLinearMap v)) := by
    rw [h₁.inner_smoothToL2, h₀.inner_smoothToL2]
    exact P.isMetricFormalAdjoint_metricFormalAdjoint h₀ h₁ u v
  have hadjQ (u : SF₀) (v : SF₁) :
      inner ℂ (k₁.smoothToL2 ν (Q.toLinearMap u)) (k₁.smoothToL2 ν v) =
        inner ℂ (k₀.smoothToL2 ν u) (k₀.smoothToL2 ν (Qa.toLinearMap v)) := by
    rw [k₁.inner_smoothToL2, k₀.inner_smoothToL2]
    exact Q.isMetricFormalAdjoint_metricFormalAdjoint k₀ k₁ u v
  have hcross (x : SE₀ ⊗[ℂ] SF₀) (y : SE₁ ⊗[ℂ] SF₁) :
      inner ℂ (a x) (d y) = inner ℂ (b x) (c y) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      induction y using TensorProduct.inductionOn with
      | tmul u' v' =>
        simp only [a, b, c, d, TensorProduct.map_tmul, TensorProduct.inner_tmul,
          LinearMap.comp_apply, hadjP, hadjQ]
      | add x y hx hy => simp only [map_add, inner_add_right, hx, hy]
    | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]
  let V (x : SE₀ ⊗[ℂ] SF₀) (y : SE₁ ⊗[ℂ] SF₁) := iA (U₀ x) + iB (U₁ y)
  have hJnorm (x : SE₀ ⊗[ℂ] SF₀) (y : SE₁ ⊗[ℂ] SF₁) :
      ‖J (V x y)‖ ^ 2 = ‖j₀ x‖ ^ 2 + ‖j₁ y‖ ^ 2 := by
    have heq : J (V x y) = WithLp.toLp 2 (e₀₀ (↑(j₀ x)), e₁₁ (↑(j₁ y))) := by
      change WithLp.toLp 2 (J₀ (U₀ x + 0), J₁ (0 + U₁ y)) = _
      simp only [add_zero, zero_add, hJ₀, hJ₁]
    rw [heq, WithLp.prod_norm_sq_eq_of_L2]
    change ‖e₀₀ (↑(j₀ x))‖ ^ 2 + ‖e₁₁ (↑(j₁ y))‖ ^ 2 = _
    rw [e₀₀.norm_map, e₁₁.norm_map, Completion.norm_coe, Completion.norm_coe]
  have hTnorm (x : SE₀ ⊗[ℂ] SF₀) (y : SE₁ ⊗[ℂ] SF₁) :
      ‖T (V x y)‖ ^ 2 =
        ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have heq : T (V x y) = WithLp.toLp 2
        (e₁₀ (↑(a x - d y)), e₀₁ (↑(b x + c y))) := by
      change T (iA (U₀ x) + iB (U₁ y)) = _
      simp only [map_add, hT₀, hT₁, ← WithLp.toLp_add, Prod.mk_add_mk,
        sub_eq_add_neg, Completion.coe_add, Completion.coe_neg, map_neg]
    rw [heq, WithLp.prod_norm_sq_eq_of_L2]
    change ‖e₁₀ (↑(a x - d y))‖ ^ 2 + ‖e₀₁ (↑(b x + c y))‖ ^ 2 = _
    rw [e₁₀.norm_map, e₀₁.norm_map, Completion.norm_coe, Completion.norm_coe,
      norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hcross]
    ring
  let C := 2 * (C₀ + C₁)
  have hC : 0 < C := by dsimp [C]; positivity
  have hfinite (x : SE₀ ⊗[ℂ] SF₀) (y : SE₁ ⊗[ℂ] SF₁) :
      ‖V x y‖ ≤ C * (‖J (V x y)‖ + ‖T (V x y)‖) := by
    have hj := hJnorm x y
    have ht := hTnorm x y
    have hj₀ : ‖j₀ x‖ ≤ ‖J (V x y)‖ := by
      nlinarith [sq_nonneg ‖j₁ y‖, norm_nonneg (J (V x y))]
    have hj₁ : ‖j₁ y‖ ≤ ‖J (V x y)‖ := by
      nlinarith [sq_nonneg ‖j₀ x‖, norm_nonneg (J (V x y))]
    have ha : ‖a x‖ ≤ ‖T (V x y)‖ := by
      nlinarith [sq_nonneg ‖b x‖, sq_nonneg ‖c y‖, sq_nonneg ‖d y‖,
        norm_nonneg (T (V x y))]
    have hb : ‖b x‖ ≤ ‖T (V x y)‖ := by
      nlinarith [sq_nonneg ‖a x‖, sq_nonneg ‖c y‖, sq_nonneg ‖d y‖,
        norm_nonneg (T (V x y))]
    have hc : ‖c y‖ ≤ ‖T (V x y)‖ := by
      nlinarith [sq_nonneg ‖a x‖, sq_nonneg ‖b x‖, sq_nonneg ‖d y‖,
        norm_nonneg (T (V x y))]
    have hd : ‖d y‖ ≤ ‖T (V x y)‖ := by
      nlinarith [sq_nonneg ‖a x‖, sq_nonneg ‖b x‖, sq_nonneg ‖c y‖,
        norm_nonneg (T (V x y))]
    have h0 := hb₀ x
    have h1 := hb₁ y
    change ‖U₀ x‖ ≤ C₀ * (‖j₀ x‖ + ‖a x‖ + ‖b x‖) at h0
    change ‖U₁ y‖ ≤ C₁ * (‖j₁ y‖ + ‖c y‖ + ‖d y‖) at h1
    have hu0 : ‖U₀ x‖ ≤ C₀ * (‖J (V x y)‖ + 2 * ‖T (V x y)‖) :=
      h0.trans (mul_le_mul_of_nonneg_left (by linarith) hC₀.le)
    have hu1 : ‖U₁ y‖ ≤ C₁ * (‖J (V x y)‖ + 2 * ‖T (V x y)‖) :=
      h1.trans (mul_le_mul_of_nonneg_left (by linarith) hC₁.le)
    have hsum : ‖V x y‖ ≤ ‖U₀ x‖ + ‖U₁ y‖ := by
      exact (norm_add_le _ _).trans_eq (congrArg₂ (· + ·)
        (WithLp.norm_toLp_fst 2 _ _ (U₀ x)) (WithLp.norm_toLp_snd 2 _ _ (U₁ y)))
    dsimp [C]
    nlinarith [mul_nonneg hC₀.le (norm_nonneg (J (V x y))),
      mul_nonneg hC₁.le (norm_nonneg (J (V x y)))]
  -- Density in the original geometric H1 topology extends the estimate to every input.
  have hU₀dense : DenseRange U₀ := by
    apply (dense_span_externalTensorH1 (E := E₀) (F := F₀) A).mono
    change _ ≤ U₀.range
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    exact ⟨u ⊗ₜ[ℂ] v, hU₀ u v⟩
  have hU₁dense : DenseRange U₁ := by
    apply (dense_span_externalTensorH1 (E := E₁) (F := F₁) B).mono
    change _ ≤ U₁.range
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    exact ⟨u ⊗ₜ[ℂ] v, hU₁ u v⟩
  refine ⟨C, hC, ?_⟩
  intro w
  obtain ⟨⟨x, y⟩, rfl⟩ := (WithLp.prodContinuousLinearEquiv 2 ℂ
    (A.SobolevSpace 1) (B.SobolevSpace 1)).symm.surjective w
  have hall (x : A.SobolevSpace 1) (y : B.SobolevSpace 1) :
      ‖iA x + iB y‖ ≤ C * (‖J (iA x + iB y)‖ + ‖T (iA x + iB y)‖) := by
    refine hU₀dense.induction_on (p := fun x ↦
      ‖iA x + iB y‖ ≤ C * (‖J (iA x + iB y)‖ + ‖T (iA x + iB y)‖)) x ?_ ?_
    · have hi : Continuous (fun x : A.SobolevSpace 1 ↦ iA x + iB y) :=
        iA.continuous.add continuous_const
      exact isClosed_le hi.norm (continuous_const.mul
        ((J.continuous.comp hi).norm.add (T.continuous.comp hi).norm))
    · intro u
      refine hU₁dense.induction_on (p := fun y ↦
        ‖iA (U₀ u) + iB y‖ ≤
          C * (‖J (iA (U₀ u) + iB y)‖ + ‖T (iA (U₀ u) + iB y)‖)) y ?_ ?_
      · have hi : Continuous (fun y : B.SobolevSpace 1 ↦ iA (U₀ u) + iB y) :=
          continuous_const.add iB.continuous
        exact isClosed_le hi.norm (continuous_const.mul
          ((J.continuous.comp hi).norm.add (T.continuous.comp hi).norm))
      · intro v
        exact hfinite u v
  have hw : (WithLp.prodContinuousLinearEquiv 2 ℂ
      (A.SobolevSpace 1) (B.SobolevSpace 1)).symm (x, y) = iA x + iB y := by
    change WithLp.toLp 2 (x, y) = WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (0, y)
    rw [← WithLp.toLp_add]
    simp
  rw [hw]
  exact hall x y


set_option linter.unusedVariables false in
set_option maxHeartbeats 3000000 in
-- The extended limit accommodates the product Sobolev realization and closed graph comparisons.
set_option backward.isDefEq.respectTransparency false in
/-- The exact closed product graph is the graph of its original geometric H1 realization. -/
theorem gradedProductL2Operator_graph_sobolev (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
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
    let g₀₀ := externalTensorMetric h₀ k₀
    let g₁₁ := externalTensorMetric h₁ k₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
        (externalTensorFiber E₀ F₀))
      (B : SmoothBundlePresentation (n := n + m) (r := r₁ * s₁)
        (externalTensorFiber E₁ F₁)),
    let J₀ := (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
    let J₁ := (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).toContinuousLinearMap.comp
      (B.sobolevInclusion 1 0 (by norm_num))
    let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
      ((J₀.prodMap J₁).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
    let T := gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B
    (gradedProductL2Operator h₀ h₁ k₀ k₁ P Q).graph =
      (J.toLinearMap.prod T.toLinearMap).range := by
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
  intro A B
  let g₀₀ := externalTensorMetric h₀ k₀
  let g₁₁ := externalTensorMetric h₁ k₁
  let g₁₀ := externalTensorMetric h₁ k₀
  let g₀₁ := externalTensorMetric h₀ k₁
  let J₀ := (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  let J₁ := (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).toContinuousLinearMap.comp
    (B.sobolevInclusion 1 0 (by norm_num))
  let inEq := WithLp.prodContinuousLinearEquiv 2 ℂ (A.SobolevSpace 1) (B.SobolevSpace 1)
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    ((J₀.prodMap J₁).comp inEq.toContinuousLinearMap)
  let T := gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B
  let L := J.prod T
  let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₁ k₁)
  let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₀ k₁)
  let P₀ := P.metricL2ClosedRealization h₀ h₁
  let Q₀ := Q.metricL2ClosedRealization k₀ k₁
  let D := gradedTensorOperator P₀ Q₀
  let G := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
  let Φ := Ueven.toContinuousLinearEquiv.prodCongr Uodd.toContinuousLinearEquiv
  change G.graph = L.range
  -- The elliptic estimate makes the original H1 graph map bounded below and hence closed.
  obtain ⟨C, hC, hbound⟩ := gradedProductH1Extension_graph_norm h₀ h₁ k₀ k₁ P Q hP hQ A B
  have hLbound (u) : ‖u‖ ≤ (⟨2 * C, by positivity⟩ : NNReal) * ‖L u‖ := by
    have hJu : ‖J u‖ ≤ ‖L u‖ := norm_fst_le (L u)
    have hTu : ‖T u‖ ≤ ‖L u‖ := norm_snd_le (L u)
    have hu := hbound u
    change ‖u‖ ≤ (2 * C) * ‖L u‖
    nlinarith
  have hLclosed : IsClosed (L.range : Set
      (WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν)) ×
        WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν)))) :=
    (L.antilipschitz_of_bound hLbound).isClosed_range L.uniformContinuous
  -- Conjugation uses precisely the two unitaries in the original geometric operator.
  have hGgraph : G.graph = D.graph.map Φ.toLinearMap := by
    apply Submodule.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x, rfl⟩ := G.mem_graph_iff'.mp hz
      let y : D.domain := ⟨Ueven.symm x.val, x.property⟩
      refine ⟨(y.val, D y), D.mem_graph y, ?_⟩
      apply Prod.ext
      · exact Ueven.apply_symm_apply x.val
      · rfl
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, rfl⟩ := D.mem_graph_iff'.mp hz
      have hx : Ueven y.val ∈ G.domain := by
        change Ueven.symm (Ueven y.val) ∈ D.domain
        rw [Ueven.symm_apply_apply]
        exact y.property
      apply G.mem_graph_iff.mpr
      refine ⟨⟨Ueven y.val, hx⟩, rfl, ?_⟩
      change Uodd (D ⟨Ueven.symm (Ueven y.val), hx⟩) = Uodd (D y)
      congr 2
      exact Subtype.ext (Ueven.symm_apply_apply y.val)
  -- The original smooth realization is exactly the range of its specified two graph maps.
  let i₀ := h₀.smoothToL2 μ
  let i₁ := h₁.smoothToL2 μ
  let j₀ := k₀.smoothToL2 ν
  let j₁ := k₁.smoothToL2 ν
  let p := i₁.comp P.toLinearMap
  let pa := i₀.comp (P.metricFormalAdjoint h₀ h₁).toLinearMap
  let q := j₁.comp Q.toLinearMap
  let qa := j₀.comp (Q.metricFormalAdjoint k₀ k₁).toLinearMap
  have hPc : P₀.graph = (i₀.prod p).range.topologicalClosure := by
    rw [(P.metricL2ClosedRealization_realization h₀ h₁).1]
    congr 1
    exact linearPMap_graph_of_injective_parametrization i₀ (h₀.smoothToL2_injective μ) p
  have hPac : P₀.adjoint.graph = (i₁.prod pa).range.topologicalClosure := by
    rw [← P.metricL2ClosedRealization_metricFormalAdjoint h₀ h₁ hP]
    rw [((P.metricFormalAdjoint h₀ h₁).metricL2ClosedRealization_realization h₁ h₀).1]
    congr 1
    exact linearPMap_graph_of_injective_parametrization i₁ (h₁.smoothToL2_injective μ) pa
  have hQc : Q₀.graph = (j₀.prod q).range.topologicalClosure := by
    rw [(Q.metricL2ClosedRealization_realization k₀ k₁).1]
    congr 1
    exact linearPMap_graph_of_injective_parametrization j₀ (k₀.smoothToL2_injective ν) q
  have hQac : Q₀.adjoint.graph = (j₁.prod qa).range.topologicalClosure := by
    rw [← Q.metricL2ClosedRealization_metricFormalAdjoint k₀ k₁ hQ]
    rw [((Q.metricFormalAdjoint k₀ k₁).metricL2ClosedRealization_realization k₁ k₀).1]
    congr 1
    exact linearPMap_graph_of_injective_parametrization j₁ (k₁.smoothToL2_injective ν) qa
  let HE := WithLp 2 (HilbertTensorProduct (h₀.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
    HilbertTensorProduct (h₁.L2SectionSpace μ) (k₁.L2SectionSpace ν))
  let HO := WithLp 2 (HilbertTensorProduct (h₁.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
    HilbertTensorProduct (h₀.L2SectionSpace μ) (k₁.L2SectionSpace ν))
  let c₀ (z : smoothSections (n := n) (r := r₀) E₀ ×
      smoothSections (n := m) (r := s₀) F₀) : HE × HO :=
    (WithLp.toLp 2 (↑(i₀ z.1 ⊗ₜ[ℂ] j₀ z.2), 0),
      WithLp.toLp 2 (↑(p z.1 ⊗ₜ[ℂ] j₀ z.2), ↑(i₀ z.1 ⊗ₜ[ℂ] q z.2)))
  let c₁ (z : smoothSections (n := n) (r := r₁) E₁ ×
      smoothSections (n := m) (r := s₁) F₁) : HE × HO :=
    (WithLp.toLp 2 (0, ↑(i₁ z.1 ⊗ₜ[ℂ] j₁ z.2)),
      WithLp.toLp 2 (-(↑(i₁ z.1 ⊗ₜ[ℂ] qa z.2)), ↑(pa z.1 ⊗ₜ[ℂ] j₁ z.2)))
  let S := Submodule.span ℂ (Set.range c₀ ∪ Set.range c₁)
  have hD : D.graph = S.topologicalClosure := gradedTensorOperator_graph_of_cores P₀ Q₀
    (P.metricL2ClosedRealization_realization h₀ h₁).2.2
    (Q.metricL2ClosedRealization_realization k₀ k₁).2.2
    i₀ p i₁ pa j₀ q j₁ qa hPc hPac hQc hQac
  have hGclosed : IsClosed (G.graph : Set
      (WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν)) ×
        WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν)))) := by
    rw [hGgraph]
    change IsClosed (Φ '' (D.graph : Set (HE × HO)))
    apply Φ.toHomeomorph.isClosedMap
    rw [hD]
    exact S.isClosed_topologicalClosure
  let iA := inEq.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (A.SobolevSpace 1) (B.SobolevSpace 1))
  let iB := inEq.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (A.SobolevSpace 1) (B.SobolevSpace 1))
  have hJ₀ (u : smoothSections (n := n + m) (r := r₀ * s₀) (externalTensorFiber E₀ F₀)) :
      J₀ (A.smoothToSobolev 1 u) = g₀₀.smoothToL2 (μ.prod ν) u := by
    change (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A)
      (A.sobolevInclusion 1 0 _ (A.smoothToSobolev 1 u)) = _
    rw [A.sobolevInclusion_smoothToSobolev, g₀₀.sobolevZeroEquivL2_smooth]
  have hJ₁ (u : smoothSections (n := n + m) (r := r₁ * s₁) (externalTensorFiber E₁ F₁)) :
      J₁ (B.smoothToSobolev 1 u) = g₁₁.smoothToL2 (μ.prod ν) u := by
    change (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B)
      (B.sobolevInclusion 1 0 _ (B.smoothToSobolev 1 u)) = _
    rw [B.sobolevInclusion_smoothToSobolev, g₁₁.sobolevZeroEquivL2_smooth]
  have hTspec := (existsUnique_gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B).exists.choose_spec
  have hc₀ (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      L (iA (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v))) = Φ (c₀ (u, v)) := by
    apply Prod.ext
    · change WithLp.toLp 2 (J₀ (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)), J₁ 0) =
        WithLp.toLp 2 ((externalTensorL2Equiv μ ν h₀ k₀) (↑(i₀ u ⊗ₜ[ℂ] j₀ v)),
          (externalTensorL2Equiv μ ν h₁ k₁) 0)
      rw [hJ₀, map_zero, map_zero]
      exact congrArg (fun z ↦ WithLp.toLp 2 (z, (0 : g₁₁.L2SectionSpace (μ.prod ν))))
        (externalTensorL2Equiv_smooth μ ν h₀ k₀ u v).symm
    · change T (WithLp.toLp 2 (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v), 0)) =
        WithLp.toLp 2 ((externalTensorL2Equiv μ ν h₁ k₀) (↑(p u ⊗ₜ[ℂ] j₀ v)),
          (externalTensorL2Equiv μ ν h₀ k₁) (↑(i₀ u ⊗ₜ[ℂ] q v)))
      rw [show T (WithLp.toLp 2
          (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v), 0)) = _ from hTspec.1 u v]
      congr 1
      exact Prod.ext (externalTensorL2Equiv_smooth μ ν h₁ k₀ (P.toLinearMap u) v).symm
        (externalTensorL2Equiv_smooth μ ν h₀ k₁ u (Q.toLinearMap v)).symm
  have hc₁ (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := m) (r := s₁) F₁) :
      L (iB (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) = Φ (c₁ (u, v)) := by
    apply Prod.ext
    · change WithLp.toLp 2 (J₀ 0, J₁ (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) =
        WithLp.toLp 2 ((externalTensorL2Equiv μ ν h₀ k₀) 0,
          (externalTensorL2Equiv μ ν h₁ k₁) (↑(i₁ u ⊗ₜ[ℂ] j₁ v)))
      rw [hJ₁, map_zero, map_zero]
      exact congrArg (fun z ↦ WithLp.toLp 2 ((0 : g₀₀.L2SectionSpace (μ.prod ν)), z))
        (externalTensorL2Equiv_smooth μ ν h₁ k₁ u v).symm
    · change T (WithLp.toLp 2 (0, B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) =
        WithLp.toLp 2 ((externalTensorL2Equiv μ ν h₁ k₀) (-(↑(i₁ u ⊗ₜ[ℂ] qa v))),
          (externalTensorL2Equiv μ ν h₀ k₁) (↑(pa u ⊗ₜ[ℂ] j₁ v)))
      rw [show T (WithLp.toLp 2
          (0, B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) = _ from hTspec.2 u v]
      rw [map_neg]
      congr 1
      exact Prod.ext (congrArg Neg.neg
        (externalTensorL2Equiv_smooth μ ν h₁ k₀ u
          ((Q.metricFormalAdjoint k₀ k₁).toLinearMap v)).symm)
        (externalTensorL2Equiv_smooth μ ν h₀ k₁
          ((P.metricFormalAdjoint h₀ h₁).toLinearMap u) v).symm
  -- Both closures contain exactly the same specified smooth graph columns.
  have hSimage : S.map Φ.toLinearMap ≤ L.range := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ (⟨⟨u, v⟩, rfl⟩ | ⟨⟨u, v⟩, rfl⟩)
    · exact ⟨iA (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)), hc₀ u v⟩
    · exact ⟨iB (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v)), hc₁ u v⟩
  have hfirst (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      L (iA (A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v))) ∈ G.graph := by
    rw [hc₀, hGgraph, hD]
    exact ⟨c₀ (u, v), S.le_topologicalClosure
      (Submodule.subset_span (Or.inl ⟨(u, v), rfl⟩)), rfl⟩
  have hsecond (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := m) (r := s₁) F₁) :
      L (iB (B.smoothToSobolev 1 (externalTensorSection E₁ F₁ u v))) ∈ G.graph := by
    rw [hc₁, hGgraph, hD]
    exact ⟨c₁ (u, v), S.le_topologicalClosure
      (Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩)), rfl⟩
  apply le_antisymm
  · rw [hGgraph, hD]
    exact (S.topologicalClosure_map Φ.toContinuousLinearMap).trans
      ((S.map Φ.toLinearMap).topologicalClosure_minimal hSimage hLclosed)
  · -- H1 density applies separately in the two columns and then to their direct sum.
    have hA (u : A.SobolevSpace 1) : L (iA u) ∈ G.graph := by
      have hs : Submodule.span ℂ
          (Set.range fun z : smoothSections (n := n) (r := r₀) E₀ ×
            smoothSections (n := m) (r := s₀) F₀ ↦
            A.smoothToSobolev 1 (externalTensorSection E₀ F₀ z.1 z.2)) ≤
          G.graph.comap (L.comp iA).toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨v, w⟩, rfl⟩
        exact hfirst v w
      exact (hGclosed.preimage (L.comp iA).continuous).closure_subset_iff.mpr hs
        (dense_span_externalTensorH1 (E := E₀) (F := F₀) A u)
    have hB (u : B.SobolevSpace 1) : L (iB u) ∈ G.graph := by
      have hs : Submodule.span ℂ
          (Set.range fun z : smoothSections (n := n) (r := r₁) E₁ ×
            smoothSections (n := m) (r := s₁) F₁ ↦
            B.smoothToSobolev 1 (externalTensorSection E₁ F₁ z.1 z.2)) ≤
          G.graph.comap (L.comp iB).toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨v, w⟩, rfl⟩
        exact hsecond v w
      exact (hGclosed.preimage (L.comp iB).continuous).closure_subset_iff.mpr hs
        (dense_span_externalTensorH1 (E := E₁) (F := F₁) B u)
    rintro z ⟨u, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := inEq.symm.surjective u
    have hsplit : inEq.symm (x, y) = iA x + iB y := by
      change WithLp.toLp 2 (x, y) = WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (0, y)
      rw [← WithLp.toLp_add]
      simp
    rw [hsplit, map_add]
    exact G.graph.add_mem (hA x) (hB y)


set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the product Sobolev realization and closed graph comparisons.
/-- The original tensor kernel inclusion identifies precisely the entire geometric kernel. -/
theorem gradedProductL2Operator_kernel_decomposition :
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
    let g₀₀ := externalTensorMetric h₀ k₀
    let g₁₁ := externalTensorMetric h₁ k₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₁ k₁)
    let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₀ k₁)
    let P₀ := P.metricL2ClosedRealization h₀ h₁
    let Q₀ := Q.metricL2ClosedRealization k₀ k₁
    let I := Ueven.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (gradedTensorKernelInclusion P₀ Q₀)
    Function.Injective I ∧
      I.toLinearMap.range = (gradedProductL2Operator h₀ h₁ k₀ k₁ P Q).ker := by
  /- Use dense closed factor realizations and the whole-domain tensor kernel
  identity. Transport that actual inclusion through the same even geometric
  unitary used in gradedProductL2Operator. Both injectivity and the exact range
  are preserved. No ellipticity is needed for this closed-operator identity.
  Under the ellipticity hypotheses of the H1 graph theorem, the existing
  formal-adjoint comparison additionally identifies these adjoint kernels
  with the original geometric formal-adjoint kernels. No unrelated vector-space
  isomorphism replaces the natural subspace inclusions. -/
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
  let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₁ k₁)
  let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₀ k₁)
  let P₀ := P.metricL2ClosedRealization h₀ h₁
  let Q₀ := Q.metricL2ClosedRealization k₀ k₁
  let D := gradedTensorOperator P₀ Q₀
  let G := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
  let I := Ueven.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (gradedTensorKernelInclusion P₀ Q₀)
  change Function.Injective I ∧ I.toLinearMap.range = G.ker
  -- Apply the closed tensor kernel theorem to the same two metric realizations.
  have hP₀ := P.metricL2ClosedRealization_realization h₀ h₁
  have hQ₀ := Q.metricL2ClosedRealization_realization k₀ k₁
  obtain ⟨hinj, hrange⟩ := gradedTensorKernelInclusion_decomposition P₀ Q₀
    hP₀.2.2 hQ₀.2.2 hP₀.2.1 hQ₀.2.1
  refine ⟨Ueven.injective.comp hinj, ?_⟩
  -- The original geometric operator conjugates the same graph by these two unitaries.
  have hkernel (x) : x ∈ G.ker ↔ Ueven.symm x ∈ D.ker := by
    constructor
    · intro hx
      obtain ⟨u, rfl, hu⟩ := G.mem_ker_iff.mp hx
      let v : D.domain := ⟨Ueven.symm u.val, u.property⟩
      refine D.mem_ker_iff.mpr ⟨v, rfl, ?_⟩
      apply Uodd.injective
      exact hu.trans (map_zero Uodd).symm
    · intro hx
      obtain ⟨v, hv, hvalue⟩ := D.mem_ker_iff.mp hx
      have hdomain : x ∈ G.domain := by
        change Ueven.symm x ∈ D.domain
        exact hv ▸ v.property
      refine G.mem_ker_iff.mpr ⟨⟨x, hdomain⟩, rfl, ?_⟩
      change Uodd (D ⟨Ueven.symm x, hdomain⟩) = 0
      have hsub : (⟨Ueven.symm x, hdomain⟩ : D.domain) = v :=
        Subtype.ext hv
      rw [hsub, hvalue, map_zero]
  apply Submodule.ext
  intro x
  rw [hkernel, ← hrange]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    exact (Ueven.symm_apply_apply _).symm
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    exact (congrArg Ueven hv).trans (Ueven.apply_symm_apply x)


set_option linter.unusedVariables false in
set_option maxHeartbeats 2400000 in
-- Compare both original graph coordinates under the specified tensor unitaries.
/-- The actual range quotient has the natural odd tensor-kernel decomposition. -/
theorem gradedProductL2Operator_cokernel_decomposition (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
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
    let g₀₀ := externalTensorMetric h₀ k₀
    let g₁₁ := externalTensorMetric h₁ k₁
    let g₁₀ := externalTensorMetric h₁ k₀
    let g₀₁ := externalTensorMetric h₀ k₁
    let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₁ k₁)
    let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₀ k₁)
    let P₀ := P.metricL2ClosedRealization h₀ h₁
    let Q₀ := Q.metricL2ClosedRealization k₀ k₁
    let D := gradedTensorOperator P₀ Q₀
    let G := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
    IsClosed (G.toFun.range : Set
      (WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν)))) ∧
      ∃ (q : (_ ⧸ D.toFun.range) ≃ₗ[ℂ] (_ ⧸ G.toFun.range))
        (φ : WithLp 2 (HilbertTensorProduct P₀.adjoint.ker Q₀.ker ×
          HilbertTensorProduct P₀.ker Q₀.adjoint.ker) ≃ₗ[ℂ] (_ ⧸ G.toFun.range)),
        (∀ z, q (D.toFun.range.mkQ z) = G.toFun.range.mkQ (Uodd z)) ∧
          ∀ w, φ w = q (gradedTensorCokernelMap P₀ Q₀ w) := by
  /- Stage 1: ellipticity on compact factors gives closed original factor
  ranges. The tensor cokernel theorem therefore gives closed range of the
  closed matrix and bijectivity of its specific odd inclusion followed by mkQ.
  Stage 2: the same odd geometric unitary transports that range onto the
  original geometric operator range. It induces the displayed quotient map q
  on every original representative, so the geometric range is also closed.
  Stage 3: compose q with the original gradedTensorCokernelMap to obtain φ.
  Its displayed formula fixes the natural kernel-pair decomposition and exact
  quotient maps. Never replace either actual range by its closure. -/
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
  let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₁ k₁)
  let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₀ k₁)
  let P₀ := P.metricL2ClosedRealization h₀ h₁
  let Q₀ := Q.metricL2ClosedRealization k₀ k₁
  let D := gradedTensorOperator P₀ Q₀
  let G := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
  change IsClosed (G.toFun.range : Set
      (WithLp 2 ((externalTensorMetric h₁ k₀).L2SectionSpace (μ.prod ν) ×
        (externalTensorMetric h₀ k₁).L2SectionSpace (μ.prod ν)))) ∧
    ∃ (q : (_ ⧸ D.toFun.range) ≃ₗ[ℂ] (_ ⧸ G.toFun.range))
      (φ : WithLp 2 (HilbertTensorProduct P₀.adjoint.ker Q₀.ker ×
        HilbertTensorProduct P₀.ker Q₀.adjoint.ker) ≃ₗ[ℂ] (_ ⧸ G.toFun.range)),
      (∀ z, q (D.toFun.range.mkQ z) = G.toFun.range.mkQ (Uodd z)) ∧
        ∀ w, φ w = q (gradedTensorCokernelMap P₀ Q₀ w)
  -- Closed elliptic factor ranges supply the actual tensor quotient, with its specified map.
  have hP₀ := P.metricL2ClosedRealization_realization h₀ h₁
  have hQ₀ := Q.metricL2ClosedRealization_realization k₀ k₁
  obtain ⟨hclosed, hbij⟩ := gradedTensorCokernelMap_decomposition P₀ Q₀
    hP₀.2.2 hQ₀.2.2 hP₀.2.1 hQ₀.2.1
    (P.closed_range_finite_metricL2ClosedRealization h₀ h₁ hP).1
    (Q.closed_range_finite_metricL2ClosedRealization k₀ k₁ hQ).1
  -- The odd unitary maps the exact tensor range onto the geometric range.
  have hrange : D.toFun.range.map Uodd.toLinearMap = G.toFun.range := by
    apply Submodule.ext
    intro y
    constructor
    · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
      have hdom : Ueven v.val ∈ G.domain := by
        change Ueven.symm (Ueven v.val) ∈ D.domain
        simpa only [Ueven.symm_apply_apply] using v.property
      refine ⟨⟨Ueven v.val, hdom⟩, ?_⟩
      change Uodd (D ⟨Ueven.symm (Ueven v.val), hdom⟩) = Uodd (D v)
      congr 2
      exact Subtype.ext (Ueven.symm_apply_apply v.val)
    · rintro ⟨u, rfl⟩
      let v : D.domain := ⟨Ueven.symm u.val, u.property⟩
      exact ⟨D v, ⟨v, rfl⟩, rfl⟩
  have hGclosed : IsClosed (G.toFun.range : Set
      (WithLp 2 ((externalTensorMetric h₁ k₀).L2SectionSpace (μ.prod ν) ×
        (externalTensorMetric h₀ k₁).L2SectionSpace (μ.prod ν)))) := by
    rw [← hrange]
    change IsClosed (Uodd '' (D.toFun.range : Set _))
    exact Uodd.toHomeomorph.isClosedMap _ hclosed
  -- The induced quotient equivalence has the prescribed value on every representative.
  let q := Submodule.Quotient.equiv D.toFun.range G.toFun.range Uodd.toLinearEquiv hrange
  let φ := (LinearEquiv.ofBijective (gradedTensorCokernelMap P₀ Q₀) hbij).trans q
  exact ⟨hGclosed, q, φ, fun _ ↦ rfl, fun _ ↦ rfl⟩

end AtiyahSinger
