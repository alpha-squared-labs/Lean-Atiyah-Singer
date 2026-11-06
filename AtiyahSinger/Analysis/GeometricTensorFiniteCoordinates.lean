/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import AtiyahSinger.Analysis.GeometricTensorDomain

/-!
# Full finite coordinates under the original geometric tensor unitaries

Public module ID: M0664.

The existing whole-kernel inclusion and actual quotient equivalence transport
finite representations through the specified even and odd external tensor
unitaries. The action hypotheses are equations for those same unitaries on
the entire Hilbert spaces; no alternative coordinate identification is chosen.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory UniformSpace
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {G : Type*} [Group G] [TopologicalSpace G]

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Keep four native tensor structures and both specified geometric unitaries in one comparison.
/-- The original tensor unitaries transport both full finite representations. -/
theorem exists_gradedProductL2Operator_finite_coordinates (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
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
    let EvenH := WithLp 2 (HilbertTensorProduct (h₀.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
      HilbertTensorProduct (h₁.L2SectionSpace μ) (k₁.L2SectionSpace ν))
    let OddH := WithLp 2 (HilbertTensorProduct (h₁.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
      HilbertTensorProduct (h₀.L2SectionSpace μ) (k₁.L2SectionSpace ν))
    let EvenG := WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν))
    let OddG := WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν))
    let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₁ k₁)
    let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₀ k₁)
    let P₀ := P.metricL2ClosedRealization h₀ h₁
    let Q₀ := Q.metricL2ClosedRealization k₀ k₁
    let D := gradedTensorOperator P₀ Q₀
    let L := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
    ∀ (κ χ : FiniteContinuousRepresentation G)
      (A : G → EvenH →L[ℂ] EvenH) (B : G → OddH →L[ℂ] OddH)
      (ρ : G → EvenG →L[ℂ] EvenG) (τ : G → OddG →L[ℂ] OddG)
      (_hUeven : ∀ g v, Ueven (A g v) = ρ g (Ueven v))
      (_hUodd : ∀ g v, Uodd (B g v) = τ g (Uodd v))
      (e₀ : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] D.ker)
      (f₀ : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] (OddH ⧸ D.toFun.range))
      (_he₀ : ∀ g v, (e₀ (κ.representation g v)).val = A g (e₀ v).val)
      (_hf₀ : ∀ g v, f₀ (χ.representation g (f₀.symm (D.toFun.range.mkQ v))) =
        D.toFun.range.mkQ (B g v)),
      ∃ e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] L.ker,
        ∃ f : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] (OddG ⧸ L.toFun.range),
          (∀ g v, (e (κ.representation g v)).val = ρ g (e v).val) ∧
          ∀ g v, f (χ.representation g (f.symm (L.toFun.range.mkQ v))) =
            L.toFun.range.mkQ (τ g v) := by
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
  let g₀₀ := externalTensorMetric h₀ k₀
  let g₁₁ := externalTensorMetric h₁ k₁
  let g₁₀ := externalTensorMetric h₁ k₀
  let g₀₁ := externalTensorMetric h₀ k₁
  let EvenH := WithLp 2 (HilbertTensorProduct (h₀.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
    HilbertTensorProduct (h₁.L2SectionSpace μ) (k₁.L2SectionSpace ν))
  let OddH := WithLp 2 (HilbertTensorProduct (h₁.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
    HilbertTensorProduct (h₀.L2SectionSpace μ) (k₁.L2SectionSpace ν))
  let EvenG := WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν))
  let OddG := WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν))
  let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₁ k₁)
  let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
    (externalTensorL2Equiv μ ν h₀ k₁)
  let P₀ := P.metricL2ClosedRealization h₀ h₁
  let Q₀ := Q.metricL2ClosedRealization k₀ k₁
  let D := gradedTensorOperator P₀ Q₀
  let L := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
  dsimp only
  intro κ χ A B ρ τ hUeven hUodd e₀ f₀ he₀ hf₀
  -- Both whole kernels are images of the same completed even kernel inclusion.
  let I := gradedTensorKernelInclusion P₀ Q₀
  let J := Ueven.toLinearIsometry.toContinuousLinearMap.comp I
  have hP₀ := P.metricL2ClosedRealization_realization h₀ h₁
  have hQ₀ := Q.metricL2ClosedRealization_realization k₀ k₁
  obtain ⟨hI, hrI⟩ := gradedTensorKernelInclusion_decomposition P₀ Q₀
    hP₀.2.2 hQ₀.2.2 hP₀.2.1 hQ₀.2.1
  obtain ⟨hJ, hrJ⟩ := gradedProductL2Operator_kernel_decomposition h₀ h₁ k₀ k₁ P Q
  let i := (LinearEquiv.ofInjective I.toLinearMap hI).trans (LinearEquiv.ofEq _ _ hrI)
  let j := (LinearEquiv.ofInjective J.toLinearMap hJ).trans (LinearEquiv.ofEq _ _ hrJ)
  let k := i.symm.trans j
  have hk (v : D.ker) : (k v).val = Ueven v.val := by
    obtain ⟨w, rfl⟩ := i.surjective v
    change (j (i.symm (i w))).val = Ueven (i w).val
    rw [i.symm_apply_apply]
    rfl
  -- The existing odd comparison uses the actual range quotient and the same Uodd.
  obtain ⟨hclosed, q, φ, hq, hφ⟩ :=
    gradedProductL2Operator_cokernel_decomposition h₀ h₁ k₀ k₁ P Q hP hQ
  let e := e₀.trans k
  let f := f₀.trans q
  refine ⟨e, f, ?_, ?_⟩
  · intro g v
    change (k (e₀ (κ.representation g v))).val = ρ g (k (e₀ v)).val
    rw [hk, hk, he₀, hUeven]
  · intro g v
    have hv : f.symm (L.toFun.range.mkQ v) =
        f₀.symm (D.toFun.range.mkQ (Uodd.symm v)) := by
      have h := hq (Uodd.symm v)
      rw [Uodd.apply_symm_apply] at h
      rw [← h]
      change f₀.symm (q.symm (q (D.toFun.range.mkQ (Uodd.symm v)))) =
        f₀.symm (D.toFun.range.mkQ (Uodd.symm v))
      exact congrArg f₀.symm (q.symm_apply_apply (D.toFun.range.mkQ (Uodd.symm v)))
    rw [hv]
    change q (f₀ (χ.representation g (f₀.symm (D.toFun.range.mkQ (Uodd.symm v))))) = _
    rw [hf₀, hq, hUodd, Uodd.apply_symm_apply]

end AtiyahSinger
