/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphFredholmIndex
public import AtiyahSinger.Analysis.GeometricTensorFiniteCoordinates
public import AtiyahSinger.Analysis.GeometricTensorGraph
public import AtiyahSinger.Analysis.GradedTensorKernelRepresentations

/-!
# The equivariant geometric tensor Fredholm operator on its original H1 graph

Public module ID: M0515.

The four actual factor kernel actions determine the full geometric tensor
index. The original completed tensor unitaries transport those coordinates,
and the specified geometric H1 realization identifies the fixed Hilbert graph
domain. This supplies the source, actions and reference Fredholm operator for
the native cutoff perturbation, retaining all four metrics and both densities.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory UniformSpace
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

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
set_option maxHeartbeats 16000000 in
-- Assemble the four finite actions, full geometric graph and exact original H1 realization.
/-- The full geometric tensor index is realized on its same invariant Hilbert graph domain. -/
theorem exists_gradedProductL2Operator_graph_fredholm (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
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
    let EvenG := WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν))
    let OddG := WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν))
    let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₁ k₁)
    let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₀ k₁)
    let P₀ := P.metricL2ClosedRealization h₀ h₁
    let Q₀ := Q.metricL2ClosedRealization k₀ k₁
    let L := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
    ∀ (A₀ : G → h₀.L2SectionSpace μ →L[ℂ] h₀.L2SectionSpace μ)
      (A₁ : G → h₁.L2SectionSpace μ →L[ℂ] h₁.L2SectionSpace μ)
      (B₀ : G → k₀.L2SectionSpace ν →L[ℂ] k₀.L2SectionSpace ν)
      (B₁ : G → k₁.L2SectionSpace ν →L[ℂ] k₁.L2SectionSpace ν)
      (_hPcov : ∀ g z, z ∈ P₀.graph → (A₀ g z.1, A₁ g z.2) ∈ P₀.graph)
      (_hPacov : ∀ g z, z ∈ P₀.adjoint.graph → (A₁ g z.1, A₀ g z.2) ∈ P₀.adjoint.graph)
      (_hQcov : ∀ g z, z ∈ Q₀.graph → (B₀ g z.1, B₁ g z.2) ∈ Q₀.graph)
      (_hQacov : ∀ g z, z ∈ Q₀.adjoint.graph → (B₁ g z.1, B₀ g z.2) ∈ Q₀.adjoint.graph)
      (ρ : ContRepresentation ℂ G EvenG) (τ : ContRepresentation ℂ G OddG)
      (_hρ : Continuous (fun p : G × EvenG ↦ ρ p.1 p.2))
      (_hτ : Continuous (fun p : G × OddG ↦ τ p.1 p.2))
      (ρI : G →* (EvenG ≃ₗᵢ[ℂ] EvenG)) (τI : G →* (OddG ≃ₗᵢ[ℂ] OddG))
      (_hρI : ∀ g v, ρI g v = ρ g v) (_hτI : ∀ g v, τI g v = τ g v)
      (_hUeven : ∀ g v, Ueven (WithLp.toLp 2
        (hilbertTensorMap (A₀ g) (B₀ g) (WithLp.ofLp v).1,
          hilbertTensorMap (A₁ g) (B₁ g) (WithLp.ofLp v).2)) = ρ g (Ueven v))
      (_hUodd : ∀ g v, Uodd (WithLp.toLp 2
        (hilbertTensorMap (A₁ g) (B₀ g) (WithLp.ofLp v).1,
          hilbertTensorMap (A₀ g) (B₁ g) (WithLp.ofLp v).2)) = τ g (Uodd v))
      (ρ₀ ρ₁ σ₀ σ₁ : FiniteContinuousRepresentation G)
      (e₀ : (Fin ρ₀.dimension → ℂ) ≃ₗ[ℂ] P₀.ker)
      (e₁ : (Fin ρ₁.dimension → ℂ) ≃ₗ[ℂ] P₀.adjoint.ker)
      (f₀ : (Fin σ₀.dimension → ℂ) ≃ₗ[ℂ] Q₀.ker)
      (f₁ : (Fin σ₁.dimension → ℂ) ≃ₗ[ℂ] Q₀.adjoint.ker)
      (_he₀ : ∀ g v, (e₀ (ρ₀.representation g v)).val = A₀ g (e₀ v).val)
      (_he₁ : ∀ g v, (e₁ (ρ₁.representation g v)).val = A₁ g (e₁ v).val)
      (_hf₀ : ∀ g v, (f₀ (σ₀.representation g v)).val = B₀ g (f₀ v).val)
      (_hf₁ : ∀ g v, (f₁ (σ₁.representation g v)).val = B₁ g (f₁ v).val)
      (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
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
    let Γ := L.graph.comap (WithLp.linearEquiv 2 ℂ (EvenG × OddG)).toLinearMap
    let FΓ := (WithLp.sndL 2 ℂ EvenG OddG).comp Γ.subtypeL
    let κ := (ρ₀.tensor σ₀).directSum (ρ₁.tensor σ₁)
    let χ := (ρ₁.tensor σ₀).directSum (ρ₀.tensor σ₁)
    ∃ (γ : ContRepresentation ℂ G Γ)
      (hγ : Continuous (fun p : G × Γ ↦ γ p.1 p.2)),
      ∃ γI : G →* (Γ ≃ₗᵢ[ℂ] Γ), (∀ g v, γI g v = γ g v) ∧
        (∀ g v, (γ g v).val = WithLp.toLp 2
          (ρ g (WithLp.ofLp v.val).1, τ g (WithLp.ofLp v.val).2)) ∧
        ∃ Φ : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1) ≃L[ℂ] Γ,
          (∀ x, (Φ x).val = WithLp.toLp 2 (J x, T x)) ∧
          ∃ hFg : ∀ g, FΓ.comp (γ g) = (τ g).comp FΓ,
            ∃ hF : FΓ.IsFredholm,
              equivariantFredholmIndex γ τ hγ _hτ FΓ hFg hF =
                finiteRepresentationClass κ - finiteRepresentationClass χ := by
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
  intro A₀ A₁ B₀ B₁ hPcov hPacov hQcov hQacov ρ τ hρ hτ ρI τI hρI hτI
    hUeven hUodd ρ₀ ρ₁ σ₀ σ₁ e₀ e₁ f₀ f₁ he₀ he₁ hf₀ hf₁ A B
  let J₀ := (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  let J₁ := (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).toContinuousLinearMap.comp
    (B.sobolevInclusion 1 0 (by norm_num))
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    ((J₀.prodMap J₁).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
  let T := gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B
  let Γ := L.graph.comap (WithLp.linearEquiv 2 ℂ (EvenG × OddG)).toLinearMap
  let FΓ := (WithLp.sndL 2 ℂ EvenG OddG).comp Γ.subtypeL
  let κ := (ρ₀.tensor σ₀).directSum (ρ₁.tensor σ₁)
  let χ := (ρ₁.tensor σ₀).directSum (ρ₀.tensor σ₁)
  let eA := WithLp.prodContinuousLinearEquiv 2 ℂ
    (HilbertTensorProduct (h₀.L2SectionSpace μ) (k₀.L2SectionSpace ν))
    (HilbertTensorProduct (h₁.L2SectionSpace μ) (k₁.L2SectionSpace ν))
  let oA := WithLp.prodContinuousLinearEquiv 2 ℂ
    (HilbertTensorProduct (h₁.L2SectionSpace μ) (k₀.L2SectionSpace ν))
    (HilbertTensorProduct (h₀.L2SectionSpace μ) (k₁.L2SectionSpace ν))
  let Ae (g : G) := eA.symm.toContinuousLinearMap.comp
    (((hilbertTensorMap (A₀ g) (B₀ g)).prodMap
      (hilbertTensorMap (A₁ g) (B₁ g))).comp eA.toContinuousLinearMap)
  let Ao (g : G) := oA.symm.toContinuousLinearMap.comp
    (((hilbertTensorMap (A₁ g) (B₀ g)).prodMap
      (hilbertTensorMap (A₀ g) (B₁ g))).comp oA.toContinuousLinearMap)
  have hPc := P.metricL2ClosedRealization_realization h₀ h₁
  have hQc := Q.metricL2ClosedRealization_realization k₀ k₁
  have hDc := gradedTensorOperator_realization P₀ Q₀ hPc.2.2 hQc.2.2 hPc.2.1 hQc.2.1
  let C := Ueven.toContinuousLinearEquiv.prodCongr Uodd.toContinuousLinearEquiv
  have hLgraph : L.graph = D.graph.map C.toLinearMap :=
    gradedProductL2Operator_graph h₀ h₁ k₀ k₁ P Q
  have hLc : L.IsClosed := by
    rw [LinearPMap.IsClosed, hLgraph]
    exact C.toHomeomorph.isClosedMap _ hDc.2.2.1
  -- Graph naturality includes the two signed columns and their full closure.
  have hLcov (g : G) (z : EvenG × OddG) (hz : z ∈ L.graph) :
      (ρ g z.1, τ g z.2) ∈ L.graph := by
    rw [hLgraph] at hz ⊢
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨(Ae g w.1, Ao g w.2), ?_, ?_⟩
    · exact gradedTensorOperator_graph_map P₀ Q₀ hPc.2.2 hQc.2.2 hPc.2.1 hQc.2.1
        (A₀ g) (A₁ g) (B₀ g) (B₁ g) (hPcov g) (hPacov g) (hQcov g) (hQacov g) w hw
    · exact Prod.ext (hUeven g w.1) (hUodd g w.2)
  have hLinv (g : G) (z : EvenG × OddG) :
      (ρI g z.1, τI g z.2) ∈ L.graph ↔ z ∈ L.graph := by
    rw [hρI, hτI]
    constructor
    · intro hz
      have hw := hLcov g⁻¹ _ hz
      have hρcancel : ρ g⁻¹ (ρ g z.1) = z.1 := by
        change ((ρ g⁻¹) * (ρ g)) z.1 = _
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      have hτcancel : τ g⁻¹ (τ g z.2) = z.2 := by
        change ((τ g⁻¹) * (τ g)) z.2 = _
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      simpa only [hρcancel, hτcancel] using hw
    · exact hLcov g z
  obtain ⟨γI, hγI, hγIv⟩ := LinearPMap.exists_graphIsometryRepresentation L ρI τI
    (hρ.congr (fun p ↦ (hρI p.1 p.2).symm))
    (hτ.congr (fun p ↦ (hτI p.1 p.2).symm)) hLinv
  let γ : ContRepresentation ℂ G Γ := ⟨{
    toFun := fun g ↦ (γI g).toLinearIsometry.toContinuousLinearMap
    map_one' := by
      apply ContinuousLinearMap.ext
      intro v
      change γI 1 v = v
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro v
      change γI (g * h) v = γI g (γI h v)
      rw [map_mul]
      rfl }⟩
  have hγ : Continuous (fun p : G × Γ ↦ γ p.1 p.2) := hγI
  have hγv (g : G) (v : Γ) : (γ g v).val = WithLp.toLp 2
      (ρ g (WithLp.ofLp v.val).1, τ g (WithLp.ofLp v.val).2) := by
    change (γI g v).val = _
    rw [hγIv, hρI, hτI]
  -- The original product H1 norm identifies this graph; its embedding remains injective.
  have hJ₀ : Function.Injective J₀ :=
    (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).injective.comp
      (A.sobolevInclusion_injective 1 0 (by norm_num))
  have hJ₁ : Function.Injective J₁ :=
    (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).injective.comp
      (B.sobolevInclusion_injective 1 0 (by norm_num))
  have hJ : Function.Injective J := by
    intro x y hxy
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply hJ₀
      exact congrArg (fun z : EvenG ↦ (WithLp.ofLp z).1) hxy
    · apply hJ₁
      exact congrArg (fun z : EvenG ↦ (WithLp.ofLp z).2) hxy
  have hGraphSobolev : L.graph = (J.prod T).toLinearMap.range :=
    gradedProductL2Operator_graph_sobolev h₀ h₁ k₀ k₁ P Q hP hQ A B
  -- Build the same graph equivalence in these fixed local norm instances.
  have hΓclosed : IsClosed (Γ : Set (WithLp 2 (EvenG × OddG))) :=
    hLc.preimage (WithLp.prod_continuous_ofLp 2 EvenG OddG)
  let : CompleteSpace Γ := hΓclosed.completeSpace_coe
  let CΓ := (WithLp.prodContinuousLinearEquiv 2 ℂ EvenG OddG).symm.toContinuousLinearMap.comp
    (J.prod T)
  have hCΓ (x : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1)) : CΓ x ∈ Γ := by
    change (J x, T x) ∈ L.graph
    rw [hGraphSobolev]
    exact ⟨x, rfl⟩
  let φ := CΓ.codRestrict Γ hCΓ
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      apply hJ
      exact congrArg (fun z : Γ ↦ (WithLp.ofLp z.val).1) hxy
    · intro z
      have hz : WithLp.ofLp z.val ∈ (J.prod T).toLinearMap.range := by
        rw [← hGraphSobolev]
        exact z.property
      obtain ⟨x, hx⟩ := hz
      refine ⟨x, Subtype.ext ?_⟩
      apply WithLp.ofLp_injective
      exact hx
  let Φ : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1) ≃L[ℂ] Γ :=
    ContinuousLinearEquiv.ofBijective φ (LinearMap.ker_eq_bot.mpr hφ.1)
      (LinearMap.range_eq_top.mpr hφ.2)
  have hΦ (x : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1)) :
      (Φ x).val = WithLp.toLp 2 (J x, T x) := rfl
  -- The same four actual finite representations give the whole kernel and quotient.
  obtain ⟨eD, fD, heD, hfD⟩ := exists_gradedTensorKernelCokernel_coordinates P₀ Q₀
    hPc.2.2 hQc.2.2 hPc.2.1 hQc.2.1
    (P.closed_range_finite_metricL2ClosedRealization h₀ h₁ hP).1
    (Q.closed_range_finite_metricL2ClosedRealization k₀ k₁ hQ).1
    A₀ A₁ B₀ B₁ hPcov hPacov hQcov hQacov
    ρ₀ ρ₁ σ₀ σ₁ e₀ e₁ f₀ f₁ he₀ he₁ hf₀ hf₁
  obtain ⟨eL, fL, heL, hfL⟩ := exists_gradedProductL2Operator_finite_coordinates
    h₀ h₁ k₀ k₁ P Q hP hQ κ χ Ae Ao (fun g ↦ ρ g) (fun g ↦ τ g)
    hUeven hUodd eD fD heD hfD
  have hLrange := (gradedProductL2Operator_cokernel_decomposition
    h₀ h₁ k₀ k₁ P Q hP hQ).1
  obtain ⟨hFg, hF, hindex⟩ := LinearPMap.exists_graphFredholmIndex L hLc hLrange ρ τ hτ
    κ χ eL fL heL hfL γ hγ hγv
  exact ⟨γ, hγ, γI, (fun _ _ ↦ rfl), hγv, Φ, hΦ, hFg, hF, hindex⟩

end AtiyahSinger
