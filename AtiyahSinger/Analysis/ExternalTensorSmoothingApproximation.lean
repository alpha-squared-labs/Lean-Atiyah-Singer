/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorL2
public import AtiyahSinger.Analysis.SmoothProjectionApproximation

/-!
# Smooth approximation of bounded factorwise operators

Public module ID: M0617.

A bounded factor operator has a bounded exterior tensor action on the original
product L2 spaces. Its H1 restriction is approximated by actual smooth kernels
using finite spans of original smooth tensors. The factorwise operator itself
is not asserted to be an isotropic product pseudodifferential operator.

This supplies the remainder regularization in SG III.13.5. The construction
retains the specified tensor bundle, Hermitian metrics and product density.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  {μ : Measure M} {ν : Measure N}
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]
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

/-- The actual bounded factorwise tensor action has genuine smooth-kernel approximants
in operator norm from the original geometric H1 space. -/
theorem exists_externalTensorL2_smoothing_approximation
    (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
    (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
    (k : SmoothHermitianMetric (n := m) (r := s) F)
    (S : smoothSections (n := n) (r := r₀) E₀ →ₗ[ℂ]
      smoothSections (n := n) (r := r₁) E₁)
    (T : h₀.L2SectionSpace μ →L[ℂ] h₁.L2SectionSpace μ)
    (hT : ∀ u : smoothSections (n := n) (r := r₀) E₀,
      T (h₀.smoothToL2 μ u) = h₁.smoothToL2 μ (S u)) (ε : ℝ) (hε : 0 < ε) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
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
    let g₀ := externalTensorMetric h₀ k
    let g₁ := externalTensorMetric h₁ k
    let U₀ := externalTensorL2Equiv μ ν h₀ k
    let U₁ := externalTensorL2Equiv μ ν h₁ k
    let Tprod := U₁.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((TensorProduct.mapL T (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion.comp
        U₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    ∀ A : SmoothBundlePresentation (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F),
      let I := (g₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
        (A.sobolevInclusion 1 0 (by norm_num))
      ∃ J : smoothSections (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F) →ₗ[ℂ]
          smoothSections (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F),
        IsSmoothingOperator (μ.prod ν) J ∧
          ∃ R : g₀.L2SectionSpace (μ.prod ν) →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
            (∀ u : smoothSections (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F),
              R (g₀.smoothToL2 (μ.prod ν) u) = g₁.smoothToL2 (μ.prod ν) (J u)) ∧
            ‖Tprod.comp I - R.comp I‖ < ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
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
  dsimp only
  intro A
  let g₀ := externalTensorMetric h₀ k
  let g₁ := externalTensorMetric h₁ k
  let U₀ := externalTensorL2Equiv μ ν h₀ k
  let U₁ := externalTensorL2Equiv μ ν h₁ k
  let Tprod := U₁.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((TensorProduct.mapL T (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion.comp
      U₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let D : Submodule ℂ (g₀.SmoothL2Section (μ.prod ν)) := Submodule.span ℂ
    (Set.range fun p : smoothSections (n := n) (r := r₀) E₀ ×
      smoothSections (n := m) (r := s) F ↦ externalTensorSection E₀ F p.1 p.2)
  -- The core consists of finite sums of the same original smooth tensor sections.
  have hD : DenseRange (fun u : D ↦ g₀.smoothToL2 (μ.prod ν) u.val) := by
    have hd := dense_span_externalTensorL2 (E := E₀) (F := F) (μ.prod ν) g₀
    let j : D →ₗ[ℂ] g₀.L2SectionSpace (μ.prod ν) :=
      (g₀.smoothToL2 (μ.prod ν)).comp D.subtype
    change DenseRange j
    apply hd.mono
    change _ ≤ j.range
    apply Submodule.span_le.mpr
    rintro x ⟨⟨a, b⟩, rfl⟩
    refine ⟨⟨externalTensorSection E₀ F a b, Submodule.subset_span ?_⟩, rfl⟩
    exact ⟨(a, b), rfl⟩
  have hpure (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s) F) :
      Tprod (g₀.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F u v)) =
        g₁.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F (S u) v) := by
    -- The selected unitaries and completed tensor map retain their pure-section formula.
    rw [← externalTensorL2Equiv_smooth μ ν h₀ k u v]
    change U₁ ((TensorProduct.mapL T (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion
      (U₀.symm (U₀ _))) = _
    rw [U₀.symm_apply_apply]
    change U₁ ((TensorProduct.mapL T (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion
      (↑(h₀.smoothToL2 μ u ⊗ₜ[ℂ] k.smoothToL2 ν v))) = _
    simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
      ContinuousLinearMap.id_apply, hT]
    exact externalTensorL2Equiv_smooth μ ν h₁ k (S u) v
  have hsmooth (u : D) : ∃ v : smoothSections (n := n + m) (r := r₁ * s)
      (externalTensorFiber E₁ F),
      Tprod (g₀.smoothToL2 (μ.prod ν) u.val) = g₁.smoothToL2 (μ.prod ν) v := by
    suffices hall : ∀ x : g₀.SmoothL2Section (μ.prod ν), x ∈ D →
        ∃ v : smoothSections (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F),
          Tprod (g₀.smoothToL2 (μ.prod ν) x) = g₁.smoothToL2 (μ.prod ν) v from
      hall u.val u.property
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      exact ⟨externalTensorSection E₁ F (S a) b, hpure a b⟩
    | zero => exact ⟨0, by simp only [map_zero]⟩
    | add x y hx hy hxx hyy =>
      obtain ⟨a, ha⟩ := hxx
      obtain ⟨b, hb⟩ := hyy
      exact ⟨a + b, by simp only [map_add, ha, hb]⟩
    | smul c x hx hxx =>
      obtain ⟨a, ha⟩ := hxx
      exact ⟨c • a, by simp only [map_smul, ha]⟩
  -- Finite projections use only this core. Their actual smooth outputs give
  -- smooth kernels through the original L2 pairing and all-order geometric duality.
  exact exists_smoothing_approximation_of_smooth_core g₀ g₁ A D hD Tprod hsmooth ε hε

end AtiyahSinger
