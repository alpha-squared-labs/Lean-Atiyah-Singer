/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorL2
public import AtiyahSinger.Analysis.SmoothProjectionApproximation

/-!
# Smooth approximation of bounded right-factor operators

Public module ID: M0928.

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

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space N] [T2Space M] [SecondCountableTopology N] [SecondCountableTopology M]
  [CompactSpace N] [CompactSpace M]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} {ν : Measure N}
  [IsSmoothPositiveMeasure (n := m) ν] [IsSmoothPositiveMeasure (n := n) μ]
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

/-- The actual bounded factorwise tensor action has genuine smooth-kernel approximants
in operator norm from the original geometric H1 space. -/
theorem exists_rightExternalTensorL2_smoothing_approximation
    (h₀ : SmoothHermitianMetric (n := m) (r := s₀) F₀)
    (h₁ : SmoothHermitianMetric (n := m) (r := s₁) F₁)
    (k : SmoothHermitianMetric (n := n) (r := r) E)
    (S : smoothSections (n := m) (r := s₀) F₀ →ₗ[ℂ]
      smoothSections (n := m) (r := s₁) F₁)
    (T : h₀.L2SectionSpace ν →L[ℂ] h₁.L2SectionSpace ν)
    (hT : ∀ v : smoothSections (n := m) (r := s₀) F₀,
      T (h₀.smoothToL2 ν v) = h₁.smoothToL2 ν (S v)) (ε : ℝ) (hε : 0 < ε) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
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
    let g₀ := externalTensorMetric k h₀
    let g₁ := externalTensorMetric k h₁
    let U₀ := externalTensorL2Equiv μ ν k h₀
    let U₁ := externalTensorL2Equiv μ ν k h₁
    let Tprod := U₁.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) T).completion.comp
        U₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    ∀ A : SmoothBundlePresentation (n := n + m) (r := r * s₀) (externalTensorFiber E F₀),
      let I := (g₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
        (A.sobolevInclusion 1 0 (by norm_num))
      ∃ J : smoothSections (n := n + m) (r := r * s₀) (externalTensorFiber E F₀) →ₗ[ℂ]
          smoothSections (n := n + m) (r := r * s₁) (externalTensorFiber E F₁),
        IsSmoothingOperator (μ.prod ν) J ∧
          ∃ R : g₀.L2SectionSpace (μ.prod ν) →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
            (∀ v : smoothSections (n := n + m) (r := r * s₀) (externalTensorFiber E F₀),
              R (g₀.smoothToL2 (μ.prod ν) v) = g₁.smoothToL2 (μ.prod ν) (J v)) ∧
            ‖Tprod.comp I - R.comp I‖ < ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
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
  dsimp only
  intro A
  let g₀ := externalTensorMetric k h₀
  let g₁ := externalTensorMetric k h₁
  let U₀ := externalTensorL2Equiv μ ν k h₀
  let U₁ := externalTensorL2Equiv μ ν k h₁
  let Tprod := U₁.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) T).completion.comp
      U₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let D : Submodule ℂ (g₀.SmoothL2Section (μ.prod ν)) := Submodule.span ℂ
    (Set.range fun p : smoothSections (n := n) (r := r) E ×
      smoothSections (n := m) (r := s₀) F₀ ↦ externalTensorSection E F₀ p.1 p.2)
  -- The core consists of finite sums of the same original smooth tensor sections.
  have hD : DenseRange (fun v : D ↦ g₀.smoothToL2 (μ.prod ν) v.val) := by
    have hd := dense_span_externalTensorL2 (E := E) (F := F₀) (μ.prod ν) g₀
    let j : D →ₗ[ℂ] g₀.L2SectionSpace (μ.prod ν) :=
      (g₀.smoothToL2 (μ.prod ν)).comp D.subtype
    change DenseRange j
    apply hd.mono
    change _ ≤ j.range
    apply Submodule.span_le.mpr
    rintro x ⟨⟨a, b⟩, rfl⟩
    refine ⟨⟨externalTensorSection E F₀ a b, Submodule.subset_span ?_⟩, rfl⟩
    exact ⟨(a, b), rfl⟩
  have hpure (u : smoothSections (n := n) (r := r) E)
      (v : smoothSections (n := m) (r := s₀) F₀) :
      Tprod (g₀.smoothToL2 (μ.prod ν) (externalTensorSection E F₀ u v)) =
        g₁.smoothToL2 (μ.prod ν) (externalTensorSection E F₁ u (S v)) := by
    -- The selected unitaries and completed tensor map retain their pure-section formula.
    rw [← externalTensorL2Equiv_smooth μ ν k h₀ u v]
    change U₁ ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) T).completion
      (U₀.symm (U₀ _))) = _
    rw [U₀.symm_apply_apply]
    change U₁ ((TensorProduct.mapL (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)) T).completion
      (↑(k.smoothToL2 μ u ⊗ₜ[ℂ] h₀.smoothToL2 ν v))) = _
    simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
      ContinuousLinearMap.id_apply, hT]
    exact externalTensorL2Equiv_smooth μ ν k h₁ u (S v)
  have hsmooth (v : D) : ∃ u : smoothSections (n := n + m) (r := r * s₁)
      (externalTensorFiber E F₁),
      Tprod (g₀.smoothToL2 (μ.prod ν) v.val) = g₁.smoothToL2 (μ.prod ν) u := by
    suffices hall : ∀ x : g₀.SmoothL2Section (μ.prod ν), x ∈ D →
        ∃ u : smoothSections (n := n + m) (r := r * s₁) (externalTensorFiber E F₁),
          Tprod (g₀.smoothToL2 (μ.prod ν) x) = g₁.smoothToL2 (μ.prod ν) u from
      hall v.val v.property
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      exact ⟨externalTensorSection E F₁ a (S b), hpure a b⟩
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
