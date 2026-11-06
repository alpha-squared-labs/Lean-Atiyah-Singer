/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint
public import AtiyahSinger.Analysis.KernelAdjointRestriction

/-!
# The actual metric adjoint in full vertical-kernel coordinates

Public module ID: M0775.

The integral pairings in the specified coefficient model identify the reverse
restriction with the metric formal adjoint of the same PDO. Uniqueness of the
positive integral adjunction, rather than a chosen inverse or a dimension
comparison, supplies this identification. The resulting joint-kernel map
retains the specified target kernel equivalence pointwise.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n a a' : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {E' : B → Type*} [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]
  {X₀₀ X₁₀ X₀₁ X₁₁ : Type*}
  [AddCommGroup X₀₀] [Module ℂ X₀₀] [AddCommGroup X₁₀] [Module ℂ X₁₀]
  [AddCommGroup X₀₁] [Module ℂ X₀₁] [AddCommGroup X₁₁] [Module ℂ X₁₁]

set_option maxSynthPendingDepth 30 in
/-- The reverse full-kernel map is the actual coefficient PDO's metric formal adjoint. -/
theorem PseudodifferentialOperator.exists_adjoint_jointKernelEquiv {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') E')
    (H₀ : X₀₀ →ₗ[ℂ] X₁₀) (H₁ : X₀₁ →ₗ[ℂ] X₁₁) (H₁a : X₁₁ →ₗ[ℂ] X₀₁)
    (V₀ : X₀₀ →ₗ[ℂ] X₀₁) (V₀a : X₀₁ →ₗ[ℂ] X₀₀)
    (V₁ : X₁₀ →ₗ[ℂ] X₁₁) (V₁a : X₁₁ →ₗ[ℂ] X₁₀)
    (p₀₀ : X₀₀ → X₀₀ → ℂ) (p₁₀ : X₁₀ → X₁₀ → ℂ)
    (p₀₁ : X₀₁ → X₀₁ → ℂ) (p₁₁ : X₁₁ → X₁₁ → ℂ)
    (hp₀₀ : ∀ x, (∀ u, p₀₀ u x = 0) → x = 0)
    (hp₁₀ : ∀ u, p₁₀ u 0 = 0)
    (hH₁ : ∀ u v, p₁₁ (H₁ u) v = p₀₁ u (H₁a v))
    (hV₀ : ∀ u v, p₀₁ (V₀ u) v = p₀₀ u (V₀a v))
    (hV₁ : ∀ u v, p₁₁ (V₁ u) v = p₁₀ u (V₁a v))
    (hcomm : ∀ u, H₁ (V₀ u) = V₁ (H₀ u))
    (Φ : smoothSections (n := n) (r := a) E ≃ₗ[ℂ] V₀a.ker)
    (Ψ : smoothSections (n := n) (r := a') E' ≃ₗ[ℂ] V₁a.ker)
    (hP : ∀ u, H₁ (Φ u).val = (Ψ (P.toLinearMap u)).val)
    (hΦ : ∀ u v, p₀₁ (Φ u).val (Φ v).val = h.sectionPairing μ u v)
    (hΨ : ∀ u v, p₁₁ (Ψ u).val (Ψ v).val = k.sectionPairing μ u v) :
    (∀ v ∈ V₁a.ker, H₁a v ∈ V₀a.ker) ∧
    (∀ v, H₁a (Ψ v).val = (Φ ((P.metricFormalAdjoint h k).toLinearMap v)).val) ∧
    ∃ κ : (P.metricFormalAdjoint h k).toLinearMap.ker ≃ₗ[ℂ] ↥(H₁a.ker ⊓ V₁a.ker),
      ∀ v, (κ v).val = (Ψ v.val).val := by
  -- The restriction and its integral identity are consequences of the original square.
  obtain ⟨hpres, R, hR, hRadjoint, κ, hκ⟩ := exists_adjoint_kernel_restriction
    H₀ H₁ H₁a V₀ V₀a V₁ V₁a p₀₀ p₁₀ p₀₁ p₁₁ hp₀₀ hp₁₀ hH₁ hV₀ hV₁ hcomm
    Φ Ψ P.toLinearMap hP (h.sectionPairing μ) (k.sectionPairing μ) hΦ hΨ
  -- Positivity of this same coefficient integral pairing identifies the full section map.
  have hReq : R = (P.metricFormalAdjoint h k).toLinearMap :=
    (show IsMetricFormalAdjoint h k μ P.toLinearMap R from hRadjoint).unique
      (P.isMetricFormalAdjoint_metricFormalAdjoint h k)
  subst R
  exact ⟨hpres, hR, κ, hκ⟩

end AtiyahSinger
