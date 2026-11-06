/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.AtlasHermitianMetric

/-!
# Transport of smooth atlases along equality of the original total topology

Public module ID: M1369.

These implementation adapters transport atlas data and smoothness certificates
only through an equality of total-space topologies. They do not assert smooth
compatibility of arbitrary continuous atlases. The rank-stratum flag bridge
uses them for the inverse phantom-model retypings, which keep every vector.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped Manifold ContDiff

universe w

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  {t₁ t₂ t₃ : TopologicalSpace (TotalSpace Unit E)}

/-- Retype the same atlas through equality of its total-space topology. -/
def congrTopology (A : letI := t₁; SmoothComplexBundleAtlas.{w} (n := n) E)
    (ht : t₁ = t₂) : letI := t₂; SmoothComplexBundleAtlas.{w} (n := n) E := by
  cases ht
  exact A

/-- Successive equality transports retain the same original atlas. -/
theorem congrTopology_trans (A : letI := t₁; SmoothComplexBundleAtlas.{w} (n := n) E)
    (h₁₂ : t₁ = t₂) (h₂₃ : t₂ = t₃) :
    (A.congrTopology h₁₂).congrTopology h₂₃ = A.congrTopology (h₁₂.trans h₂₃) := by
  cases h₁₂
  cases h₂₃
  rfl

/-- The inverse topology equality recovers the original atlas data. -/
theorem congrTopology_symm (A : letI := t₁; SmoothComplexBundleAtlas.{w} (n := n) E)
    (ht : t₁ = t₂) : (A.congrTopology ht).congrTopology ht.symm = A := by
  cases ht
  rfl

/-- Equality transport preserves smoothness of the same original Hermitian form. -/
theorem isSmoothHermitianMetric_congrTopology
    (A : letI := t₁; SmoothComplexBundleAtlas.{w} (n := n) E) (ht : t₁ = t₂)
    (h₁ : letI := t₁; ComplexBundle.ContinuousHermitianMetric E)
    (h₂ : letI := t₂; ComplexBundle.ContinuousHermitianMetric E)
    (hc : (letI := t₂; h₂.toCore) = (letI := t₁; h₁.toCore))
    (hh : letI := t₁; A.IsSmoothHermitianMetric h₁) :
    letI := t₂
    (A.congrTopology ht).IsSmoothHermitianMetric h₂ := by
  cases ht
  have heq : h₂ = h₁ := by
    cases h₁
    cases h₂
    cases hc
    rfl
  subst h₂
  exact hh

variable {m : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  {F : N → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  {s₁ s₂ : TopologicalSpace (TotalSpace Unit F)}

/-- Equality transports preserve the smoothness of the same fiberwise linear map. -/
theorem isSmoothAtlasBundleMapOver_congrTopology
    (A : letI := t₁; SmoothComplexBundleAtlas (n := n) E)
    (B : letI := s₁; SmoothComplexBundleAtlas (n := m) F)
    (hE : t₁ = t₂) (hF : s₁ = s₂) (f : M → N) (a : ∀ x, E x →ₗ[ℂ] F (f x)) :
    (letI := t₂
     letI := s₂
     IsSmoothAtlasBundleMapOver (A.congrTopology hE) (B.congrTopology hF) f a) ↔
    (letI := t₁
     letI := s₁
     IsSmoothAtlasBundleMapOver A B f a) := by
  cases hE
  cases hF
  rfl

end AtiyahSinger.SmoothComplexBundleAtlas
