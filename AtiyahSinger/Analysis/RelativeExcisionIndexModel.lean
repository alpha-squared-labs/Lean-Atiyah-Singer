/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Analysis.RelativeEllipticRealization
public import AtiyahSinger.Analysis.RelativeExcisionSectionTransport
public import AtiyahSinger.Geometry.OpenEmbeddingBundleIso
public import AtiyahSinger.Geometry.RelativeExcisionTransport
public import AtiyahSinger.Geometry.SmoothBundleMapTopSource

import all AtiyahSinger.Analysis.OpenExtensionIndex

/-!
# A common supported model for relative analytic excision

Public module ID: M0915.

An ambient realization records one actual elliptic operator, the original
supported source action, both integral pairings, and both full kernel supports.
Two such realizations can then be compared on the same source spaces. The
geometric and symbolic construction retains the specified open parametrization,
the single finite correction family, and the original compact-support K class.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace MeasureTheory Filter
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- One actual elliptic realization of the same supported source action and K class.
This implementation record is reused for the two ambient environments in excision. -/
structure RelativeExcisionIndexModel
    (E F : SmoothFiniteComplexBundle (n := n) O)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure O) (L : Set O)
    (D : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L →ₗ[ℂ]
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber L)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := O)))
    (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U) where
  /-- The actual ambient source bundle. -/
  source : SmoothFiniteComplexBundle (n := n) M
  /-- The actual ambient target bundle. -/
  target : SmoothFiniteComplexBundle (n := n) M
  /-- The actual ambient positive smooth density. -/
  measure : Measure M
  /-- Positivity and smoothness of the same density. -/
  [positive : IsSmoothPositiveMeasure (n := n) measure]
  /-- The ambient source metric used for the adjoint. -/
  sourceMetric : SmoothHermitianMetric (n := n) (r := source.rank) source.Fiber
  /-- The ambient target metric used for the adjoint. -/
  targetMetric : SmoothHermitianMetric (n := n) (r := target.rank) target.Fiber
  /-- The ambient elliptic operator, retaining its lower-order terms. -/
  operator : PseudodifferentialOperator (n := n) (r := source.rank) (q := target.rank)
    source.Fiber target.Fiber measure 0
  /-- Ellipticity of this actual operator. -/
  elliptic : operator.IsElliptic
  /-- The exact supported source-section identification. -/
  sourceEquiv : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L ≃ₗ[ℂ]
    supportedSmoothSections (n := n) (r := source.rank) source.Fiber
      ((fun x : O ↦ (e x).val) '' L)
  /-- The exact supported target-section identification. -/
  targetEquiv : supportedSmoothSections (n := n) (r := F.rank) F.Fiber L ≃ₗ[ℂ]
    supportedSmoothSections (n := n) (r := target.rank) target.Fiber
      ((fun x : O ↦ (e x).val) '' L)
  /-- The source integral pairing agrees on the same identified sections. -/
  source_pairing : ∀ s t, sourceMetric.sectionPairing measure
    (sourceEquiv s).val (sourceEquiv t).val = h.sectionPairing ν s.val t.val
  /-- The target integral pairing agrees on the same identified sections. -/
  target_pairing : ∀ s t, targetMetric.sectionPairing measure
    (targetEquiv s).val (targetEquiv t).val = k.sectionPairing ν s.val t.val
  /-- The ambient operator realizes exactly the common source action. -/
  action : ∀ s, operator.toLinearMap (sourceEquiv s).val = (targetEquiv (D s)).val
  /-- The actual adjoint preserves the controlled section space. -/
  adjoint_support : ∀ v : supportedSmoothSections (n := n) (r := target.rank)
    target.Fiber ((fun x : O ↦ (e x).val) '' L),
    (operator.metricFormalAdjoint sourceMetric targetMetric).toLinearMap v.val ∈
      supportedSmoothSections (n := n) (r := source.rank) source.Fiber
        ((fun x : O ↦ (e x).val) '' L)
  /-- The full operator kernel has the stated support. -/
  kernel_support : operator.toLinearMap.ker ≤ supportedSmoothSections (n := n)
    (r := source.rank) source.Fiber ((fun x : O ↦ (e x).val) '' L)
  /-- The full adjoint kernel has the stated support. -/
  adjoint_kernel_support :
    (operator.metricFormalAdjoint sourceMetric targetMetric).toLinearMap.ker ≤
      supportedSmoothSections (n := n) (r := target.rank) target.Fiber
        ((fun x : O ↦ (e x).val) '' L)
  /-- The public open cotangent K class evaluates to this operator's index. -/
  class_eq_index : analyticIndexOfComponents measure (cotangentKZeroOpenEmbedding U e u) =
    operator.toLinearMap.index

attribute [instance] RelativeExcisionIndexModel.positive

variable {N : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

omit [SecondCountableTopology O] [BorelSpace O] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two actual elliptic realizations of the same supported model have equal full indices. -/
theorem RelativeExcisionIndexModel.index_eq
    (E F : SmoothFiniteComplexBundle (n := n) O)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure O) (L : Set O) (hL : IsCompact L)
    (D : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L →ₗ[ℂ]
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber L)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := O)))
    (U : Opens M) (V : Opens N)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (f : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
    (X : RelativeExcisionIndexModel E F h k ν L D u U e)
    (Y : RelativeExcisionIndexModel E F h k ν L D u V f) :
    X.operator.toLinearMap.index = Y.operator.toLinearMap.index := by
  -- Compose through the same source spaces, so both pairings and the actual action match.
  let A := X.sourceEquiv.symm.trans Y.sourceEquiv
  let B := X.targetEquiv.symm.trans Y.targetEquiv
  have hP : ∀ s : supportedSmoothSections (n := n) (r := X.source.rank) X.source.Fiber
      ((fun x : O ↦ (e x).val) '' L), X.operator.toLinearMap s.val ∈
        supportedSmoothSections (n := n) (r := X.target.rank) X.target.Fiber
          ((fun x : O ↦ (e x).val) '' L) := by
    intro s
    obtain ⟨s, rfl⟩ := X.sourceEquiv.surjective s
    rw [X.action]
    exact (X.targetEquiv (D s)).property
  have hA : ∀ s t, Y.sourceMetric.sectionPairing Y.measure (A s).val (A t).val =
      X.sourceMetric.sectionPairing X.measure s.val t.val := by
    intro s t
    change Y.sourceMetric.sectionPairing Y.measure
      (Y.sourceEquiv (X.sourceEquiv.symm s)).val
      (Y.sourceEquiv (X.sourceEquiv.symm t)).val = _
    rw [Y.source_pairing]
    have hp := X.source_pairing (X.sourceEquiv.symm s) (X.sourceEquiv.symm t)
    simpa only [LinearEquiv.apply_symm_apply] using hp.symm
  have hB : ∀ s t, Y.targetMetric.sectionPairing Y.measure (B s).val (B t).val =
      X.targetMetric.sectionPairing X.measure s.val t.val := by
    intro s t
    change Y.targetMetric.sectionPairing Y.measure
      (Y.targetEquiv (X.targetEquiv.symm s)).val
      (Y.targetEquiv (X.targetEquiv.symm t)).val = _
    rw [Y.target_pairing]
    have hp := X.target_pairing (X.targetEquiv.symm s) (X.targetEquiv.symm t)
    simpa only [LinearEquiv.apply_symm_apply] using hp.symm
  have hPQ : ∀ s, Y.operator.toLinearMap (A s).val =
      (B ⟨X.operator.toLinearMap s.val, hP s⟩).val := by
    intro s
    have hsource : X.targetEquiv.symm ⟨X.operator.toLinearMap s.val, hP s⟩ =
        D (X.sourceEquiv.symm s) := by
      apply X.targetEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      simpa only [LinearEquiv.apply_symm_apply] using X.action (X.sourceEquiv.symm s)
    change Y.operator.toLinearMap (Y.sourceEquiv (X.sourceEquiv.symm s)).val =
      (Y.targetEquiv (X.targetEquiv.symm ⟨X.operator.toLinearMap s.val, hP s⟩)).val
    rw [Y.action, hsource]
  -- Full kernel supports permit the existing elliptic two-kernel comparison.
  exact PseudodifferentialOperator.index_eq_of_supported_intertwining
    X.source X.target Y.source Y.target X.sourceMetric X.targetMetric
    Y.sourceMetric Y.targetMetric X.measure Y.measure X.operator Y.operator X.elliptic Y.elliptic
    ((fun x : O ↦ (e x).val) '' L) ((fun x : O ↦ (f x).val) '' L)
    (hL.image (continuous_subtype_val.comp e.continuous))
    (hL.image (continuous_subtype_val.comp f.continuous)) hP X.adjoint_support Y.adjoint_support
    X.kernel_support Y.kernel_support X.adjoint_kernel_support Y.adjoint_kernel_support
    A B hA hB hPQ

end AtiyahSinger
