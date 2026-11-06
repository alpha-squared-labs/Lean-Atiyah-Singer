/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Analysis.ComponentCotangentNaturality
public import AtiyahSinger.Analysis.PreconnectedAnalyticNaturality
public import AtiyahSinger.Topology.OpenCotangentKZero

/-!
# Invariance of the analytic index under diffeomorphisms

Public module ID: M0079.

A10/P02: change the compact ambient manifold by an actual smooth diffeomorphism,
using its inverse-dual cotangent K transport. This naturality statement is a
prerequisite for excision, not the excision theorem for a proper open subregion.
Sources: SG III.3 coordinate covariance and III.13 (13.7)--(13.8).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped Manifold ContDiff

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isSmoothPositiveMeasure_comap_opens

/-- The compact analytic-index homomorphisms commute with actual cotangent diffeomorphisms. -/
theorem analyticIndexOfComponents_diffeomorph
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν]
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    (analyticIndexOfComponents ν).comp (cotangentKZeroDiffeomorph e).toAddMonoidHom =
      analyticIndexOfComponents μ := by
  classical
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin m)) N
  let := Fintype.ofFinite (ConnectedComponents M)
  let := Fintype.ofFinite (ConnectedComponents N)
  -- Expand the actual component sum and reindex by the original diffeomorphism.
  apply AddMonoidHom.ext
  intro u
  simp only [analyticIndexOfComponents, AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply]
  change (∑ c : ConnectedComponents N,
    analyticIndex (n := m) (ν.comap (Subtype.val : manifoldComponent (n := m) c → N))
      (cotangentKZeroComponents (cotangentKZeroDiffeomorph e u) c)) =
    ∑ c : ConnectedComponents M,
      analyticIndex (n := n) (μ.comap (Subtype.val : manifoldComponent (n := n) c → M))
        (cotangentKZeroComponents u c)
  rw [← (diffeomorphConnectedComponentsEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  rw [cotangentKZeroComponents_diffeomorph]
  -- A component is nonempty. Its invertible differential equates the two model dimensions.
  obtain ⟨x⟩ := (inferInstance : Nonempty (manifoldComponent (n := n) c))
  have hdim : n = m := by
    have hd : e.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) :=
      ⟨(e.mdifferentiable (by simp)).mdifferentiableOn,
        (e.symm.mdifferentiable (by simp)).mdifferentiableOn⟩
    have h := (hd.mfderiv (x := x.val) (by trivial)).toLinearEquiv.finrank_eq
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) at h
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using h
  subst m
  -- Each actual component has its own representative; their virtual ranks may differ.
  have h := analyticIndex_diffeomorph
    (μ.comap (Subtype.val : manifoldComponent (n := n) c → M))
    (ν.comap (Subtype.val :
      manifoldComponent (n := n) (diffeomorphConnectedComponentsEquiv e c) → N))
    (componentDiffeomorph e c)
  exact DFunLike.congr_fun h (cotangentKZeroComponents u c)

end AtiyahSinger
