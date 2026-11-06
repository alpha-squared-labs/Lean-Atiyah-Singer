/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CoefficientBundleRescaling
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The original bundle rescaling as an open cylinder

Public module ID: M1114.

A normalized partial diffeomorphism and its inverse extend by fiber dilation
to a parameter-preserving partial homeomorphism, with explicit open source and
target. The scalar parameter may be any continuous real-valued function, so
the construction applies directly to the closed unit interval.

Both maps keep their actual original bundle topology and inverse identities.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Set Topology
open scoped ContDiff

variable {EB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]
  {C : Type*} [TopologicalSpace C]

/-- Rescaling a normalized partial diffeomorphism gives a genuine open cylinder. -/
def rescaleBundlePartialHomeomorph (a : C → ℝ) (ha : Continuous a)
    (e : PartialDiffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F))
      (TotalSpace F V) (TotalSpace F V) ∞)
    (hzero : ∀ x : B, e ⟨x, 0⟩ = ⟨x, 0⟩)
    (hsource : ∀ x : B, (⟨x, 0⟩ : TotalSpace F V) ∈ e.source)
    (hnormal : ∀ x : B,
      let c := extChartAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (⟨x, 0⟩ : TotalSpace F V)
      (fderiv ℝ (fun z : EB × F ↦ (c (e (c.symm z))).2) (c ⟨x, 0⟩)).comp
        (ContinuousLinearMap.inr ℝ EB F) = ContinuousLinearMap.id ℝ F)
    (hnormali : ∀ x : B,
      let c := extChartAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (⟨x, 0⟩ : TotalSpace F V)
      (fderiv ℝ (fun z : EB × F ↦ (c (e.symm (c.symm z))).2) (c ⟨x, 0⟩)).comp
        (ContinuousLinearMap.inr ℝ EB F) = ContinuousLinearMap.id ℝ F) :
    OpenPartialHomeomorph (C × TotalSpace F V) (C × TotalSpace F V) := by
  -- The smooth hypotheses supply the two continuity inputs for the common cylinder.
  have hzeroi (x : B) : e.symm ⟨x, 0⟩ = ⟨x, 0⟩ := by
    simpa only [hzero x] using! e.left_inv (hsource x)
  exact rescaleBundleOpenPartialHomeomorph a ha e.toOpenPartialHomeomorph hzero hsource
    (continuousOn_rescaleBundleMap e e.contMDiffOn e.open_source hzero hnormal)
    (continuousOn_rescaleBundleMap e.symm e.contMDiffOn_invFun e.open_target hzeroi hnormali)

end AtiyahSinger
