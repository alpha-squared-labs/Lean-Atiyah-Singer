/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.TangentEmbeddingRealIsotopy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Isotopy invariance under a change of the original smooth embedding

Public module ID: M2231.

A jointly smooth family of embeddings of a compact manifold gives equal actual
tangent embedding pushforwards at its endpoints. Reparameterize through the
closed unit interval by a smooth cosine function to obtain an all-real family
of embeddings with the same endpoints. This permits the native boundaryless
parameter geometry without an additional stability collar theorem.

The all-real comparison constructs the proper vertical tangent cylinder, its
parameter-preserving normalized tube, and continuous complex transport of the
original quotient normal family. Its endpoint splittings and tubes satisfy an
exact diagram for those same witnesses. Supported Thom naturality and the open
cylinder comparison then identify the original endpoint pushforwards.

Sources: SG III.13, printed pp.243--244, and Karoubi IV.5.21. The precise
compact-source, general-ambient statement and its parameter-preserving proof
are project supplements to those references. Compactness is used for joint
properness of the actual tangent cylinder, not for compactness of TM.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff unitInterval

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [CompactSpace M] [T2Space M] [T2Space N]
  [SecondCountableTopology M] [SecondCountableTopology N]

/-- A smooth isotopy of compact-source embeddings preserves the actual tangent pushforward. -/
theorem tangentEmbeddingPushforward_eq_of_isotopy
    (f : ℝ → ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ f p.1 p.2))
    (hemb : ∀ t : I, IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f t)) :
    tangentEmbeddingPushforward (f 0) (hemb 0) (f 0).contMDiff.continuous.isProperMap =
      tangentEmbeddingPushforward (f 1) (hemb 1) (f 1).contMDiff.continuous.isProperMap := by
  -- A smooth map into the original parameter interval preserves the two endpoints.
  let α : ℝ → ℝ := fun t ↦ (1 - Real.cos (Real.pi * t)) / 2
  have hα : ContDiff ℝ ∞ α := by
    unfold α
    fun_prop
  have hαmem (t : ℝ) : α t ∈ Set.Icc (0 : ℝ) 1 := by
    have hlo := Real.neg_one_le_cos (Real.pi * t)
    have hhi := Real.cos_le_one (Real.pi * t)
    constructor <;> dsimp [α] <;> linarith
  have hα0 : α 0 = 0 := by simp [α]
  have hα1 : α 1 = 1 := by simp [α]
  let g (t : ℝ) := f (α t)
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ g p.1 p.2) :=
    hsmooth.comp (hα.contMDiff.prodMap contMDiff_id)
  have hge (t : ℝ) : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (g t) :=
    hemb ⟨α t, hαmem t⟩
  -- The actual all-real cylinder comparison returns the original endpoint maps.
  have h := tangentEmbeddingPushforward_eq_of_real_isotopy g hg hge
  simpa only [g, hα0, hα1] using h

end AtiyahSinger
