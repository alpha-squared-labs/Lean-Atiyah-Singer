/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding

/-!
# Smooth sections are smooth embeddings

Public module ID: M1410.

A smooth left inverse splits the differential and supplies the induced topology
on the image. The finite-dimensional immersion criterion therefore makes a
smooth section a smooth embedding. This standard section theorem is used for
both the zero section of a normal bundle and its sphere compactification.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth map admitting a smooth left inverse is a smooth embedding. -/
theorem isSmoothEmbedding_of_leftInverse
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, E) N M ∞)
    (h : Function.LeftInverse g f) : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  have hcomp : (g : N → M) ∘ (f : M → N) = id := funext h
  -- Differentiating the left inverse shows that the actual derivative of f is injective.
  have hderiv (x : M) : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) := by
    have hD := mfderiv_comp x (g.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x)
    rw [hcomp, mfderiv_id] at hD
    intro u v huv
    have hh := congrArg (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g (f x)) huv
    change ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g (f x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) u =
        ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g (f x)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) v at hh
    rw [← hD] at hh
    exact hh
  -- The same left inverse gives the subspace topology, without separation assumptions.
  exact ⟨isImmersion_of_injective_mfderiv f hderiv,
    h.isEmbedding g.contMDiff.continuous f.contMDiff.continuous⟩

end AtiyahSinger
