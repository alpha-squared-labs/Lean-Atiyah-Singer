/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Topology.OpenEmbeddingKZero

/-!
# Cotangent K transport and open extension

Public module ID: M1966.

These are the cotangent maps in SG III.13.4 used by analytic excision.
A smooth open embedding is presented as a
specified diffeomorphism onto an open submanifold. This retains its inverse
smoothness and the actual inverse-dual differential. No finite-topological-type
or compactness assumption is needed to construct these K-theory maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N] [T2Space N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- K-theory transport induced by the actual inverse-dual cotangent homeomorphism. -/
def cotangentKZeroDiffeomorph
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) ≃+
      CompactSupportKZero (CotangentTotalSpace (n := m) (M := N)) :=
  compactSupportKZeroHomeomorphEquiv (cotangentDiffeomorph e)

/-- Extend cotangent K classes from an open submanifold by its actual open inclusion. -/
def cotangentKZeroOpenExtension (U : Opens M) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := U)) →+
      CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  compactSupportKZeroOpenPushforward (cotangentOpenInclusion U)
    (isOpenEmbedding_cotangentOpenInclusion U)

/-- Open cotangent extension after the specified diffeomorphism onto the image. -/
def cotangentKZeroOpenEmbedding (V : Opens N)
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ V) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+
      CompactSupportKZero (CotangentTotalSpace (n := m) (M := N)) :=
  (cotangentKZeroOpenExtension V).comp (cotangentKZeroDiffeomorph e).toAddMonoidHom

end AtiyahSinger
