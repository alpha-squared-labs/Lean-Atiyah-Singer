/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# The original Euclidean coordinate inclusion for stabilization

Public module ID: M1218.

Append k zero coordinates to a vector of real Euclidean n-space. The actual
map is the inverse of mathlib's specified Fin-addition coordinate equivalence
applied to (x,0). No arbitrary Euclidean linear equivalence or chosen embedding
is substituted. Its smooth-embedding and properness certificate covers all
natural n and k, including either dimension being zero.

This is the standard coordinate inclusion used when stabilizing the Euclidean
embedding in the topological-index construction of SG III.13. The properties
are an elementary linear-geometric supplement; no separately numbered source
theorem is claimed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Topology
open scoped ContDiff

/-- Append zero coordinates in the fixed original Fin-addition coordinate order. -/
def euclideanZeroAppend (n k : ℕ) :
    ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + k)))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (n + k))) ∞ :=
  ⟨fun x ↦ (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm (x, 0),
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm.contDiff.comp
      (contDiff_id.prodMk contDiff_const)).contMDiff⟩

/-- The actual zero-coordinate inclusion is a proper smooth embedding in every dimension. -/
theorem euclideanZeroAppend_properties (n k : ℕ) :
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + k))) ∞ (euclideanZeroAppend n k) ∧
      IsProperMap (euclideanZeroAppend n k) := by
  /- Stage 1: apply the original finAddEquivProd target coordinates. The map
  becomes precisely x -> (x,0), with the first n coordinates unchanged and
  the final k zero. Its derivative is that same continuous linear inclusion.
  The final k-coordinate factor is an explicit complement, so these global
  linear charts directly give the immersion normal form.
  Stage 2: the first-coordinate projection is a continuous inverse on the
  image. The image is the inverse image of the closed singleton {0} under the
  final-coordinate projection. Thus the original inclusion, transported by
  the specified linear homeomorphism, is a closed topological embedding.
  Stage 3: a closed embedding is proper, by the existing IsClosedEmbedding
  properness theorem. Combine its embedding with the immersion from Stage 1.
  None of these arguments uses a positive dimension, nonzero vector or chosen
  basis; the same maps and certificates apply when n=0, k=0, or both are zero. -/
  -- The specified block coordinates give a global immersion with the last block as complement.
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)
  have himm : IsImmersionOfComplement (EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + k)))
      ∞ (euclideanZeroAppend n k) := by
    intro x
    apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
      (euclideanZeroAppend n k).contMDiff.continuous.continuousAt e.symm
    intro y hy
    simp [euclideanZeroAppend, e]
  -- The original inclusion has a closed image: the final coordinates vanish.
  have hblock : IsClosedEmbedding
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (x, (0 : EuclideanSpace ℝ (Fin k)))) := by
    refine ⟨isEmbedding_prodMkLeft 0, ?_⟩
    have hrange : Set.range (fun x : EuclideanSpace ℝ (Fin n) ↦
        (x, (0 : EuclideanSpace ℝ (Fin k)))) =
        Prod.snd ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin k))) := by
      ext ⟨y, z⟩
      simp [eq_comm]
    rw [hrange]
    exact isClosed_singleton.preimage continuous_snd
  have hclosed : IsClosedEmbedding (euclideanZeroAppend n k) :=
    e.symm.toHomeomorph.isClosedEmbedding.comp hblock
  -- Closed embeddings are proper, including either zero-dimensional block.
  exact ⟨⟨himm.isImmersion, hclosed.isEmbedding⟩, hclosed.isProperMap⟩

end AtiyahSinger
