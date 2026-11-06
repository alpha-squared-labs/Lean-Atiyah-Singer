/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanEmbedding

/-!
# The complementary Euclidean coordinate inclusion

Public module ID: M1213.

The second embedding in SG III.13's comparison occupies the final coordinate
block, while the first embedding occupies the initial block. This file supplies
that actual second inclusion in the same fixed Fin-addition coordinates as
`euclideanZeroAppend`. Its geometric certificate includes zero dimensions.
Source: SG III.13, printed p.244 / PDF p.256, for the embedding comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Topology
open scoped ContDiff

/-- Prepend n zero coordinates, with the original vector in the final k-coordinate block. -/
def euclideanZeroPrepend (n k : ℕ) :
    ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + k)))
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin (n + k))) ∞ :=
  ⟨fun x ↦ (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm (0, x),
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm.contDiff.comp
      (contDiff_const.prodMk contDiff_id)).contMDiff⟩

/-- The complementary coordinate inclusion is a proper smooth embedding, including zero ranks. -/
theorem euclideanZeroPrepend_properties (n k : ℕ) :
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + k))) ∞ (euclideanZeroPrepend n k) ∧
      IsProperMap (euclideanZeroPrepend n k) := by
  /- Stage 1: in the specified finAddEquivProd coordinates the map is x -> (0,x).
  Its derivative is the same linear inclusion, complemented by the initial
  real n-coordinate block. Exchanging the two real blocks gives explicit
  global inclusion charts and hence the local-normal-form immersion property.
  Stage 2: projection to the final block is a continuous inverse on the image.
  That image is closed, being the inverse image of {0} under the initial-block
  projection. Thus the original map is a closed embedding and is proper.
  This geometric real-coordinate exchange does not identify a complex
  Thom or Bott class. Its complex orientation is checked separately in the
  stabilization statement. Neither step assumes positive dimension. -/
  -- The specified block coordinates give a global immersion with the first block as complement.
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)
  have himm : IsImmersionOfComplement (EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + k)))
      ∞ (euclideanZeroPrepend n k) := by
    intro x
    apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
      (euclideanZeroPrepend n k).contMDiff.continuous.continuousAt
      ((ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin n))).trans e.symm)
    intro y hy
    simp [euclideanZeroPrepend, e]
  -- The original inclusion has a closed image: the initial coordinates vanish.
  have hblock : IsClosedEmbedding
      (fun x : EuclideanSpace ℝ (Fin k) ↦ ((0 : EuclideanSpace ℝ (Fin n)), x)) := by
    refine ⟨isEmbedding_prodMkRight 0, ?_⟩
    have hrange : Set.range (fun x : EuclideanSpace ℝ (Fin k) ↦
        ((0 : EuclideanSpace ℝ (Fin n)), x)) =
        Prod.fst ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
      ext ⟨y, z⟩
      simp [eq_comm]
    rw [hrange]
    exact isClosed_singleton.preimage continuous_fst
  have hclosed : IsClosedEmbedding (euclideanZeroPrepend n k) :=
    e.symm.toHomeomorph.isClosedEmbedding.comp hblock
  -- Closed embeddings are proper, including either zero-dimensional block.
  exact ⟨⟨himm.isImmersion, hclosed.isEmbedding⟩, hclosed.isProperMap⟩

end AtiyahSinger
