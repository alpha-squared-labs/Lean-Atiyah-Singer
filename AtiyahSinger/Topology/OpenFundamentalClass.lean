/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import AtiyahSinger.Topology.OpenHomologicalOrientation

/-!
# Open embeddings and the specified compact-relative fundamental classes

Public module ID: M1973.

An orientation-preserving open embedding sends the original fundamental
class over a compact set to that over its compact image. This follows from
local normalization and uniqueness, with the actual same map of pairs.
Rationalization preserves this comparison and its specified sign.

Source: Hatcher, Algebraic Topology, section 3.3, uniqueness and naturality
of fundamental classes. These comparisons feed cap naturality and integration.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

universe u

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
  [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]

/-- Open embeddings preserving the chosen local generators preserve compact fundamental classes. -/
theorem compactRelativeFundamentalClass_openEmbedding
    (OX : HomologicalOrientation n X) (OY : HomologicalOrientation n Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (ho : IsOrientationPreservingOpenEmbedding OX OY f hf) (K : Compacts X) :
    relativeSingularHomologyMap ℤ f
      (A := (K : Set X)ᶜ) (B := (openEmbeddingCompactImage f K : Set Y)ᶜ)
      (fun _x hx h ↦ hx (hf.injective.mem_set_image.mp h)) n
      (compactRelativeFundamentalClass OX K) =
        compactRelativeFundamentalClass OY (openEmbeddingCompactImage f K) := by
  -- The image has the prescribed local value at each of its own points.
  apply (existsUnique_compactRelativeFundamentalClass OY
    (openEmbeddingCompactImage f K)).unique
  · rintro y ⟨x, hx, rfl⟩
    have hA : (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
    have hB : (openEmbeddingCompactImage f K : Set Y)ᶜ ⊆ ({f x}ᶜ : Set Y) :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr ⟨x, hx, rfl⟩)
    have hsquare := relativeSingularHomologyMap_inclusion ℤ f hA hB
      (fun z hz h ↦ hz (hf.injective.mem_set_image.mp h))
      (fun z hz h ↦ hz (hf.injective h)) n
    have hvalue := congrArg (fun t ↦ t (compactRelativeFundamentalClass OX K)) hsquare
    change relativeSingularHomologyMap ℤ f (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
      (fun z (hz : z ∈ ({x}ᶜ : Set X)) h ↦ hz (hf.injective h)) n
      (relativeSingularHomologyInclusion ℤ (K : Set X)ᶜ ({x}ᶜ) hA n
        (compactRelativeFundamentalClass OX K)) = _ at hvalue
    rw [compactRelativeFundamentalClass_restriction OX K x hx] at hvalue
    exact hvalue.symm.trans (ho x)
  · exact compactRelativeFundamentalClass_restriction OY (openEmbeddingCompactImage f K)

/-- Coefficient change retains the same compact image and orientation normalization. -/
theorem rationalCompactRelativeFundamentalClass_openEmbedding
    (OX : HomologicalOrientation n X) (OY : HomologicalOrientation n Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (ho : IsOrientationPreservingOpenEmbedding OX OY f hf) (K : Compacts X) :
    relativeSingularHomologyMap ℚ f
      (A := (K : Set X)ᶜ) (B := (openEmbeddingCompactImage f K : Set Y)ᶜ)
      (fun _x hx h ↦ hx (hf.injective.mem_set_image.mp h)) n
      (rationalCompactRelativeFundamentalClass OX K) =
        rationalCompactRelativeFundamentalClass OY (openEmbeddingCompactImage f K) := by
  -- The original integral class is rationalized through the actual natural coefficient map.
  have hnat := relativeSingularHomologyRationalization_naturality f
    (A := (K : Set X)ᶜ) (B := (openEmbeddingCompactImage f K : Set Y)ᶜ)
    (fun _x hx h ↦ hx (hf.injective.mem_set_image.mp h)) n
    (compactRelativeFundamentalClass OX K)
  exact hnat.symm.trans (congrArg
    (relativeSingularHomologyRationalization (openEmbeddingCompactImage f K : Set Y)ᶜ n)
    (compactRelativeFundamentalClass_openEmbedding OX OY f hf ho K))

end AtiyahSinger
