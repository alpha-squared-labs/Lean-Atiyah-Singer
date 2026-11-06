/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# The actual overlap transition of two open embeddings

Public module ID: M1972.

Two specified open embeddings of the same source give an open partial
homeomorphism on their actual overlap. If the embeddings agree on a specified
family of source points, that family lies in the overlap and the transition
fixes it. The construction also covers an empty source.

This is the topological overlap used for a normalized nested tubular map;
no smoothness or rescaling property is asserted here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The same open embeddings determine their precise overlap and fixed-point transition. -/
theorem exists_openEmbeddingTransition (f g : X → Y)
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (j : Z → X) (hzero : ∀ z, f (j z) = g (j z)) :
    ∃ e : OpenPartialHomeomorph X X,
      e.source = g ⁻¹' range f ∧ e.target = f ⁻¹' range g ∧
      (∀ z, j z ∈ e.source) ∧ (∀ z, e (j z) = j z) ∧
      (∀ x, x ∈ e.source → f (e x) = g x) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    let := hX
    refine ⟨OpenPartialHomeomorph.refl X, ?_, ?_, ?_, ?_, ?_⟩
    · ext x
      exact isEmptyElim x
    · ext x
      exact isEmptyElim x
    · intro z
      exact isEmptyElim (j z)
    · intro z
      rfl
    · intro x
      exact isEmptyElim x
  | inr hX =>
    let := hX
    let F := hf.toOpenPartialHomeomorph f
    let G := hg.toOpenPartialHomeomorph g
    let e := G.trans F.symm
    have hsource : e.source = g ⁻¹' range f := by
      ext x
      simp [e, F, G]
    have htarget : e.target = f ⁻¹' range g := by
      ext x
      simp [e, F, G]
    have hmem (z : Z) : j z ∈ e.source := by
      rw [hsource]
      exact ⟨j z, hzero z⟩
    have hmap (x : X) (hx : x ∈ e.source) : f (e x) = g x := by
      have hx' : g x ∈ range f := by
        simpa only [hsource, Set.mem_preimage] using hx
      change f (F.symm (g x)) = g x
      exact hf.toOpenPartialHomeomorph_right_inv f hx'
    refine ⟨e, hsource, htarget, hmem, ?_, hmap⟩
    intro z
    exact hf.injective ((hmap (j z) (hmem z)).trans (hzero z).symm)

end AtiyahSinger
