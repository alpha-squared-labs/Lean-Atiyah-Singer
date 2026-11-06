/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Joint graph closure from the two actual adjunctions

Public module ID: M0773.

A dense common input and its two operator images define a simultaneous graph.
Pairing each output with its own dense test space excludes a nonzero output
above zero input in the graph closure. This gives an actual densely defined
closed partial map, retaining both images. It supplies the joint domains for
associated horizontal and vertical actions once their integral adjunctions
have been transported to the specified inner-product spaces. No separate closures
are intersected without a simultaneous approximation proof.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E F₀ F₁ S T₀ T₁ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁]
  [AddCommGroup S] [Module ℂ S]
  [AddCommGroup T₀] [Module ℂ T₀]
  [AddCommGroup T₁] [Module ℂ T₁]

/-- The two adjunctions identify the simultaneous graph closure as a densely defined
closed partial map. -/
theorem exists_closed_jointGraph_of_adjoint_pairings
    (i : S →ₗ[ℂ] E) (p : S →ₗ[ℂ] F₀) (q : S →ₗ[ℂ] F₁)
    (j₀ : T₀ →ₗ[ℂ] F₀) (j₁ : T₁ →ₗ[ℂ] F₁)
    (pa : T₀ →ₗ[ℂ] E) (qa : T₁ →ₗ[ℂ] E)
    (hi : DenseRange i) (hj₀ : DenseRange j₀) (hj₁ : DenseRange j₁)
    (hp : ∀ s t, inner ℂ (p s) (j₀ t) = inner ℂ (i s) (pa t))
    (hq : ∀ s t, inner ℂ (q s) (j₁ t) = inner ℂ (i s) (qa t)) :
    ∃ D : E →ₗ.[ℂ] (F₀ × F₁),
      D.graph = (i.prod (p.prod q)).range.topologicalClosure ∧
      D.IsClosed ∧ Dense (D.domain : Set E) := by
  let J := (i.prod (p.prod q)).range
  let C := J.topologicalClosure
  -- Both pairings remain continuous in all joint graph coordinates.
  have hpClosure (x : E × F₀ × F₁) (hx : x ∈ C) (t : T₀) :
      inner ℂ x.2.1 (j₀ t) = inner ℂ x.1 (pa t) := by
    have hc : IsClosed {x : E × F₀ × F₁ |
        inner ℂ x.2.1 (j₀ t) = inner ℂ x.1 (pa t)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hc.closure_subset_iff.mpr ?_ hx
    rintro _ ⟨s, rfl⟩
    exact hp s t
  have hqClosure (x : E × F₀ × F₁) (hx : x ∈ C) (t : T₁) :
      inner ℂ x.2.2 (j₁ t) = inner ℂ x.1 (qa t) := by
    have hc : IsClosed {x : E × F₀ × F₁ |
        inner ℂ x.2.2 (j₁ t) = inner ℂ x.1 (qa t)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hc.closure_subset_iff.mpr ?_ hx
    rintro _ ⟨s, rfl⟩
    exact hq s t
  -- Density of the two test spaces forces both zero-input output coordinates to vanish.
  have hfunctional (x : E × F₀ × F₁) (hx : x ∈ C) (hx₀ : x.1 = 0) : x.2 = 0 := by
    apply Prod.ext
    · apply hj₀.eq_of_inner_left ℂ
      intro t
      rw [hpClosure x hx t, hx₀]
      simp only [Prod.fst_zero, inner_zero_left]
    · apply hj₁.eq_of_inner_left ℂ
      intro t
      rw [hqClosure x hx t, hx₀]
      simp only [Prod.snd_zero, inner_zero_left]
  let D := C.toLinearPMap
  have hgraph : D.graph = C := C.toLinearPMap_graph_eq hfunctional
  refine ⟨D, hgraph, ?_, ?_⟩
  · change IsClosed (D.graph : Set (E × F₀ × F₁))
    rw [hgraph]
    exact J.isClosed_topologicalClosure
  · -- Every point of the original input image belongs to this exact graph-closure domain.
    apply hi.mono
    rintro _ ⟨s, rfl⟩
    change i s ∈ C.map (LinearMap.fst ℂ E (F₀ × F₁))
    exact ⟨(i s, p s, q s), J.le_topologicalClosure ⟨s, rfl⟩, rfl⟩

end AtiyahSinger
