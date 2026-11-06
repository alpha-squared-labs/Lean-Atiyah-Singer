/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Formal adjunction on the original closed graph domains

Public module ID: M0335.

A pairing identity on two smooth cores extends to their two specified graph
closures by continuity in the graph coordinates. This retains the actual
domains and gives formal adjunction there. It does not identify either closed
domain with the full domain of the other operator's Hilbert adjoint.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E F S T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]

/-- The original smooth pairing extends to the two exact simultaneous graph closures. -/
theorem LinearPMap.isFormalAdjoint_of_graph_eq_closure
    (i : S →ₗ[ℂ] E) (j : T →ₗ[ℂ] F) (p : S →ₗ[ℂ] F) (q : T →ₗ[ℂ] E)
    (D : E →ₗ.[ℂ] F) (A : F →ₗ.[ℂ] E)
    (hD : D.graph = (i.prod p).range.topologicalClosure)
    (hA : A.graph = (j.prod q).range.topologicalClosure)
    (hpair : ∀ s t, inner ℂ (p s) (j t) = inner ℂ (i s) (q t)) :
    D.IsFormalAdjoint A := by
  have hgraph (x : E × F) (hx : x ∈ D.graph)
      (y : F × E) (hy : y ∈ A.graph) : inner ℂ x.2 y.1 = inner ℂ x.1 y.2 := by
    rw [hD] at hx
    rw [hA] at hy
    -- First extend in the second graph variable, keeping the first graph point fixed.
    have hyclosed : IsClosed {y : F × E | inner ℂ x.2 y.1 = inner ℂ x.1 y.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hyclosed.closure_subset_iff.mpr ?_ hy
    rintro _ ⟨t, rfl⟩
    -- For each original second-core section, continuity extends the first variable.
    have hxclosed : IsClosed {x : E × F | inner ℂ x.2 (j t) = inner ℂ x.1 (q t)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hxclosed.closure_subset_iff.mpr ?_ hx
    rintro _ ⟨s, rfl⟩
    exact hpair s t
  intro u v
  exact hgraph (u.val, D u) (D.mem_graph u) (v.val, A v) (A.mem_graph v)

end AtiyahSinger
