/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Orthogonal characterization of a closed operator's kernel

Public module ID: M0342.

For a closed densely defined Hilbert space operator, the kernel is precisely
the annihilator of the actual adjoint range. Closedness is used on the original
graph through the double orthogonal theorem. No closed-range hypothesis is needed.
This is the unbounded counterpart of the standard bounded-operator identity and
is used in the kernel calculation for the graded Hilbert tensor operator.
-/

@[expose] public noncomputable section

namespace LinearPMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The kernel of the actual adjoint annihilates exactly the original operator range. -/
theorem ker_adjoint_eq_orthogonal_range (T : E →ₗ.[ℂ] F)
    (hT : Dense (T.domain : Set E)) :
    T.adjoint.ker = T.toFun.range.orthogonal := by
  apply le_antisymm
  · intro y hy x hx
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl, hv⟩ := T.adjoint.mem_ker_iff.mp hy
    change inner ℂ (T u) (v : F) = 0
    rw [(T.adjoint_isFormalAdjoint hT).symm u v, hv, inner_zero_right]
  · intro y hy
    have hrepresent (x : T.domain) : inner ℂ (0 : E) (x : E) = inner ℂ y (T x) := by
      have h := hy (T x) ⟨x, rfl⟩
      rw [inner_zero_left, ← inner_conj_symm]
      simpa only [_root_.map_zero] using (congrArg (starRingEnd ℂ) h).symm
    have hdomain : y ∈ T.adjoint.domain := by
      apply T.mem_adjoint_domain_of_exists
      exact ⟨0, hrepresent⟩
    exact T.adjoint.mem_ker_iff.mpr
      ⟨⟨y, hdomain⟩, rfl, T.adjoint_apply_eq hT _ hrepresent⟩

/-- A closed densely defined operator's kernel is the orthogonal of its actual adjoint range. -/
theorem ker_eq_orthogonal_adjoint_range (T : E →ₗ.[ℂ] F)
    (hT : Dense (T.domain : Set E)) (hclosed : T.IsClosed) :
    T.ker = T.adjoint.toFun.range.orthogonal := by
  let G := T.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  have hG : _root_.IsClosed (G : Set (WithLp 2 (E × F))) :=
    hclosed.preimage (WithLp.prod_continuous_ofLp 2 E F)
  apply le_antisymm
  · intro x hx y hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨u, rfl, hu⟩ := T.mem_ker_iff.mp hx
    have h := T.adjoint_isFormalAdjoint hT z u
    change inner ℂ (T.adjoint z) (u : E) = 0
    simpa only [hu, inner_zero_right] using h
  · intro x hx
    -- A graph-orthogonal vector represents an adjoint-domain vector with the opposite first entry.
    have hdouble : WithLp.toLp 2 (x, (0 : F)) ∈ G.orthogonal.orthogonal := by
      intro w hw
      have hrepresent (u : T.domain) :
          inner ℂ (-(WithLp.ofLp w).1) (u : E) =
            inner ℂ (WithLp.ofLp w).2 (T u) := by
        have huG : WithLp.toLp 2 ((u : E), T u) ∈ G := mem_graph T u
        have h := hw _ huG
        simp only [WithLp.prod_inner_apply] at h
        have hc := congrArg (starRingEnd ℂ) h
        simp only [_root_.map_add, inner_conj_symm, _root_.map_zero] at hc
        rw [inner_neg_left]
        exact neg_eq_iff_add_eq_zero.mpr hc
      have hdomain : (WithLp.ofLp w).2 ∈ T.adjoint.domain := by
        apply T.mem_adjoint_domain_of_exists
        exact ⟨-(WithLp.ofLp w).1, hrepresent⟩
      have hvalue : T.adjoint ⟨(WithLp.ofLp w).2, hdomain⟩ = -(WithLp.ofLp w).1 :=
        T.adjoint_apply_eq hT _ hrepresent
      have hann := hx (T.adjoint ⟨(WithLp.ofLp w).2, hdomain⟩)
        ⟨⟨(WithLp.ofLp w).2, hdomain⟩, rfl⟩
      rw [hvalue, inner_neg_left, neg_eq_zero] at hann
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, inner_zero_right, add_zero]
        using hann
    -- Closedness returns (x,0) to the same graph, and thus to the original kernel.
    rw [Submodule.orthogonal_orthogonal_eq_closure, hG.submodule_topologicalClosure_eq]
      at hdouble
    have hg : (x, (0 : F)) ∈ T.graph := hdouble
    obtain ⟨u, hu, hval⟩ := T.mem_graph_iff.mp hg
    exact T.mem_ker_iff.mpr ⟨u, hu.symm, hval⟩

end LinearPMap
