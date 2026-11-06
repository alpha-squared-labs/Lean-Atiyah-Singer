/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockGraph
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The closed graded matrix on its two simultaneous domains

Public module ID: M0705.

Two closed joint operators retain the horizontal and vertical output together.
Their cancelling cross pairings give an actual closed graded operator whose
domain is exactly the product of the two supplied joint domains. This is the
functional-analytic assembly for the associated-bundle smooth graph closures;
it does not assume that those domains equal intersections of separate closures.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]

/-- The same two closed joint graphs define a closed graded matrix on their exact product domain. -/
theorem exists_closed_gradedJointOperator
    (P : E₀ →ₗ.[ℂ] (F₀ × F₁)) (Q : E₁ →ₗ.[ℂ] (F₀ × F₁))
    (hP : P.IsClosed) (hQ : Q.IsClosed)
    (hcross : ∀ (u : P.domain) (v : Q.domain),
      inner ℂ (P u).1 (Q v).1 = inner ℂ (P u).2 (Q v).2) :
    ∃ D : WithLp 2 (E₀ × E₁) →ₗ.[ℂ] WithLp 2 (F₀ × F₁),
      D.IsClosed ∧
      D.domain = (P.domain.prod Q.domain).comap
        (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toLinearMap ∧
      ∀ (u : P.domain) (v : Q.domain),
        (WithLp.toLp 2 (u.val, v.val),
          WithLp.toLp 2 ((P u).1 - (Q v).1, (P u).2 + (Q v).2)) ∈ D.graph := by
  let X := E₀ × F₀ × F₁
  let Y := E₁ × F₀ × F₁
  let Even := WithLp 2 (E₀ × E₁)
  let Odd := WithLp 2 (F₀ × F₁)
  -- This exact coordinate map keeps the prescribed minus sign and both input coordinates.
  let f : X × Y →L[ℂ] Even × Odd := {
    toFun z := (WithLp.toLp 2 (z.1.1, z.2.1),
      WithLp.toLp 2 (z.1.2.1 - z.2.2.1, z.1.2.2 + z.2.2.2))
    map_add' z w := by
      apply Prod.ext <;> apply WithLp.ofLp_injective
      · rfl
      · change ((z.1.2.1 + w.1.2.1) - (z.2.2.1 + w.2.2.1),
          (z.1.2.2 + w.1.2.2) + (z.2.2.2 + w.2.2.2)) =
          ((z.1.2.1 - z.2.2.1) + (w.1.2.1 - w.2.2.1),
            (z.1.2.2 + z.2.2.2) + (w.1.2.2 + w.2.2.2))
        congr 1 <;> abel
    map_smul' a z := by
      apply Prod.ext <;> apply WithLp.ofLp_injective
      · rfl
      · change (a • z.1.2.1 - a • z.2.2.1, a • z.1.2.2 + a • z.2.2.2) =
          (a • (z.1.2.1 - z.2.2.1), a • (z.1.2.2 + z.2.2.2))
        rw [smul_sub, smul_add]
    cont := by dsimp only [X, Y]; fun_prop }
  let G := (P.graph.prod Q.graph).map f.toLinearMap
  have henergy : ∀ x ∈ P.graph, ∀ y ∈ Q.graph,
      inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2 := by
    intro x hx y hy
    obtain ⟨u, rfl⟩ := P.mem_graph_iff'.mp hx
    obtain ⟨v, rfl⟩ := Q.mem_graph_iff'.mp hy
    exact hcross u v
  have hGclosed : IsClosed (G : Set (Even × Odd)) := by
    have h := map_jointGraphClosure_of_inner_eq P.graph Q.graph f (fun _ _ ↦ rfl) henergy
    rw [hP.submodule_topologicalClosure_eq, hQ.submodule_topologicalClosure_eq] at h
    change G = G.topologicalClosure at h
    rw [h]
    exact G.isClosed_topologicalClosure
  -- Functionality comes from the supplied two operators, not from the energy bound alone.
  have hfunctional (z : Even × Odd) (hz : z ∈ G) (hz₀ : z.1 = 0) : z.2 = 0 := by
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := hz
    have hxy := congrArg WithLp.ofLp hz₀
    have hx₀ : x.1 = 0 := congrArg Prod.fst hxy
    have hy₀ : y.1 = 0 := congrArg Prod.snd hxy
    have hxout := P.graph_fst_eq_zero_snd hx hx₀
    have hyout := Q.graph_fst_eq_zero_snd hy hy₀
    apply WithLp.ofLp_injective
    change (x.2.1 - y.2.1, x.2.2 + y.2.2) = (0, 0)
    rw [hxout, hyout]
    simp
  let D := G.toLinearPMap
  have hgraph : D.graph = G := G.toLinearPMap_graph_eq hfunctional
  refine ⟨D, ?_, ?_, ?_⟩
  · change IsClosed (D.graph : Set (Even × Odd))
    rwa [hgraph]
  · -- Projection of the same graph gives exactly the two original simultaneous domains.
    ext z
    change z ∈ D.domain ↔ z.ofLp.1 ∈ P.domain ∧ z.ofLp.2 ∈ Q.domain
    rw [LinearPMap.mem_domain_iff, hgraph]
    constructor
    · rintro ⟨w, ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩⟩
      have hin := congrArg (fun t : Even × Odd ↦ WithLp.ofLp t.1) hxy
      have hx₀ : x.1 = z.ofLp.1 := congrArg Prod.fst hin
      have hy₀ : y.1 = z.ofLp.2 := congrArg Prod.snd hin
      exact ⟨hx₀ ▸ LinearPMap.mem_domain_of_mem_graph hx,
        hy₀ ▸ LinearPMap.mem_domain_of_mem_graph hy⟩
    · rintro ⟨hz₀, hz₁⟩
      let u : P.domain := ⟨z.ofLp.1, hz₀⟩
      let v : Q.domain := ⟨z.ofLp.2, hz₁⟩
      refine ⟨WithLp.toLp 2 ((P u).1 - (Q v).1, (P u).2 + (Q v).2),
        ⟨((u.val, P u), (v.val, Q v)), ⟨P.mem_graph u, Q.mem_graph v⟩, ?_⟩⟩
      apply Prod.ext
      · exact WithLp.toLp_ofLp 2 z
      · rfl
  · intro u v
    rw [hgraph]
    exact ⟨((u.val, P u), (v.val, Q v)), ⟨P.mem_graph u, Q.mem_graph v⟩, rfl⟩

end AtiyahSinger
