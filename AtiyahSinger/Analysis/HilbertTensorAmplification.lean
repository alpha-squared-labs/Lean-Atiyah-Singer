/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorApproximation

/-!
# The actual closed tensor amplifications

Public module ID: M0730.

Bounded graph approximation proves that closing either original factor tensor
graph remains functional. Thus the partial-map and closure constructions retain
the specified graph, including their original domain inclusions and actions.
-/

@[expose] public noncomputable section

open Filter UniformSpace
open scoped TensorProduct Topology

namespace Submodule

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Bounded intertwining approximations rule out a vertical vector in the closed graph. -/
theorem toLinearPMap_closure_graph_eq_of_approximation (G : Submodule ℂ (E × F))
    (A : ℕ → E →L[ℂ] F) (S : ℕ → F →L[ℂ] F)
    (hintertwine : ∀ n (z : E × F), z ∈ G → A n z.1 = S n z.2)
    (hS : ∀ y : F, Tendsto (fun n ↦ S n y) atTop (𝓝 y)) :
    G.toLinearPMap.closure.graph = G.topologicalClosure := by
  have hfunctional (z : E × F) (hz : z ∈ G.topologicalClosure) (hzero : z.1 = 0) :
      z.2 = 0 := by
    have hSn (n : ℕ) : S n z.2 = 0 := by
      have hclosed : IsClosed {z : E × F | A n z.1 = S n z.2} :=
        isClosed_eq (by fun_prop) (by fun_prop)
      have h := hclosed.closure_subset_iff.mpr (fun z hz ↦ hintertwine n z hz) hz
      change A n z.1 = S n z.2 at h
      rw [hzero, map_zero] at h
      exact h.symm
    exact tendsto_nhds_unique (hS z.2) (by simpa only [hSn] using tendsto_const_nhds)
  -- Both potentially partial constructions therefore keep their literal graph.
  have hgraph : G.toLinearPMap.graph = G :=
    G.toLinearPMap_graph_eq fun z hz hzero ↦
      hfunctional z (G.le_topologicalClosure hz) hzero
  have hclosedGraph : G.topologicalClosure.toLinearPMap.graph = G.topologicalClosure :=
    G.topologicalClosure.toLinearPMap_graph_eq hfunctional
  have hclosable : G.toLinearPMap.IsClosable :=
    ⟨G.topologicalClosure.toLinearPMap, by rw [hgraph, hclosedGraph]⟩
  rw [← hclosable.graph_closure_eq_closure_graph, hgraph]

end Submodule

namespace LinearPMap

variable {E E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

/-- Closing the original left tensor graph yields precisely its topological closure. -/
theorem left_tensor_closure_graph (P : E →ₗ.[ℂ] E')
    (hP : P.IsClosed) (hPdense : Dense (P.domain : Set E))
    (hPadjoint : Dense (P.adjoint.domain : Set E'))
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    let G := Submodule.span ℂ (Set.range fun z : P.domain × F ↦
      ((((z.1 : E) ⊗ₜ[ℂ] z.2 : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F)),
        ((P z.1 ⊗ₜ[ℂ] z.2 : E' ⊗[ℂ] F) : Completion (E' ⊗[ℂ] F))))
    G.toLinearPMap.closure.graph = G.topologicalClosure := by
  dsimp only
  obtain ⟨R, A, S, hbound, hgraph, hcomm, hR, hS⟩ :=
    P.exists_graph_approximation hP hPdense hPadjoint
  apply Submodule.toLinearPMap_closure_graph_eq_of_approximation
    (A := fun n ↦ (TensorProduct.mapL (A n) (ContinuousLinearMap.id ℂ F)).completion)
    (S := fun n ↦ (TensorProduct.mapL (S n) (ContinuousLinearMap.id ℂ F)).completion)
  · intro n z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul, hcomm]
    | zero => simp
    | add x y hx hy h₁ h₂ =>
      simp only [Prod.fst_add, Prod.snd_add, _root_.map_add, h₁, h₂]
    | smul a x hx h₁ =>
      simp only [Prod.smul_fst, Prod.smul_snd, _root_.map_smul, h₁]
  · intro y
    exact TensorProduct.tendsto_completion_mapL_of_contractions S
      (fun _ ↦ ContinuousLinearMap.id ℂ F) (fun n ↦ (hbound n).2)
      (fun _ ↦ ContinuousLinearMap.norm_id_le) hS (fun _ ↦ tendsto_const_nhds) y

/-- Closing the original right tensor graph yields precisely its topological closure. -/
theorem right_tensor_closure_graph (P : E →ₗ.[ℂ] E')
    (hP : P.IsClosed) (hPdense : Dense (P.domain : Set E))
    (hPadjoint : Dense (P.adjoint.domain : Set E'))
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    let G := Submodule.span ℂ (Set.range fun z : F × P.domain ↦
      (((z.1 ⊗ₜ[ℂ] (z.2 : E) : F ⊗[ℂ] E) : Completion (F ⊗[ℂ] E)),
        ((z.1 ⊗ₜ[ℂ] P z.2 : F ⊗[ℂ] E') : Completion (F ⊗[ℂ] E'))))
    G.toLinearPMap.closure.graph = G.topologicalClosure := by
  dsimp only
  obtain ⟨R, A, S, hbound, hgraph, hcomm, hR, hS⟩ :=
    P.exists_graph_approximation hP hPdense hPadjoint
  apply Submodule.toLinearPMap_closure_graph_eq_of_approximation
    (A := fun n ↦ (TensorProduct.mapL (ContinuousLinearMap.id ℂ F) (A n)).completion)
    (S := fun n ↦ (TensorProduct.mapL (ContinuousLinearMap.id ℂ F) (S n)).completion)
  · intro n z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul, hcomm]
    | zero => simp
    | add x y hx hy h₁ h₂ =>
      simp only [Prod.fst_add, Prod.snd_add, _root_.map_add, h₁, h₂]
    | smul a x hx h₁ =>
      simp only [Prod.smul_fst, Prod.smul_snd, _root_.map_smul, h₁]
  · intro y
    exact TensorProduct.tendsto_completion_mapL_of_contractions
      (fun _ ↦ ContinuousLinearMap.id ℂ F) S
      (fun _ ↦ ContinuousLinearMap.norm_id_le) (fun n ↦ (hbound n).2)
      (fun _ ↦ tendsto_const_nhds) hS y

end LinearPMap
