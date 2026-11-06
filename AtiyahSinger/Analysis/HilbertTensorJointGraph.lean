/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorApproximation

/-!
# Simultaneous approximation of the two factor graphs

Public module ID: M0734.

Finite tensors from the original operator domains approximate a vector in the
intersection of the two closed tensor graphs, together with both operator images.
The bounded graph contractions commute because they act in different factors.
Their bounded off-diagonal blocks turn ambient tensor approximation into graph
approximation; their target contractions preserve the specified operator images.
-/

@[expose] public noncomputable section

namespace TensorProduct

open Filter UniformSpace
open scoped TensorProduct Topology

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']

/-- The graph of both factor actions on the original finite tensor core. -/
def jointGraph (P : E →ₗ.[ℂ] E') (Q : F →ₗ.[ℂ] F') :
    Submodule ℂ (Completion (E ⊗[ℂ] F) ×
      Completion (E' ⊗[ℂ] F) × Completion (E ⊗[ℂ] F')) :=
  Submodule.span ℂ (Set.range fun z : P.domain × Q.domain ↦
    ((((z.1 : E) ⊗ₜ[ℂ] (z.2 : F) : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F)),
      (((P z.1 ⊗ₜ[ℂ] (z.2 : F) : E' ⊗[ℂ] F) : Completion (E' ⊗[ℂ] F)),
        ((((z.1 : E) ⊗ₜ[ℂ] Q z.2 : E ⊗[ℂ] F') : Completion (E ⊗[ℂ] F'))))))

/-- A common input and both closed factor graph images belong to the joint graph closure. -/
theorem mem_topologicalClosure_joint_graph
    (P : E →ₗ.[ℂ] E') (Q : F →ₗ.[ℂ] F')
    (hP : P.IsClosed) (hQ : Q.IsClosed)
    (hPdense : Dense (P.domain : Set E)) (hQdense : Dense (Q.domain : Set F))
    (hPadjoint : Dense (P.adjoint.domain : Set E'))
    (hQadjoint : Dense (Q.adjoint.domain : Set F'))
    (u : Completion (E ⊗[ℂ] F)) (v : Completion (E' ⊗[ℂ] F))
    (w : Completion (E ⊗[ℂ] F'))
    (hleft : (u, v) ∈ (Submodule.span ℂ (Set.range fun z : P.domain × F ↦
      ((((z.1 : E) ⊗ₜ[ℂ] z.2 : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F)),
        ((P z.1 ⊗ₜ[ℂ] z.2 : E' ⊗[ℂ] F) : Completion (E' ⊗[ℂ] F))))).topologicalClosure)
    (hright : (u, w) ∈ (Submodule.span ℂ (Set.range fun z : E × Q.domain ↦
      (((z.1 ⊗ₜ[ℂ] (z.2 : F) : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F)),
        ((z.1 ⊗ₜ[ℂ] Q z.2 : E ⊗[ℂ] F') : Completion (E ⊗[ℂ] F'))))).topologicalClosure) :
    (u, (v, w)) ∈ (jointGraph P Q).topologicalClosure := by
  obtain ⟨R, A, S, hbound, hgraph, hcomm, hR, hS⟩ :=
    P.exists_graph_approximation hP hPdense hPadjoint
  obtain ⟨R', A', S', hbound', hgraph', hcomm', hR', hS'⟩ :=
    Q.exists_graph_approximation hQ hQdense hQadjoint
  let J := jointGraph P Q
  let C := J.topologicalClosure
  -- Each bounded regularization lies in the closure of the same joint tensor graph.
  have hregularized (n : ℕ) (t : Completion (E ⊗[ℂ] F)) :
      ((mapL (R n) (R' n)).completion t,
        ((mapL (A n) (R' n)).completion t, (mapL (R n) (A' n)).completion t)) ∈ C := by
    refine Completion.induction_on (p := fun t ↦
      ((mapL (R n) (R' n)).completion t,
        ((mapL (A n) (R' n)).completion t, (mapL (R n) (A' n)).completion t)) ∈ C)
      t (J.isClosed_topologicalClosure.preimage (by fun_prop)) ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨x', hx, hAx⟩ := P.mem_graph_iff.mp (hgraph n x)
      obtain ⟨y', hy, hAy⟩ := Q.mem_graph_iff.mp (hgraph' n y)
      dsimp only [Prod.fst, Prod.snd] at hx hy hAx hAy
      simp only [ContinuousLinearMap.completion_apply_coe, mapL_tmul]
      rw [← hx, ← hy, ← hAx, ← hAy]
      exact J.le_topologicalClosure (Submodule.subset_span ⟨(x', y'), rfl⟩)
    | add x y hx hy =>
      simpa only [Completion.coe_add, _root_.map_add, Prod.mk_add_mk] using C.add_mem hx hy
  -- The left regularizer intertwines the actual left image on the entire closed graph.
  have hleft_image (n : ℕ) :
      (mapL (A n) (R' n)).completion u = (mapL (S n) (R' n)).completion v := by
    have hclosed : IsClosed {z : Completion (E ⊗[ℂ] F) × Completion (E' ⊗[ℂ] F) |
        (mapL (A n) (R' n)).completion z.1 =
          (mapL (S n) (R' n)).completion z.2} := isClosed_eq (by fun_prop) (by fun_prop)
    apply hclosed.closure_subset_iff.mpr ?_ hleft
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      simp only [Set.mem_ofPred_eq, ContinuousLinearMap.completion_apply_coe, mapL_tmul,
        hcomm]
    | zero => simp
    | add x y hx hy h₁ h₂ =>
      change (mapL (A n) (R' n)).completion x.1 =
        (mapL (S n) (R' n)).completion x.2 at h₁
      change (mapL (A n) (R' n)).completion y.1 =
        (mapL (S n) (R' n)).completion y.2 at h₂
      simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, _root_.map_add, h₁, h₂]
    | smul a x hx h₁ =>
      change (mapL (A n) (R' n)).completion x.1 =
        (mapL (S n) (R' n)).completion x.2 at h₁
      simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, _root_.map_smul, h₁]
  -- The right image is treated in its own factor, with the identical original domain.
  have hright_image (n : ℕ) :
      (mapL (R n) (A' n)).completion u = (mapL (R n) (S' n)).completion w := by
    have hclosed : IsClosed {z : Completion (E ⊗[ℂ] F) × Completion (E ⊗[ℂ] F') |
        (mapL (R n) (A' n)).completion z.1 =
          (mapL (R n) (S' n)).completion z.2} := isClosed_eq (by fun_prop) (by fun_prop)
    apply hclosed.closure_subset_iff.mpr ?_ hright
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      simp only [Set.mem_ofPred_eq, ContinuousLinearMap.completion_apply_coe, mapL_tmul,
        hcomm']
    | zero => simp
    | add x y hx hy h₁ h₂ =>
      change (mapL (R n) (A' n)).completion x.1 =
        (mapL (R n) (S' n)).completion x.2 at h₁
      change (mapL (R n) (A' n)).completion y.1 =
        (mapL (R n) (S' n)).completion y.2 at h₂
      simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, _root_.map_add, h₁, h₂]
    | smul a x hx h₁ =>
      change (mapL (R n) (A' n)).completion x.1 =
        (mapL (R n) (S' n)).completion x.2 at h₁
      simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, _root_.map_smul, h₁]
  -- All three coordinates converge, because their remaining factor maps are contractions.
  have hu := tendsto_completion_mapL_of_contractions R R'
    (fun n ↦ (hbound n).1) (fun n ↦ (hbound' n).1) hR hR' u
  have hv := tendsto_completion_mapL_of_contractions S R'
    (fun n ↦ (hbound n).2) (fun n ↦ (hbound' n).1) hS hR' v
  have hw := tendsto_completion_mapL_of_contractions R S'
    (fun n ↦ (hbound n).1) (fun n ↦ (hbound' n).2) hR hS' w
  apply J.isClosed_topologicalClosure.mem_of_tendsto (hu.prodMk_nhds (hv.prodMk_nhds hw))
  exact Filter.Eventually.of_forall fun n ↦ by
    rw [← hleft_image n, ← hright_image n]
    exact hregularized n u

end TensorProduct
