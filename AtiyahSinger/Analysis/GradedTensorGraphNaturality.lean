/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorOperator

/-!
# Naturality of the entire closed graded tensor graph

Public module ID: M0714.

Bounded maps preserving both factor graphs and their actual adjoint graphs
preserve the original graded tensor graph. The proof uses the two signed
core columns and then the closure of that same graph. It applies to each
element of the independent geometric group actions without a new domain.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open UniformSpace
open scoped TensorProduct

variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)

local notation "Even" =>
  WithLp 2 (HilbertTensorProduct H₀ K₀ × HilbertTensorProduct H₁ K₁)
local notation "Odd" =>
  WithLp 2 (HilbertTensorProduct H₁ K₀ × HilbertTensorProduct H₀ K₁)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Graph intertwiners for both factors and adjoints preserve the full graded tensor graph. -/
theorem gradedTensorOperator_graph_map
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed)
    (A₀ : H₀ →L[ℂ] H₀) (A₁ : H₁ →L[ℂ] H₁)
    (B₀ : K₀ →L[ℂ] K₀) (B₁ : K₁ →L[ℂ] K₁)
    (hP : ∀ z ∈ P.graph, (A₀ z.1, A₁ z.2) ∈ P.graph)
    (hP' : ∀ z ∈ P.adjoint.graph, (A₁ z.1, A₀ z.2) ∈ P.adjoint.graph)
    (hQ : ∀ z ∈ Q.graph, (B₀ z.1, B₁ z.2) ∈ Q.graph)
    (hQ' : ∀ z ∈ Q.adjoint.graph, (B₁ z.1, B₀ z.2) ∈ Q.adjoint.graph)
    (z : Even × Odd) (hz : z ∈ (gradedTensorOperator P Q).graph) :
    (WithLp.toLp 2
        (hilbertTensorMap A₀ B₀ (WithLp.ofLp z.1).1,
          hilbertTensorMap A₁ B₁ (WithLp.ofLp z.1).2),
      WithLp.toLp 2
        (hilbertTensorMap A₁ B₀ (WithLp.ofLp z.2).1,
          hilbertTensorMap A₀ B₁ (WithLp.ofLp z.2).2)) ∈
      (gradedTensorOperator P Q).graph := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ
    (HilbertTensorProduct H₀ K₀) (HilbertTensorProduct H₁ K₁)
  let o := WithLp.prodContinuousLinearEquiv 2 ℂ
    (HilbertTensorProduct H₁ K₀) (HilbertTensorProduct H₀ K₁)
  let Ae := e.symm.toContinuousLinearMap.comp
    (((hilbertTensorMap A₀ B₀).prodMap (hilbertTensorMap A₁ B₁)).comp e.toContinuousLinearMap)
  let Ao := o.symm.toContinuousLinearMap.comp
    (((hilbertTensorMap A₁ B₀).prodMap (hilbertTensorMap A₀ B₁)).comp o.toContinuousLinearMap)
  let T := Ae.prodMap Ao
  let S := gradedTensorGraph P Q
  have hT (w : Even × Odd) : T w =
      (WithLp.toLp 2 (hilbertTensorMap A₀ B₀ (WithLp.ofLp w.1).1,
        hilbertTensorMap A₁ B₁ (WithLp.ofLp w.1).2),
      WithLp.toLp 2 (hilbertTensorMap A₁ B₀ (WithLp.ofLp w.2).1,
        hilbertTensorMap A₀ B₁ (WithLp.ofLp w.2).2)) := rfl
  -- Each original domain pair maps to another original domain pair with the same operator value.
  have hcore : S ≤ S.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro w (⟨⟨u, v⟩, rfl⟩ | ⟨⟨u, v⟩, rfl⟩)
    · obtain ⟨u', hu'⟩ := P.mem_graph_iff'.mp
        (hP (u.val, P u) (P.mem_graph_iff'.mpr ⟨u, rfl⟩))
      obtain ⟨v', hv'⟩ := Q.mem_graph_iff'.mp
        (hQ (v.val, Q v) (Q.mem_graph_iff'.mpr ⟨v, rfl⟩))
      have hu₀ : u'.val = A₀ u.val := congrArg Prod.fst hu'
      have hu₁ : P u' = A₁ (P u) := congrArg Prod.snd hu'
      have hv₀ : v'.val = B₀ v.val := congrArg Prod.fst hv'
      have hv₁ : Q v' = B₁ (Q v) := congrArg Prod.snd hv'
      change T _ ∈ S
      apply Submodule.subset_span
      left
      refine ⟨(u', v'), ?_⟩
      rw [hT]
      dsimp only [WithLp.ofLp_toLp]
      simp only [hilbertTensorMap, Completion.coe_toComplL,
        ContinuousLinearMap.completion_apply_coe,
        TensorProduct.mapL_tmul, map_zero, hu₀, hu₁, hv₀, hv₁]
    · obtain ⟨u', hu'⟩ := P.adjoint.mem_graph_iff'.mp
        (hP' (u.val, P.adjoint u) (P.adjoint.mem_graph_iff'.mpr ⟨u, rfl⟩))
      obtain ⟨v', hv'⟩ := Q.adjoint.mem_graph_iff'.mp
        (hQ' (v.val, Q.adjoint v) (Q.adjoint.mem_graph_iff'.mpr ⟨v, rfl⟩))
      have hu₀ : u'.val = A₁ u.val := congrArg Prod.fst hu'
      have hu₁ : P.adjoint u' = A₀ (P.adjoint u) := congrArg Prod.snd hu'
      have hv₀ : v'.val = B₁ v.val := congrArg Prod.fst hv'
      have hv₁ : Q.adjoint v' = B₀ (Q.adjoint v) := congrArg Prod.snd hv'
      change T _ ∈ S
      apply Submodule.subset_span
      right
      refine ⟨(u', v'), ?_⟩
      rw [hT]
      dsimp only [WithLp.ofLp_toLp]
      simp only [hilbertTensorMap, map_neg, Completion.coe_toComplL,
        ContinuousLinearMap.completion_apply_coe,
        TensorProduct.mapL_tmul, map_zero, hu₀, hu₁, hv₀, hv₁]
  -- The same bounded block maps preserve the closure of the original signed core graph.
  change T z ∈ (gradedTensorOperator P Q).graph
  rw [(gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed).2.1] at hz ⊢
  exact map_mem_closure T.continuous hz (fun _ hw ↦ hcore hw)

end AtiyahSinger
