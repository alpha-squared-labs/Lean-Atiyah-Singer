/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedTensorJointEnergy
public import AtiyahSinger.Analysis.HilbertTensorAmplification
public import AtiyahSinger.Analysis.HilbertTensorOperator
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The full joint domain of the closed graded tensor operator

Public module ID: M0733.

UL01: the left and right tensor amplifications close the graphs of the
factor operators on their pure-tensor domains. Their common domain defines
the matrix with the same signs as `gradedTensorOperator`. For closed densely
defined factors, this joint-domain matrix equals the closure of the graded
core, and the energy identity holds on its entire domain.

The proof uses simultaneous graph-projection approximation and the energy
identity on the two joint graph closures. No closed-range assumption or
finite-dimensional kernel is needed. The comparison with a geometric
product H¹ model is handled separately.

Source: SG III.13.5, (13.12)–(13.14), pp.249–250. The explicit joint-domain
formulation is a project supplement to the unbounded Hilbert tensor argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

/-- Close the actual graph of P tensor the identity on finite domain pure-tensor sums. -/
def hilbertTensorLeftOperator {H₀ H₁ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    (P : H₀ →ₗ.[ℂ] H₁) (K : Type*)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    HilbertTensorProduct H₀ K →ₗ.[ℂ] HilbertTensorProduct H₁ K :=
  (Submodule.span ℂ (Set.range fun z : P.domain × K ↦
    ((UniformSpace.Completion.toComplL (S := ℂ) (α := H₀ ⊗[ℂ] K))
        ((z.1 : H₀) ⊗ₜ[ℂ] z.2),
      (UniformSpace.Completion.toComplL (S := ℂ) (α := H₁ ⊗[ℂ] K))
        (P z.1 ⊗ₜ[ℂ] z.2)))).toLinearPMap.closure

/-- Close the actual graph of the identity tensor Q on finite domain pure-tensor sums. -/
def hilbertTensorRightOperator (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {K₀ K₁ : Type*}
    [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
    [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    (Q : K₀ →ₗ.[ℂ] K₁) :
    HilbertTensorProduct H K₀ →ₗ.[ℂ] HilbertTensorProduct H K₁ :=
  (Submodule.span ℂ (Set.range fun z : H × Q.domain ↦
    ((UniformSpace.Completion.toComplL (S := ℂ) (α := H ⊗[ℂ] K₀))
        (z.1 ⊗ₜ[ℂ] (z.2 : K₀)),
      (UniformSpace.Completion.toComplL (S := ℂ) (α := H ⊗[ℂ] K₁))
        (z.1 ⊗ₜ[ℂ] Q z.2)))).toLinearPMap.closure

variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [hH₀ : CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [hH₁ : CompleteSpace H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [hK₀ : CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [hK₁ : CompleteSpace K₁]
  (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)

local notation "H₀₀" => HilbertTensorProduct H₀ K₀
local notation "H₁₀" => HilbertTensorProduct H₁ K₀
local notation "H₀₁" => HilbertTensorProduct H₀ K₁
local notation "H₁₁" => HilbertTensorProduct H₁ K₁
local notation "Even" => WithLp 2 (H₀₀ × H₁₁)
local notation "Odd" => WithLp 2 (H₁₀ × H₀₁)

/-- The simultaneous domains of both factor operators in each original even tensor summand. -/
def gradedTensorJointDomain : Submodule ℂ Even :=
  let fst : Even →ₗ[ℂ] H₀₀ :=
    (LinearMap.fst ℂ H₀₀ H₁₁).comp (WithLp.linearEquiv 2 ℂ (H₀₀ × H₁₁)).toLinearMap
  let snd : Even →ₗ[ℂ] H₁₁ :=
    (LinearMap.snd ℂ H₀₀ H₁₁).comp (WithLp.linearEquiv 2 ℂ (H₀₀ × H₁₁)).toLinearMap
  ((hilbertTensorLeftOperator P K₀).domain ⊓
      (hilbertTensorRightOperator H₀ Q).domain).comap fst ⊓
    ((hilbertTensorLeftOperator P.adjoint K₁).domain ⊓
      (hilbertTensorRightOperator H₁ Q.adjoint).domain).comap snd

/-- The original graded matrix acting on the full simultaneous factor domain. -/
def gradedTensorJointOperator : Even →ₗ.[ℂ] Odd where
  domain := gradedTensorJointDomain P Q
  toFun := by
    -- Restrict the two original even coordinates to each actual amplified domain.
    let fst : Even →ₗ[ℂ] H₀₀ :=
      (LinearMap.fst ℂ H₀₀ H₁₁).comp (WithLp.linearEquiv 2 ℂ (H₀₀ × H₁₁)).toLinearMap
    let snd : Even →ₗ[ℂ] H₁₁ :=
      (LinearMap.snd ℂ H₀₀ H₁₁).comp (WithLp.linearEquiv 2 ℂ (H₀₀ × H₁₁)).toLinearMap
    let left₀ : gradedTensorJointDomain P Q →ₗ[ℂ] H₁₀ :=
      (hilbertTensorLeftOperator P K₀).toFun.comp
        (LinearMap.codRestrict (hilbertTensorLeftOperator P K₀).domain
          (fst.domRestrict (gradedTensorJointDomain P Q)) (fun z ↦ z.property.1.1))
    let right₀ : gradedTensorJointDomain P Q →ₗ[ℂ] H₀₁ :=
      (hilbertTensorRightOperator H₀ Q).toFun.comp
        (LinearMap.codRestrict (hilbertTensorRightOperator H₀ Q).domain
          (fst.domRestrict (gradedTensorJointDomain P Q)) (fun z ↦ z.property.1.2))
    let left₁ : gradedTensorJointDomain P Q →ₗ[ℂ] H₀₁ :=
      (hilbertTensorLeftOperator P.adjoint K₁).toFun.comp
        (LinearMap.codRestrict (hilbertTensorLeftOperator P.adjoint K₁).domain
          (snd.domRestrict (gradedTensorJointDomain P Q)) (fun z ↦ z.property.2.1))
    let right₁ : gradedTensorJointDomain P Q →ₗ[ℂ] H₁₀ :=
      (hilbertTensorRightOperator H₁ Q.adjoint).toFun.comp
        (LinearMap.codRestrict (hilbertTensorRightOperator H₁ Q.adjoint).domain
          (snd.domRestrict (gradedTensorJointDomain P Q)) (fun z ↦ z.property.2.2))
    -- Assemble the prescribed minus sign and the original odd summand order.
    exact (WithLp.linearEquiv 2 ℂ (H₁₀ × H₀₁)).symm.toLinearMap.comp
      ((left₀ - right₁).prod (right₀ + left₁))

include hH₀ hH₁ hK₀ hK₁

set_option maxHeartbeats 800000 in

/-- Closing the original graded core gives exactly the full joint-domain matrix. -/
theorem gradedTensorOperator_eq_jointOperator
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed) :
    gradedTensorOperator P Q = gradedTensorJointOperator P Q := by
  /- The two closed joint graph spaces retain all four factor images. Energy
  makes their signed graph map bounded below, hence its range is closed.
  Continuity and the original generators identify that range with the graded
  core closure. Projecting the joint graph spaces recovers exactly the four
  original amplified domains; simultaneous approximation proves the converse. -/
  let X := H₀₀ × H₁₀ × H₀₁
  let Y := H₁₁ × H₀₁ × H₁₀
  let J₀ := (TensorProduct.jointGraph P Q).topologicalClosure
  let J₁ := (TensorProduct.jointGraph P.adjoint Q.adjoint).topologicalClosure
  let C := J₀.prod J₁
  have hC : IsClosed (C : Set (X × Y)) :=
    (TensorProduct.jointGraph P Q).isClosed_topologicalClosure.prod
      (TensorProduct.jointGraph P.adjoint Q.adjoint).isClosed_topologicalClosure
  let : CompleteSpace C := hC.completeSpace_coe
  -- The map retains both input components and the original signed output matrix.
  let f : X × Y →L[ℂ] Even × Odd :=
    { toFun z := (WithLp.toLp 2 (z.1.1, z.2.1),
        WithLp.toLp 2 (z.1.2.1 - z.2.2.2, z.1.2.2 + z.2.2.1))
      map_add' z w := by
        apply Prod.ext <;> apply WithLp.ofLp_injective
        · change (z.1.1 + w.1.1, z.2.1 + w.2.1) = _
          rfl
        · change ((z.1.2.1 + w.1.2.1) - (z.2.2.2 + w.2.2.2),
            (z.1.2.2 + w.1.2.2) + (z.2.2.1 + w.2.2.1)) = _
          simp only [WithLp.ofLp_add, Prod.mk_add_mk]
          congr 1 <;> abel
      map_smul' a z := by
        apply Prod.ext <;> apply WithLp.ofLp_injective
        · rfl
        · change (a • z.1.2.1 - a • z.2.2.2, a • z.1.2.2 + a • z.2.2.1) = _
          simp only [WithLp.ofLp_smul, Prod.smul_mk, smul_sub, smul_add, RingHom.id_apply]
      cont := by dsimp only [X, Y]; fun_prop }
  let F := f.comp C.subtypeL
  -- Energy controls all four factor images by the single graded output norm.
  have hbound (z : C) : ‖z‖ ≤ ‖F z‖ := by
    have henergy := LinearPMap.graded_tensor_joint_energy P Q hPdense hQdense
      z.val.1 z.val.2 z.property.1 z.property.2
    have hout : ‖(f z.val).2‖ ^ 2 =
        ‖z.val.1.2.1‖ ^ 2 + ‖z.val.1.2.2‖ ^ 2 +
          ‖z.val.2.2.1‖ ^ 2 + ‖z.val.2.2.2‖ ^ 2 := by
      change ‖WithLp.toLp 2 (z.val.1.2.1 - z.val.2.2.2,
        z.val.1.2.2 + z.val.2.2.1)‖ ^ 2 = _
      rw [WithLp.prod_norm_sq_eq_of_L2]
      exact henergy
    have ha : ‖z.val.1.2.1‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.2‖, sq_nonneg ‖z.val.2.2.1‖,
        sq_nonneg ‖z.val.2.2.2‖, norm_nonneg (f z.val).2]
    have hb : ‖z.val.1.2.2‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.1‖, sq_nonneg ‖z.val.2.2.1‖,
        sq_nonneg ‖z.val.2.2.2‖, norm_nonneg (f z.val).2]
    have hc : ‖z.val.2.2.1‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.1‖, sq_nonneg ‖z.val.1.2.2‖,
        sq_nonneg ‖z.val.2.2.2‖, norm_nonneg (f z.val).2]
    have hd : ‖z.val.2.2.2‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.1‖, sq_nonneg ‖z.val.1.2.2‖,
        sq_nonneg ‖z.val.2.2.1‖, norm_nonneg (f z.val).2]
    have hx₀ : ‖z.val.1.1‖ ≤ ‖(f z.val).1‖ :=
      WithLp.norm_fst_le H₀₀ (f z.val).1
    have hx₁ : ‖z.val.2.1‖ ≤ ‖(f z.val).1‖ :=
      WithLp.norm_snd_le H₀₀ (f z.val).1
    change max (max ‖z.val.1.1‖ (max ‖z.val.1.2.1‖ ‖z.val.1.2.2‖))
        (max ‖z.val.2.1‖ (max ‖z.val.2.2.1‖ ‖z.val.2.2.2‖)) ≤
      max ‖(f z.val).1‖ ‖(f z.val).2‖
    exact max_le
      (max_le (hx₀.trans (le_max_left _ _))
        (max_le (ha.trans (le_max_right _ _)) (hb.trans (le_max_right _ _))))
      (max_le (hx₁.trans (le_max_left _ _))
        (max_le (hc.trans (le_max_right _ _)) (hd.trans (le_max_right _ _))))
  have hclosedRange : IsClosed (F.range : Set (Even × Odd)) := by
    have hanti : AntilipschitzWith 1 F := F.antilipschitz_of_bound (fun z ↦ by
      simpa only [NNReal.coe_one, one_mul] using hbound z)
    exact hanti.isClosed_range F.uniformContinuous
  have hreal := gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed
  -- The original core generators already lie in the closed range of the joint-graph map.
  have hG : gradedTensorGraph P Q ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro z (⟨⟨u, v⟩, rfl⟩ | ⟨⟨u, v⟩, rfl⟩)
    · let t : X :=
        ((↑((u : H₀) ⊗ₜ[ℂ] (v : K₀)) : H₀₀),
          ((↑(P u ⊗ₜ[ℂ] (v : K₀)) : H₁₀), (↑((u : H₀) ⊗ₜ[ℂ] Q v) : H₀₁)))
      have ht : t ∈ J₀ := (TensorProduct.jointGraph P Q).le_topologicalClosure
        (Submodule.subset_span ⟨(u, v), rfl⟩)
      refine ⟨⟨(t, 0), ⟨ht, J₁.zero_mem⟩⟩, ?_⟩
      change (WithLp.toLp 2 (t.1, 0), WithLp.toLp 2 (t.2.1 - 0, t.2.2 + 0)) = _
      simp only [sub_zero, add_zero]
      rfl
    · let t : Y :=
        ((↑((u : H₁) ⊗ₜ[ℂ] (v : K₁)) : H₁₁),
          ((↑(P.adjoint u ⊗ₜ[ℂ] (v : K₁)) : H₀₁),
            (↑((u : H₁) ⊗ₜ[ℂ] Q.adjoint v) : H₁₀)))
      have ht : t ∈ J₁ := (TensorProduct.jointGraph P.adjoint Q.adjoint).le_topologicalClosure
        (Submodule.subset_span ⟨(u, v), rfl⟩)
      refine ⟨⟨(0, t), ⟨J₀.zero_mem, ht⟩⟩, ?_⟩
      change (WithLp.toLp 2 (0, t.1), WithLp.toLp 2 (0 - t.2.2, 0 + t.2.1)) = _
      simp only [zero_sub, zero_add]
      rfl
  let f₀ := f.comp (ContinuousLinearMap.inl ℂ X Y)
  let f₁ := f.comp (ContinuousLinearMap.inr ℂ X Y)
  -- Continuity carries both separate joint graph closures into the original closed graph.
  have h₀ : J₀ ≤ (gradedTensorOperator P Q).graph.comap f₀.toLinearMap := by
    apply (TensorProduct.jointGraph P Q).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨⟨u, v⟩, rfl⟩
      change f (_, 0) ∈ (gradedTensorOperator P Q).graph
      rw [hreal.2.1]
      apply (gradedTensorGraph P Q).le_topologicalClosure
      apply Submodule.subset_span
      apply Or.inl
      refine ⟨(u, v), ?_⟩
      change _ = (WithLp.toLp 2
        ((↑((u : H₀) ⊗ₜ[ℂ] (v : K₀)) : H₀₀), 0),
        WithLp.toLp 2 ((↑(P u ⊗ₜ[ℂ] (v : K₀)) : H₁₀) - 0,
          (↑((u : H₀) ⊗ₜ[ℂ] Q v) : H₀₁) + 0))
      simp only [sub_zero, add_zero]
      rfl
    · exact hreal.2.2.1.preimage f₀.continuous
  have h₁ : J₁ ≤ (gradedTensorOperator P Q).graph.comap f₁.toLinearMap := by
    apply (TensorProduct.jointGraph P.adjoint Q.adjoint).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨⟨u, v⟩, rfl⟩
      change f (0, _) ∈ (gradedTensorOperator P Q).graph
      rw [hreal.2.1]
      apply (gradedTensorGraph P Q).le_topologicalClosure
      apply Submodule.subset_span
      apply Or.inr
      refine ⟨(u, v), ?_⟩
      change _ = (WithLp.toLp 2
        (0, (↑((u : H₁) ⊗ₜ[ℂ] (v : K₁)) : H₁₁)),
        WithLp.toLp 2 (0 - (↑((u : H₁) ⊗ₜ[ℂ] Q.adjoint v) : H₁₀),
          0 + (↑(P.adjoint u ⊗ₜ[ℂ] (v : K₁)) : H₀₁)))
      simp only [zero_sub, zero_add]
      rfl
    · exact hreal.2.2.1.preimage f₁.continuous
  have hDgraph : (gradedTensorOperator P Q).graph = F.range := by
    apply le_antisymm
    · rw [hreal.2.1]
      exact (gradedTensorGraph P Q).topologicalClosure_minimal hG hclosedRange
    · rintro z ⟨t, rfl⟩
      have hdecompose : F t = f₀ t.val.1 + f₁ t.val.2 := by
        change f (t.val.1, t.val.2) = f (t.val.1, 0) + f (0, t.val.2)
        rw [← map_add]
        simp only [Prod.mk_add_mk, add_zero, zero_add]
      change F t ∈ (gradedTensorOperator P Q).graph
      rw [hdecompose]
      exact (gradedTensorOperator P Q).graph.add_mem (h₀ t.property.1) (h₁ t.property.2)
  have hPadj := dense_adjoint_domain_of_isClosed P hPclosed
  have hQadj := dense_adjoint_domain_of_isClosed Q hQclosed
  have hPaa := dense_adjoint_domain_of_isClosed P.adjoint (P.adjoint_isClosed hPdense)
  have hQaa := dense_adjoint_domain_of_isClosed Q.adjoint (Q.adjoint_isClosed hQdense)
  -- Projection of each joint graph closure retains its two actual amplified graph coordinates.
  have hl₀ : ∀ t : X, t ∈ J₀ → (t.1, t.2.1) ∈ (hilbertTensorLeftOperator P K₀).graph := by
    let L := Submodule.span ℂ (Set.range fun z : P.domain × K₀ ↦
      ((↑((z.1 : H₀) ⊗ₜ[ℂ] z.2) : H₀₀), (↑(P z.1 ⊗ₜ[ℂ] z.2) : H₁₀)))
    have heq : (hilbertTensorLeftOperator P K₀).graph = L.topologicalClosure := by
      simpa only [hilbertTensorLeftOperator, UniformSpace.Completion.coe_toComplL] using
        P.left_tensor_closure_graph hPclosed hPdense hPadj K₀
    let π : X →L[ℂ] H₀₀ × H₁₀ :=
      (ContinuousLinearMap.fst ℂ H₀₀ (H₁₀ × H₀₁)).prod
        ((ContinuousLinearMap.fst ℂ H₁₀ H₀₁).comp
          (ContinuousLinearMap.snd ℂ H₀₀ (H₁₀ × H₀₁)))
    have h : J₀ ≤ L.topologicalClosure.comap π.toLinearMap := by
      apply (TensorProduct.jointGraph P Q).topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro t ⟨⟨u, v⟩, rfl⟩
        exact L.le_topologicalClosure (Submodule.subset_span ⟨(u, (v : K₀)), rfl⟩)
      · exact L.isClosed_topologicalClosure.preimage π.continuous
    intro t ht
    rw [heq]
    exact h ht
  have hr₀ : ∀ t : X, t ∈ J₀ → (t.1, t.2.2) ∈ (hilbertTensorRightOperator H₀ Q).graph := by
    let L := Submodule.span ℂ (Set.range fun z : H₀ × Q.domain ↦
      ((↑(z.1 ⊗ₜ[ℂ] (z.2 : K₀)) : H₀₀), (↑(z.1 ⊗ₜ[ℂ] Q z.2) : H₀₁)))
    have heq : (hilbertTensorRightOperator H₀ Q).graph = L.topologicalClosure := by
      simpa only [hilbertTensorRightOperator, UniformSpace.Completion.coe_toComplL] using
        Q.right_tensor_closure_graph hQclosed hQdense hQadj H₀
    let π : X →L[ℂ] H₀₀ × H₀₁ :=
      (ContinuousLinearMap.fst ℂ H₀₀ (H₁₀ × H₀₁)).prod
        ((ContinuousLinearMap.snd ℂ H₁₀ H₀₁).comp
          (ContinuousLinearMap.snd ℂ H₀₀ (H₁₀ × H₀₁)))
    have h : J₀ ≤ L.topologicalClosure.comap π.toLinearMap := by
      apply (TensorProduct.jointGraph P Q).topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro t ⟨⟨u, v⟩, rfl⟩
        exact L.le_topologicalClosure (Submodule.subset_span ⟨((u : H₀), v), rfl⟩)
      · exact L.isClosed_topologicalClosure.preimage π.continuous
    intro t ht
    rw [heq]
    exact h ht
  have hl₁ : ∀ t : Y, t ∈ J₁ → (t.1, t.2.1) ∈ (hilbertTensorLeftOperator P.adjoint K₁).graph := by
    let L := Submodule.span ℂ (Set.range fun z : P.adjoint.domain × K₁ ↦
      ((↑((z.1 : H₁) ⊗ₜ[ℂ] z.2) : H₁₁), (↑(P.adjoint z.1 ⊗ₜ[ℂ] z.2) : H₀₁)))
    have heq : (hilbertTensorLeftOperator P.adjoint K₁).graph = L.topologicalClosure := by
      simpa only [hilbertTensorLeftOperator, UniformSpace.Completion.coe_toComplL] using
        P.adjoint.left_tensor_closure_graph (P.adjoint_isClosed hPdense) hPadj hPaa K₁
    let π : Y →L[ℂ] H₁₁ × H₀₁ :=
      (ContinuousLinearMap.fst ℂ H₁₁ (H₀₁ × H₁₀)).prod
        ((ContinuousLinearMap.fst ℂ H₀₁ H₁₀).comp
          (ContinuousLinearMap.snd ℂ H₁₁ (H₀₁ × H₁₀)))
    have h : J₁ ≤ L.topologicalClosure.comap π.toLinearMap := by
      apply (TensorProduct.jointGraph P.adjoint Q.adjoint).topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro t ⟨⟨u, v⟩, rfl⟩
        exact L.le_topologicalClosure (Submodule.subset_span ⟨(u, (v : K₁)), rfl⟩)
      · exact L.isClosed_topologicalClosure.preimage π.continuous
    intro t ht
    rw [heq]
    exact h ht
  have hr₁ : ∀ t : Y, t ∈ J₁ → (t.1, t.2.2) ∈ (hilbertTensorRightOperator H₁ Q.adjoint).graph := by
    let L := Submodule.span ℂ (Set.range fun z : H₁ × Q.adjoint.domain ↦
      ((↑(z.1 ⊗ₜ[ℂ] (z.2 : K₁)) : H₁₁), (↑(z.1 ⊗ₜ[ℂ] Q.adjoint z.2) : H₁₀)))
    have heq : (hilbertTensorRightOperator H₁ Q.adjoint).graph = L.topologicalClosure := by
      simpa only [hilbertTensorRightOperator, UniformSpace.Completion.coe_toComplL] using
        Q.adjoint.right_tensor_closure_graph (Q.adjoint_isClosed hQdense) hQadj hQaa H₁
    let π : Y →L[ℂ] H₁₁ × H₁₀ :=
      (ContinuousLinearMap.fst ℂ H₁₁ (H₀₁ × H₁₀)).prod
        ((ContinuousLinearMap.snd ℂ H₀₁ H₁₀).comp
          (ContinuousLinearMap.snd ℂ H₁₁ (H₀₁ × H₁₀)))
    have h : J₁ ≤ L.topologicalClosure.comap π.toLinearMap := by
      apply (TensorProduct.jointGraph P.adjoint Q.adjoint).topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro t ⟨⟨u, v⟩, rfl⟩
        exact L.le_topologicalClosure (Submodule.subset_span ⟨((u : H₁), v), rfl⟩)
      · exact L.isClosed_topologicalClosure.preimage π.continuous
    intro t ht
    rw [heq]
    exact h ht
  -- The closed range gives exactly the domain and values of the specified joint matrix.
  apply LinearPMap.eq_of_eq_graph
  rw [hDgraph]
  apply le_antisymm
  · rintro z ⟨t, rfl⟩
    obtain ⟨a₀, ha₀, hA⟩ := (hilbertTensorLeftOperator P K₀).mem_graph_iff.mp (hl₀ _ t.property.1)
    obtain ⟨b₀, hb₀, hB⟩ := (hilbertTensorRightOperator H₀ Q).mem_graph_iff.mp (hr₀ _ t.property.1)
    obtain ⟨a₁, ha₁, hC⟩ :=
      (hilbertTensorLeftOperator P.adjoint K₁).mem_graph_iff.mp (hl₁ _ t.property.2)
    obtain ⟨b₁, hb₁, hD⟩ :=
      (hilbertTensorRightOperator H₁ Q.adjoint).mem_graph_iff.mp (hr₁ _ t.property.2)
    dsimp only [Prod.fst, Prod.snd] at ha₀ hb₀ ha₁ hb₁ hA hB hC hD
    let u : gradedTensorJointDomain P Q :=
      ⟨WithLp.toLp 2 (t.val.1.1, t.val.2.1),
        ⟨⟨ha₀ ▸ a₀.property, hb₀ ▸ b₀.property⟩, ⟨ha₁ ▸ a₁.property, hb₁ ▸ b₁.property⟩⟩⟩
    apply (gradedTensorJointOperator P Q).mem_graph_iff'.mpr
    refine ⟨u, ?_⟩
    apply Prod.ext
    · rfl
    · apply WithLp.ofLp_injective
      change
        (hilbertTensorLeftOperator P K₀ ⟨t.val.1.1, _⟩ -
          hilbertTensorRightOperator H₁ Q.adjoint ⟨t.val.2.1, _⟩,
         hilbertTensorRightOperator H₀ Q ⟨t.val.1.1, _⟩ +
          hilbertTensorLeftOperator P.adjoint K₁ ⟨t.val.2.1, _⟩) =
        (t.val.1.2.1 - t.val.2.2.2, t.val.1.2.2 + t.val.2.2.1)
      have hA' : (⟨t.val.1.1, u.property.1.1⟩ : (hilbertTensorLeftOperator P K₀).domain) = a₀ :=
        Subtype.ext ha₀.symm
      have hB' : (⟨t.val.1.1, u.property.1.2⟩ : (hilbertTensorRightOperator H₀ Q).domain) = b₀ :=
        Subtype.ext hb₀.symm
      have hC' : (⟨t.val.2.1, u.property.2.1⟩ :
          (hilbertTensorLeftOperator P.adjoint K₁).domain) = a₁ := Subtype.ext ha₁.symm
      have hD' : (⟨t.val.2.1, u.property.2.2⟩ :
          (hilbertTensorRightOperator H₁ Q.adjoint).domain) = b₁ := Subtype.ext hb₁.symm
      rw [hA', hB', hC', hD', hA, hB, hC, hD]
  · intro z hz
    obtain ⟨u, rfl⟩ := (gradedTensorJointOperator P Q).mem_graph_iff'.mp hz
    let x₀ : H₀₀ := (WithLp.ofLp u.val).1
    let x₁ : H₁₁ := (WithLp.ofLp u.val).2
    let a : H₁₀ := hilbertTensorLeftOperator P K₀ ⟨x₀, u.property.1.1⟩
    let b : H₀₁ := hilbertTensorRightOperator H₀ Q ⟨x₀, u.property.1.2⟩
    let c : H₀₁ := hilbertTensorLeftOperator P.adjoint K₁ ⟨x₁, u.property.2.1⟩
    let d : H₁₀ := hilbertTensorRightOperator H₁ Q.adjoint ⟨x₁, u.property.2.2⟩
    -- The four actual amplified values belong to the closures of their prescribed graphs.
    have hA := (hilbertTensorLeftOperator P K₀).mem_graph ⟨x₀, u.property.1.1⟩
    change (x₀, a) ∈ (hilbertTensorLeftOperator P K₀).graph at hA
    simp only [hilbertTensorLeftOperator, UniformSpace.Completion.coe_toComplL] at hA
    rw [P.left_tensor_closure_graph hPclosed hPdense hPadj K₀] at hA
    have hB := (hilbertTensorRightOperator H₀ Q).mem_graph ⟨x₀, u.property.1.2⟩
    change (x₀, b) ∈ (hilbertTensorRightOperator H₀ Q).graph at hB
    simp only [hilbertTensorRightOperator, UniformSpace.Completion.coe_toComplL] at hB
    rw [Q.right_tensor_closure_graph hQclosed hQdense hQadj H₀] at hB
    have hC := (hilbertTensorLeftOperator P.adjoint K₁).mem_graph ⟨x₁, u.property.2.1⟩
    change (x₁, c) ∈ (hilbertTensorLeftOperator P.adjoint K₁).graph at hC
    simp only [hilbertTensorLeftOperator, UniformSpace.Completion.coe_toComplL] at hC
    rw [P.adjoint.left_tensor_closure_graph (P.adjoint_isClosed hPdense) hPadj hPaa K₁] at hC
    have hD := (hilbertTensorRightOperator H₁ Q.adjoint).mem_graph ⟨x₁, u.property.2.2⟩
    change (x₁, d) ∈ (hilbertTensorRightOperator H₁ Q.adjoint).graph at hD
    simp only [hilbertTensorRightOperator, UniformSpace.Completion.coe_toComplL] at hD
    rw [Q.adjoint.right_tensor_closure_graph (Q.adjoint_isClosed hQdense) hQadj hQaa H₁] at hD
    -- Simultaneous approximation retains both images in each parity summand.
    have hx := TensorProduct.mem_topologicalClosure_joint_graph P Q hPclosed hQclosed
      hPdense hQdense hPadj hQadj x₀ a b hA hB
    have hy := TensorProduct.mem_topologicalClosure_joint_graph P.adjoint Q.adjoint
      (P.adjoint_isClosed hPdense) (Q.adjoint_isClosed hQdense)
      hPadj hQadj hPaa hQaa x₁ c d hC hD
    refine ⟨⟨((x₀, (a, b)), (x₁, (c, d))), ⟨hx, hy⟩⟩, ?_⟩
    apply Prod.ext
    · exact WithLp.toLp_ofLp 2 u.val
    · rfl

/-- The graded energy identity holds on every vector of the full joint domain. -/
theorem gradedTensorJointOperator_energy
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed)
    (u : gradedTensorJointDomain P Q) :
    ‖gradedTensorJointOperator P Q u‖ ^ 2 =
      ‖hilbertTensorLeftOperator P K₀
        ⟨(WithLp.ofLp u.val).1, u.property.1.1⟩‖ ^ 2 +
      ‖hilbertTensorRightOperator H₀ Q
        ⟨(WithLp.ofLp u.val).1, u.property.1.2⟩‖ ^ 2 +
      ‖hilbertTensorLeftOperator P.adjoint K₁
        ⟨(WithLp.ofLp u.val).2, u.property.2.1⟩‖ ^ 2 +
      ‖hilbertTensorRightOperator H₁ Q.adjoint
        ⟨(WithLp.ofLp u.val).2, u.property.2.2⟩‖ ^ 2 := by
  -- Both original factors and their adjoints have the dense test domains needed for graph closure.
  have hPadj := dense_adjoint_domain_of_isClosed P hPclosed
  have hQadj := dense_adjoint_domain_of_isClosed Q hQclosed
  have hPaa := dense_adjoint_domain_of_isClosed P.adjoint (P.adjoint_isClosed hPdense)
  have hQaa := dense_adjoint_domain_of_isClosed Q.adjoint (Q.adjoint_isClosed hQdense)
  let x₀ : H₀₀ := (WithLp.ofLp u.val).1
  let x₁ : H₁₁ := (WithLp.ofLp u.val).2
  let a : H₁₀ := hilbertTensorLeftOperator P K₀ ⟨x₀, u.property.1.1⟩
  let b : H₀₁ := hilbertTensorRightOperator H₀ Q ⟨x₀, u.property.1.2⟩
  let c : H₀₁ := hilbertTensorLeftOperator P.adjoint K₁ ⟨x₁, u.property.2.1⟩
  let d : H₁₀ := hilbertTensorRightOperator H₁ Q.adjoint ⟨x₁, u.property.2.2⟩
  -- The four actual amplified values belong to the closures of their prescribed graphs.
  have hA := (hilbertTensorLeftOperator P K₀).mem_graph ⟨x₀, u.property.1.1⟩
  change (x₀, a) ∈ (hilbertTensorLeftOperator P K₀).graph at hA
  simp only [hilbertTensorLeftOperator, UniformSpace.Completion.coe_toComplL] at hA
  rw [P.left_tensor_closure_graph hPclosed hPdense hPadj K₀] at hA
  have hB := (hilbertTensorRightOperator H₀ Q).mem_graph ⟨x₀, u.property.1.2⟩
  change (x₀, b) ∈ (hilbertTensorRightOperator H₀ Q).graph at hB
  simp only [hilbertTensorRightOperator, UniformSpace.Completion.coe_toComplL] at hB
  rw [Q.right_tensor_closure_graph hQclosed hQdense hQadj H₀] at hB
  have hC := (hilbertTensorLeftOperator P.adjoint K₁).mem_graph ⟨x₁, u.property.2.1⟩
  change (x₁, c) ∈ (hilbertTensorLeftOperator P.adjoint K₁).graph at hC
  simp only [hilbertTensorLeftOperator, UniformSpace.Completion.coe_toComplL] at hC
  rw [P.adjoint.left_tensor_closure_graph (P.adjoint_isClosed hPdense) hPadj hPaa K₁] at hC
  have hD := (hilbertTensorRightOperator H₁ Q.adjoint).mem_graph ⟨x₁, u.property.2.2⟩
  change (x₁, d) ∈ (hilbertTensorRightOperator H₁ Q.adjoint).graph at hD
  simp only [hilbertTensorRightOperator, UniformSpace.Completion.coe_toComplL] at hD
  rw [Q.adjoint.right_tensor_closure_graph (Q.adjoint_isClosed hQdense) hQadj hQaa H₁] at hD
  -- Simultaneous approximation retains both images in each parity summand.
  have hx := TensorProduct.mem_topologicalClosure_joint_graph P Q hPclosed hQclosed
    hPdense hQdense hPadj hQadj x₀ a b hA hB
  have hy := TensorProduct.mem_topologicalClosure_joint_graph P.adjoint Q.adjoint
    (P.adjoint_isClosed hPdense) (Q.adjoint_isClosed hQdense)
    hPadj hQadj hPaa hQaa x₁ c d hC hD
  have henergy := LinearPMap.graded_tensor_joint_energy P Q hPdense hQdense
    (x₀, (a, b)) (x₁, (c, d)) hx hy
  -- The prescribed signed matrix has exactly these two output coordinates.
  change ‖WithLp.toLp 2 (a - d, b + c)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  exact henergy

end AtiyahSinger
