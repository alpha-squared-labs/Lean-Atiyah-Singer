/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedJointRealization

/-!
# The kernel on the exact simultaneous graded domain

Public module ID: M0703.

For the specified partial graded operator, energy identifies its kernel with
the product of the two original joint kernels. Bounded coordinate projections
on the actual graph spaces let the existing graded-block kernel theorem apply
without assuming that an unbounded operator is continuous in its ambient norm.
The exact domain equality is essential in the forward direction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁]

/-- The original graded operator kernel is the product of its two simultaneous kernels. -/
theorem ker_eq_prod_of_gradedJointOperator
    (P : E₀ →ₗ.[ℂ] (F₀ × F₁)) (Q : E₁ →ₗ.[ℂ] (F₀ × F₁))
    (hcross : ∀ (u : P.domain) (v : Q.domain),
      inner ℂ (P u).1 (Q v).1 = inner ℂ (P u).2 (Q v).2)
    (D : WithLp 2 (E₀ × E₁) →ₗ.[ℂ] WithLp 2 (F₀ × F₁))
    (hdom : D.domain = (P.domain.prod Q.domain).comap
      (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toLinearMap)
    (hD : ∀ (u : P.domain) (v : Q.domain),
      (WithLp.toLp 2 (u.val, v.val),
        WithLp.toLp 2 ((P u).1 - (Q v).1, (P u).2 + (Q v).2)) ∈ D.graph) :
    D.ker = (P.ker.prod Q.ker).comap
      (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toLinearMap := by
  -- The four maps are bounded projections of the full graph coordinates.
  let U := (ContinuousLinearMap.fst ℂ F₀ F₁).comp
    ((ContinuousLinearMap.snd ℂ E₀ (F₀ × F₁)).comp P.graph.subtypeL)
  let V := (ContinuousLinearMap.snd ℂ F₀ F₁).comp
    ((ContinuousLinearMap.snd ℂ E₀ (F₀ × F₁)).comp P.graph.subtypeL)
  let W := (ContinuousLinearMap.fst ℂ F₀ F₁).comp
    ((ContinuousLinearMap.snd ℂ E₁ (F₀ × F₁)).comp Q.graph.subtypeL)
  let Z := (ContinuousLinearMap.snd ℂ F₀ F₁).comp
    ((ContinuousLinearMap.snd ℂ E₁ (F₀ × F₁)).comp Q.graph.subtypeL)
  have hc (x : P.graph) (y : Q.graph) :
      inner ℂ (U x) (W y) = inner ℂ (V x) (Z y) := by
    obtain ⟨u, hu⟩ := P.mem_graph_iff'.mp x.property
    obtain ⟨v, hv⟩ := Q.mem_graph_iff'.mp y.property
    change inner ℂ x.val.2.1 y.val.2.1 = inner ℂ x.val.2.2 y.val.2.2
    rw [← hu, ← hv]
    exact hcross u v
  have hblock := ker_gradedBlockOperator_of_inner_eq U V W Z hc
  have hzero (u : P.domain) (v : Q.domain)
      (h : WithLp.toLp 2 ((P u).1 - (Q v).1, (P u).2 + (Q v).2) = 0) :
      P u = 0 ∧ Q v = 0 := by
    let x : P.graph := ⟨(u.val, P u), P.mem_graph u⟩
    let y : Q.graph := ⟨(v.val, Q v), Q.mem_graph v⟩
    have hx : WithLp.toLp 2 (x, y) ∈ (gradedBlockOperator U V W Z).ker := by
      change gradedBlockOperator U V W Z (WithLp.toLp 2 (x, y)) = 0
      apply WithLp.ofLp_injective
      have h' := congrArg WithLp.ofLp h
      change ((P u).1 - (Q v).1, (P u).2 + (Q v).2) = (0, 0) at h'
      change ((P u).1 + -((Q v).1), (P u).2 + (Q v).2) = (0, 0)
      simpa only [sub_eq_add_neg] using h'
    rw [hblock] at hx
    change ((P u).1 = 0 ∧ (P u).2 = 0) ∧ (Q v).1 = 0 ∧ (Q v).2 = 0 at hx
    exact ⟨Prod.ext hx.1.1 hx.1.2, Prod.ext hx.2.1 hx.2.2⟩
  have hker (z : WithLp 2 (E₀ × E₁)) : z ∈ D.ker ↔ (z, 0) ∈ D.graph := by
    constructor
    · intro hz
      obtain ⟨u, rfl, hu⟩ := D.mem_ker_iff.mp hz
      exact hu ▸ D.mem_graph u
    · intro hz
      obtain ⟨u, hu, hDu⟩ := D.mem_graph_iff.mp hz
      exact D.mem_ker_iff.mpr ⟨u, hu.symm, hDu⟩
  -- The original domain certificate supplies both joint inputs for every graded kernel vector.
  ext z
  change z ∈ D.ker ↔ z.ofLp.1 ∈ P.ker ∧ z.ofLp.2 ∈ Q.ker
  rw [hker]
  constructor
  · intro hz
    have hzdom := LinearPMap.mem_domain_of_mem_graph hz
    rw [hdom] at hzdom
    let u : P.domain := ⟨z.ofLp.1, hzdom.1⟩
    let v : Q.domain := ⟨z.ofLp.2, hzdom.2⟩
    have hzout := D.mem_graph_snd_inj (hD u v) hz (WithLp.toLp_ofLp 2 z)
    obtain ⟨hu, hv⟩ := hzero u v hzout
    exact ⟨P.mem_ker_iff.mpr ⟨u, rfl, hu⟩, Q.mem_ker_iff.mpr ⟨v, rfl, hv⟩⟩
  · rintro ⟨hz₀, hz₁⟩
    obtain ⟨u, hu, hPu⟩ := P.mem_ker_iff.mp hz₀
    obtain ⟨v, hv, hQv⟩ := Q.mem_ker_iff.mp hz₁
    have h := hD u v
    have hin : WithLp.toLp 2 (u.val, v.val) = z := by
      rw [← hu, ← hv]
    simp only [hin, hPu, hQv, Prod.fst_zero, Prod.snd_zero, sub_self, add_zero] at h
    change (z, WithLp.toLp 2 (0 : F₀ × F₁)) ∈ D.graph at h
    simpa only [WithLp.toLp_zero] using h

end AtiyahSinger
