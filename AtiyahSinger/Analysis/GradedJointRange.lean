/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedJointKernel

/-!
# Closed range of the original graded joint operator

Public module ID: M0704.

The signed output map is bounded below on the product of the two original
joint ranges: their cross pairings cancel in the squared Hilbert norm.
Consequently, closed joint ranges give a closed graded range. The exact
domain and graph certificates identify this image with the specified operator,
without replacing its simultaneous domains by separate closures.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]

/-- Closed simultaneous ranges and the original energy identity give closed graded range. -/
theorem isClosed_range_gradedJointOperator
    (P : E₀ →ₗ.[ℂ] (F₀ × F₁)) (Q : E₁ →ₗ.[ℂ] (F₀ × F₁))
    (hP : IsClosed (P.toFun.range : Set (F₀ × F₁)))
    (hQ : IsClosed (Q.toFun.range : Set (F₀ × F₁)))
    (hcross : ∀ (u : P.domain) (v : Q.domain),
      inner ℂ (P u).1 (Q v).1 = inner ℂ (P u).2 (Q v).2)
    (D : WithLp 2 (E₀ × E₁) →ₗ.[ℂ] WithLp 2 (F₀ × F₁))
    (hdom : D.domain = (P.domain.prod Q.domain).comap
      (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁).toLinearMap)
    (hD : ∀ (u : P.domain) (v : Q.domain),
      (WithLp.toLp 2 (u.val, v.val),
        WithLp.toLp 2 ((P u).1 - (Q v).1, (P u).2 + (Q v).2)) ∈ D.graph) :
    IsClosed (D.toFun.range : Set (WithLp 2 (F₀ × F₁))) := by
  let C := P.toFun.range.prod Q.toFun.range
  have hC : IsClosed (C : Set ((F₀ × F₁) × (F₀ × F₁))) := hP.prod hQ
  let : CompleteSpace C := hC.completeSpace_coe
  let f : ((F₀ × F₁) × (F₀ × F₁)) →L[ℂ] WithLp 2 (F₀ × F₁) := {
    toFun z := WithLp.toLp 2 (z.1.1 - z.2.1, z.1.2 + z.2.2)
    map_add' z w := by
      apply WithLp.ofLp_injective
      change ((z.1.1 + w.1.1) - (z.2.1 + w.2.1),
        (z.1.2 + w.1.2) + (z.2.2 + w.2.2)) =
        ((z.1.1 - z.2.1) + (w.1.1 - w.2.1),
          (z.1.2 + z.2.2) + (w.1.2 + w.2.2))
      congr 1 <;> abel
    map_smul' a z := by
      apply WithLp.ofLp_injective
      change (a • z.1.1 - a • z.2.1, a • z.1.2 + a • z.2.2) =
        (a • (z.1.1 - z.2.1), a • (z.1.2 + z.2.2))
      rw [smul_sub, smul_add]
    cont := by fun_prop }
  let F := f.comp C.subtypeL
  -- Cancellation controls all four output coordinates by the same graded image.
  have hbound (z : C) : ‖z‖ ≤ ‖F z‖ := by
    obtain ⟨u, hu⟩ := z.property.1
    obtain ⟨v, hv⟩ := z.property.2
    have hpair : inner ℂ z.val.1.1 z.val.2.1 = inner ℂ z.val.1.2 z.val.2.2 := by
      rw [← hu, ← hv]
      exact hcross u v
    have henergy : ‖F z‖ ^ 2 =
        ‖z.val.1.1‖ ^ 2 + ‖z.val.1.2‖ ^ 2 +
          ‖z.val.2.1‖ ^ 2 + ‖z.val.2.2‖ ^ 2 := by
      change ‖WithLp.toLp 2 (z.val.1.1 - z.val.2.1, z.val.1.2 + z.val.2.2)‖ ^ 2 = _
      rw [WithLp.prod_norm_sq_eq_of_L2]
      change ‖z.val.1.1 - z.val.2.1‖ ^ 2 + ‖z.val.1.2 + z.val.2.2‖ ^ 2 = _
      rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hpair]
      ring
    have ha : ‖z.val.1.1‖ ≤ ‖F z‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2‖, sq_nonneg ‖z.val.2.1‖,
        sq_nonneg ‖z.val.2.2‖, norm_nonneg (F z)]
    have hb : ‖z.val.1.2‖ ≤ ‖F z‖ := by
      nlinarith [sq_nonneg ‖z.val.1.1‖, sq_nonneg ‖z.val.2.1‖,
        sq_nonneg ‖z.val.2.2‖, norm_nonneg (F z)]
    have hc : ‖z.val.2.1‖ ≤ ‖F z‖ := by
      nlinarith [sq_nonneg ‖z.val.1.1‖, sq_nonneg ‖z.val.1.2‖,
        sq_nonneg ‖z.val.2.2‖, norm_nonneg (F z)]
    have hd : ‖z.val.2.2‖ ≤ ‖F z‖ := by
      nlinarith [sq_nonneg ‖z.val.1.1‖, sq_nonneg ‖z.val.1.2‖,
        sq_nonneg ‖z.val.2.1‖, norm_nonneg (F z)]
    change max (max ‖z.val.1.1‖ ‖z.val.1.2‖) (max ‖z.val.2.1‖ ‖z.val.2.2‖) ≤ ‖F z‖
    exact max_le (max_le ha hb) (max_le hc hd)
  have hclosed : IsClosed (F.range : Set (WithLp 2 (F₀ × F₁))) := by
    have hanti : AntilipschitzWith 1 F := F.antilipschitz_of_bound (fun z ↦ by
      simpa only [NNReal.coe_one, one_mul] using hbound z)
    exact hanti.isClosed_range F.uniformContinuous
  -- The specified product domain supplies both joint inputs for every graded output.
  have hrange : F.range = D.toFun.range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨u, hu⟩ := z.property.1
      obtain ⟨v, hv⟩ := z.property.2
      apply LinearPMap.mem_range_iff.mpr
      refine ⟨WithLp.toLp 2 (u.val, v.val), ?_⟩
      have hout : F z = WithLp.toLp 2 ((P u).1 - (Q v).1, (P u).2 + (Q v).2) := by
        change f z.val = _
        simp only [f, ← hu, ← hv, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
        rfl
      change (WithLp.toLp 2 (u.val, v.val), F z) ∈ D.graph
      rw [hout]
      exact hD u v
    · intro hy
      obtain ⟨x, hxy⟩ := LinearPMap.mem_range_iff.mp hy
      have hx := LinearPMap.mem_domain_of_mem_graph hxy
      rw [hdom] at hx
      let u : P.domain := ⟨x.ofLp.1, hx.1⟩
      let v : Q.domain := ⟨x.ofLp.2, hx.2⟩
      have hout := D.mem_graph_snd_inj (hD u v) hxy (WithLp.toLp_ofLp 2 x)
      exact ⟨⟨(P u, Q v), ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩⟩, hout⟩
  exact hrange ▸ hclosed

end AtiyahSinger
