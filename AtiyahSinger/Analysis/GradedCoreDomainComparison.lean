/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphCoreRealization

/-!
# The original graded graph domain from its two core estimates

Public module ID: M0695.

Keep the given complete component domains, their actual inclusions and all
four bounded block maps. The original cross pairing cancels the signed
matrix cross terms on the specified dense core. The two reverse
joint estimates therefore give a reverse estimate for this same full matrix.
The existing closed-graph completion theorem identifies the given product
domain with the actual graph of the supplied closed graded operator.

This interface is used for both the original graded operator and its signed
formal transpose. Its two geometric core estimates remain explicit inputs;
no uniform estimate for a varying elliptic regularization is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X₀ X₁ E₀ E₁ Y₀ Y₁ S₀ S₁ : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [CompleteSpace X₀]
  [NormedAddCommGroup X₁] [NormedSpace ℂ X₁] [CompleteSpace X₁]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup Y₀] [InnerProductSpace ℂ Y₀] [CompleteSpace Y₀]
  [NormedAddCommGroup Y₁] [InnerProductSpace ℂ Y₁] [CompleteSpace Y₁]
  [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]

/-- Two original joint core estimates identify the domain of the same signed graded operator. -/
theorem LinearPMap.exists_graded_graphDomainEquiv_of_joint_core_bounds
    (J₀ : X₀ →L[ℂ] E₀) (J₁ : X₁ →L[ℂ] E₁)
    (hJ₀ : Function.Injective J₀) (hJ₁ : Function.Injective J₁)
    (H₀ : X₀ →L[ℂ] Y₀) (V₀ : X₀ →L[ℂ] Y₁)
    (V₁ : X₁ →L[ℂ] Y₀) (H₁ : X₁ →L[ℂ] Y₁)
    (i₀ : S₀ →ₗ[ℂ] X₀) (i₁ : S₁ →ₗ[ℂ] X₁)
    (hi₀ : DenseRange i₀) (hi₁ : DenseRange i₁)
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbound₀ : ∀ s : S₀, ‖i₀ s‖ ≤ C₀ *
      (‖J₀ (i₀ s)‖ + ‖H₀ (i₀ s)‖ + ‖V₀ (i₀ s)‖))
    (hbound₁ : ∀ t : S₁, ‖i₁ t‖ ≤ C₁ *
      (‖J₁ (i₁ t)‖ + ‖V₁ (i₁ t)‖ + ‖H₁ (i₁ t)‖))
    (hcross : ∀ s t, inner ℂ (H₀ (i₀ s)) (V₁ (i₁ t)) =
      inner ℂ (V₀ (i₀ s)) (H₁ (i₁ t))) :
    let X := WithLp 2 (X₀ × X₁)
    let Even := WithLp 2 (E₀ × E₁)
    let Odd := WithLp 2 (Y₀ × Y₁)
    let cX := WithLp.prodContinuousLinearEquiv 2 ℂ X₀ X₁
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ E₀ E₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ Y₀ Y₁
    let i := cX.symm.toLinearMap.comp (i₀.prodMap i₁)
    let J := cEven.symm.toContinuousLinearMap.comp
      ((J₀.prodMap J₁).comp cX.toContinuousLinearMap)
    let T := cOdd.symm.toContinuousLinearMap.comp
      (((H₀.coprod (-V₁)).prod (V₀.coprod H₁)).comp cX.toContinuousLinearMap)
    ∀ (D : Even →ₗ.[ℂ] Odd), D.IsClosed →
      D.graph = ((J.prod T).toLinearMap.comp i).range.topologicalClosure →
      let Γ := D.graph.comap (WithLp.linearEquiv 2 ℂ (Even × Odd)).toLinearMap
      ∃ Φ : X ≃L[ℂ] Γ, ∀ x, (Φ x).val = WithLp.toLp 2 (J x, T x) := by
  intro X Even Odd cX cEven cOdd i J T D hD hgraph
  -- The specified product core is dense in the same complete product domain.
  have hi : DenseRange i :=
    cX.symm.surjective.denseRange.comp (hi₀.prodMap hi₁) cX.symm.continuous
  have hJ : Function.Injective J := by
    intro x y hxy
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply hJ₀
      exact congrArg (fun z : Even ↦ z.ofLp.1) hxy
    · apply hJ₁
      exact congrArg (fun z : Even ↦ z.ofLp.2) hxy
  -- On each core pair, cancellation bounds all four blocks by the signed output.
  have hbound (z : S₀ × S₁) :
      ‖i z‖ ≤ (2 * (C₀ + C₁)) * (‖J (i z)‖ + ‖T (i z)‖) := by
    rcases z with ⟨s, t⟩
    let x := i (s, t)
    have henergy : ‖T x‖ ^ 2 =
        ‖H₀ (i₀ s)‖ ^ 2 + ‖V₀ (i₀ s)‖ ^ 2 +
          ‖V₁ (i₁ t)‖ ^ 2 + ‖H₁ (i₁ t)‖ ^ 2 := by
      have hTx : T x = WithLp.toLp 2
          (H₀ (i₀ s) - V₁ (i₁ t), V₀ (i₀ s) + H₁ (i₁ t)) := by
        apply WithLp.ofLp_injective
        change (H₀ (i₀ s) + -(V₁ (i₁ t)), V₀ (i₀ s) + H₁ (i₁ t)) = _
        rw [sub_eq_add_neg]
      rw [hTx, WithLp.prod_norm_sq_eq_of_L2]
      change ‖H₀ (i₀ s) - V₁ (i₁ t)‖ ^ 2 +
        ‖V₀ (i₀ s) + H₁ (i₁ t)‖ ^ 2 = _
      rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hcross s t]
      ring
    have hh₀ : ‖H₀ (i₀ s)‖ ≤ ‖T x‖ := by
      nlinarith [sq_nonneg ‖V₀ (i₀ s)‖, sq_nonneg ‖V₁ (i₁ t)‖,
        sq_nonneg ‖H₁ (i₁ t)‖, norm_nonneg (T x)]
    have hv₀ : ‖V₀ (i₀ s)‖ ≤ ‖T x‖ := by
      nlinarith [sq_nonneg ‖H₀ (i₀ s)‖, sq_nonneg ‖V₁ (i₁ t)‖,
        sq_nonneg ‖H₁ (i₁ t)‖, norm_nonneg (T x)]
    have hv₁ : ‖V₁ (i₁ t)‖ ≤ ‖T x‖ := by
      nlinarith [sq_nonneg ‖H₀ (i₀ s)‖, sq_nonneg ‖V₀ (i₀ s)‖,
        sq_nonneg ‖H₁ (i₁ t)‖, norm_nonneg (T x)]
    have hh₁ : ‖H₁ (i₁ t)‖ ≤ ‖T x‖ := by
      nlinarith [sq_nonneg ‖H₀ (i₀ s)‖, sq_nonneg ‖V₀ (i₀ s)‖,
        sq_nonneg ‖V₁ (i₁ t)‖, norm_nonneg (T x)]
    have hj₀ : ‖J₀ (i₀ s)‖ ≤ ‖J x‖ := WithLp.norm_fst_le E₀ (J x)
    have hj₁ : ‖J₁ (i₁ t)‖ ≤ ‖J x‖ := WithLp.norm_snd_le E₀ (J x)
    have hx : ‖x‖ ≤ ‖i₀ s‖ + ‖i₁ t‖ := by
      have hx₂ : ‖x‖ ^ 2 = ‖i₀ s‖ ^ 2 + ‖i₁ t‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 x
      nlinarith [norm_nonneg x, norm_nonneg (i₀ s), norm_nonneg (i₁ t)]
    have h₀ := (hbound₀ s).trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hj₀ hh₀) hv₀) hC₀)
    have h₁ := (hbound₁ t).trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hj₁ hv₁) hh₁) hC₁)
    have hsum := hx.trans (add_le_add h₀ h₁)
    have hJnorm : 0 ≤ ‖J x‖ := norm_nonneg _
    change ‖x‖ ≤ (2 * (C₀ + C₁)) * (‖J x‖ + ‖T x‖)
    nlinarith [mul_nonneg (add_nonneg hC₀ hC₁) hJnorm]
  -- The existing completion theorem retains the original D, inclusion and matrix action.
  exact LinearPMap.exists_graphDomainEquiv_of_core_bound D hD J T hJ i hi hgraph
    (2 * (C₀ + C₁)) (mul_nonneg (by norm_num) (add_nonneg hC₀ hC₁)) hbound

end AtiyahSinger
