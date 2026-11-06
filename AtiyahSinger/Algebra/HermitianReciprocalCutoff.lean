/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianCoreTensorSymbol
public import AtiyahSinger.Topology.TrivialSupportProduct

/-!
# The direct Hermitian-to-reciprocal cutoff homotopy

Public module ID: M0033.

The affine path retains the actual forward cutoffs and their original reciprocal
maps. Saturation of one invertible factor makes every matrix on this path
invertible. The reverse composite is a sum of nonnegative Hermitian squares
and a positive scalar at positive time.
This algebraic homotopy is used to compare the analytic graded
boundary with the supported external-product boundary.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct unitInterval

section InnerProduct

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]

set_option maxHeartbeats 1600000 in
-- The two factors may have different ranks inside their original controls.
private theorem affine_reciprocal_bijective
    (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀) (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hd : d'.comp d = (r : ℂ) • LinearMap.id)
    (hd' : d.comp d' = (r : ℂ) • LinearMap.id)
    (he : e'.comp e = (s : ℂ) • LinearMap.id)
    (he' : e.comp e' = (s : ℂ) • LinearMap.id)
    (h : (r = 1 ∧ Function.Bijective d) ∨ (s = 1 ∧ Function.Bijective e)) (t : I) :
    Function.Bijective ((1 - (t : ℂ)) • reciprocalTensorSymbol d d.adjoint e e.adjoint +
      (t : ℂ) • reciprocalTensorSymbol ((r : ℂ) • d) d' ((s : ℂ) • e) e') := by
  -- Time zero is the original Hermitian matrix, including unequal ranks in the other factor.
  by_cases ht : (t : ℝ) = 0
  · simpa [ht, weightedGradedTensorSymbol] using
      weightedGradedTensorSymbol_bijective d e 1 1
        (h.elim (fun h ↦ Or.inl ⟨one_ne_zero, h.2⟩)
          (fun h ↦ Or.inr ⟨one_ne_zero, h.2⟩))
  let α : ℝ := (1 - (t : ℝ)) + (t : ℝ) * r
  let β : ℝ := (1 - (t : ℝ)) + (t : ℝ) * s
  let c : ℝ := (1 - (t : ℝ)) * α
  let c' : ℝ := (1 - (t : ℝ)) * β
  let w : ℝ := (t : ℝ) * (α * r + β * s)
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have hα : 0 ≤ α := add_nonneg hnonneg (mul_nonneg t.property.1 hr)
  have hβ : 0 ≤ β := add_nonneg hnonneg (mul_nonneg t.property.1 hs)
  have hc : 0 ≤ c := mul_nonneg hnonneg hα
  have hc' : 0 ≤ c' := mul_nonneg hnonneg hβ
  have hpositive : 0 < w := by
    apply mul_pos htpos
    rcases h with ⟨h, _⟩ | ⟨h, _⟩
    · have hαone : α = 1 := by simp [α, h]
      rw [h, hαone, mul_one]
      exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hβ hs)
    · have hβone : β = 1 := by simp [β, h]
      rw [h, hβone, mul_one]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hα hr) zero_lt_one
  let D₀ := TensorProduct.map d (LinearMap.id : F₀ →ₗ[ℂ] F₀)
  let D₁ := TensorProduct.map d.adjoint (LinearMap.id : F₁ →ₗ[ℂ] F₁)
  let e₀ := TensorProduct.map (LinearMap.id : E₀ →ₗ[ℂ] E₀) e
  let e₁ := TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) e.adjoint
  let T := reciprocalTensorSymbol ((α : ℂ) • d)
    (((1 - (t : ℝ) : ℝ) : ℂ) • d.adjoint + (t : ℂ) • d') ((β : ℂ) • e)
    (((1 - (t : ℝ) : ℝ) : ℂ) • e.adjoint + (t : ℂ) • e')
  let S := reciprocalTensorSymbolReverse ((α : ℂ) • d)
    (((1 - (t : ℝ) : ℝ) : ℂ) • d.adjoint + (t : ℂ) • d') ((β : ℂ) • e)
    (((1 - (t : ℝ) : ℝ) : ℂ) • e.adjoint + (t : ℂ) • e')
  have hdx (x : E₀) : d' (d x) = (r : ℂ) • x := LinearMap.congr_fun hd x
  have hdx' (x : E₁) : d (d' x) = (r : ℂ) • x := LinearMap.congr_fun hd' x
  have hex (x : F₀) : e' (e x) = (s : ℂ) • x := LinearMap.congr_fun he x
  have hex' (x : F₁) : e (e' x) = (s : ℂ) • x := LinearMap.congr_fun he' x
  -- The mixed terms cancel; each diagonal is a nonnegative square plus a positive scalar.
  have hcomp : S.comp T =
      (((c : ℂ) • (D₀.adjoint.comp D₀) + (c' : ℂ) • (e₀.adjoint.comp e₀) +
          (w : ℂ) • LinearMap.id).comp (LinearMap.fst ℂ _ _)).prod
        (((c : ℂ) • (D₁.adjoint.comp D₁) + (c' : ℂ) • (e₁.adjoint.comp e₁) +
          (w : ℂ) • LinearMap.id).comp (LinearMap.snd ℂ _ _)) := by
    dsimp only [S, T, D₀, D₁, e₀, e₁, c, c', w]
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_id, LinearMap.adjoint_adjoint]
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro x y <;> apply Prod.ext
    all_goals
      simp [reciprocalTensorSymbol, reciprocalTensorSymbolReverse, hdx, hdx', hex, hex']
    all_goals
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', RCLike.real_smul_eq_coe_smul (K := ℂ)]
      module
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      change T z = 0 at hz
      have hcomposite : (S.comp T) z = 0 := by simp only [LinearMap.comp_apply, hz, map_zero]
      rw [hcomp] at hcomposite
      have hc₀ := congrArg Prod.fst hcomposite
      have hc₁ := congrArg Prod.snd hcomposite
      change (c : ℂ) • D₀.adjoint (D₀ z.1) + (c' : ℂ) • e₀.adjoint (e₀ z.1) +
        (w : ℂ) • z.1 = 0 at hc₀
      change (c : ℂ) • D₁.adjoint (D₁ z.2) + (c' : ℂ) • e₁.adjoint (e₁ z.2) +
        (w : ℂ) • z.2 = 0 at hc₁
      have hi₀ := congrArg (fun y ↦ (inner ℂ z.1 y).re) hc₀
      have hi₁ := congrArg (fun y ↦ (inner ℂ z.2 y).re) hc₁
      simp only [inner_add_right, inner_smul_right, LinearMap.adjoint_inner_right,
        inner_zero_right, Complex.zero_re,
        Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at hi₀ hi₁
      rw [show (inner ℂ (D₀ z.1) (D₀ z.1)).re = ‖D₀ z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (D₀ z.1),
        show (inner ℂ (e₀ z.1) (e₀ z.1)).re = ‖e₀ z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (e₀ z.1),
        show (inner ℂ z.1 z.1).re = ‖z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) z.1] at hi₀
      rw [show (inner ℂ (D₁ z.2) (D₁ z.2)).re = ‖D₁ z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (D₁ z.2),
        show (inner ℂ (e₁ z.2) (e₁ z.2)).re = ‖e₁ z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (e₁ z.2),
        show (inner ℂ z.2 z.2).re = ‖z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) z.2] at hi₁
      have hz₀ : z.1 = 0 := by
        apply norm_eq_zero.mp
        have hA := add_nonneg (mul_nonneg hc (sq_nonneg ‖D₀ z.1‖))
          (mul_nonneg hc' (sq_nonneg ‖e₀ z.1‖))
        have hle : w * ‖z.1‖ ^ 2 ≤ 0 := by linarith only [hi₀, hA]
        have hsq : ‖z.1‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle hpositive
        nlinarith only [hsq, norm_nonneg z.1]
      have hz₁ : z.2 = 0 := by
        apply norm_eq_zero.mp
        have hA := add_nonneg (mul_nonneg hc (sq_nonneg ‖D₁ z.2‖))
          (mul_nonneg hc' (sq_nonneg ‖e₁ z.2‖))
        have hle : w * ‖z.2‖ ^ 2 ≤ 0 := by linarith only [hi₁, hA]
        have hsq : ‖z.2‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle hpositive
        nlinarith only [hsq, norm_nonneg z.2]
      exact Prod.ext hz₀ hz₁
    · exact bot_le
  -- Either original invertible factor gives the equality of total parity dimensions.
  have hdim : Module.finrank ℂ ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) =
      Module.finrank ℂ ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) := by
    simp only [Module.finrank_prod, Module.finrank_tensorProduct]
    rcases h with ⟨_, hd⟩ | ⟨_, he⟩
    · rw [(LinearEquiv.ofBijective d hd).finrank_eq]
    · rw [(LinearEquiv.ofBijective e he).finrank_eq]
      omega
  have hT : Function.Bijective T :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  have hmatrix :
      (1 - (t : ℂ)) • reciprocalTensorSymbol d d.adjoint e e.adjoint +
        (t : ℂ) • reciprocalTensorSymbol ((r : ℂ) • d) d' ((s : ℂ) • e) e' = T := by
    apply LinearMap.ext
    intro z
    let u₀ := TensorProduct.map d (LinearMap.id : F₀ →ₗ[ℂ] F₀) z.1
    let u₁ := TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) e.adjoint z.2
    let ui := TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) e' z.2
    let v₀ := TensorProduct.map (LinearMap.id : E₀ →ₗ[ℂ] E₀) e z.1
    let v₁ := TensorProduct.map d.adjoint (LinearMap.id : F₁ →ₗ[ℂ] F₁) z.2
    let vi := TensorProduct.map d' (LinearMap.id : F₁ →ₗ[ℂ] F₁) z.2
    change (1 - (t : ℂ)) • reciprocalTensorSymbol d d.adjoint e e.adjoint z +
      (t : ℂ) • reciprocalTensorSymbol ((r : ℂ) • d) d' ((s : ℂ) • e) e' z = T z
    simp only [T, reciprocalTensorSymbol, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right, TensorProduct.map_add_left, TensorProduct.map_add_right]
    change (1 - (t : ℂ)) • (u₀ + -u₁, v₀ + v₁) +
      (t : ℂ) • ((r : ℂ) • u₀ + -ui, (s : ℂ) • v₀ + vi) =
        ((α : ℂ) • u₀ + -(((1 - (t : ℝ) : ℝ) : ℂ) • u₁ + (t : ℂ) • ui),
          (β : ℂ) • v₀ + (((1 - (t : ℝ) : ℝ) : ℂ) • v₁ + (t : ℂ) • vi))
    apply Prod.ext
    · change (1 - (t : ℂ)) • (u₀ + -u₁) +
        (t : ℂ) • ((r : ℂ) • u₀ + -ui) =
          (α : ℂ) • u₀ + -(((1 - (t : ℝ) : ℝ) : ℂ) • u₁ + (t : ℂ) • ui)
      simp only [α, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_one]
      module
    · change (1 - (t : ℂ)) • (v₀ + v₁) +
        (t : ℂ) • ((s : ℂ) • v₀ + vi) =
          (β : ℂ) • v₀ + (((1 - (t : ℝ) : ℝ) : ℂ) • v₁ + (t : ℂ) • vi)
      simp only [β, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_one]
      module
  rw [hmatrix]
  exact hT

end InnerProduct

variable {E₀ E₁ F₀ F₁ : Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [FiniteDimensional ℂ E₀]
  [AddCommGroup E₁] [Module ℂ E₁] [FiniteDimensional ℂ E₁]
  [AddCommGroup F₀] [Module ℂ F₀] [FiniteDimensional ℂ F₀]
  [AddCommGroup F₁] [Module ℂ F₁] [FiniteDimensional ℂ F₁]

/-- The actual reciprocal-cutoff boundary is joined to its prescribed Hermitian boundary
through invertible affine matrices whenever one invertible factor retains cutoff one. -/
theorem reciprocalTensorSymbol_hermitian_cutoff_affine_bijective
    (h₀ : InnerProductSpace.Core ℂ E₀) (h₁ : InnerProductSpace.Core ℂ E₁)
    (k₀ : InnerProductSpace.Core ℂ F₀) (k₁ : InnerProductSpace.Core ℂ F₁)
    (p : E₀ →ₗ[ℂ] E₁) (pi : E₁ →ₗ[ℂ] E₀)
    (q : F₀ →ₗ[ℂ] F₁) (qi : F₁ →ₗ[ℂ] F₀)
    (hp : ∀ u v, h₁.inner (p u) v = h₀.inner u (pi v))
    (hq : ∀ u v, k₁.inner (q u) v = k₀.inner u (qi v))
    (j : E₁ →ₗ[ℂ] E₀) (k : F₁ →ₗ[ℂ] F₀) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hj : j.comp p = (r : ℂ) • LinearMap.id)
    (hj' : p.comp j = (r : ℂ) • LinearMap.id)
    (hk : k.comp q = (s : ℂ) • LinearMap.id)
    (hk' : q.comp k = (s : ℂ) • LinearMap.id)
    (h : (r = 1 ∧ Function.Bijective p) ∨ (s = 1 ∧ Function.Bijective q)) (t : I) :
    Function.Bijective ((1 - (t : ℂ)) • reciprocalTensorSymbol p pi q qi +
      (t : ℂ) • reciprocalTensorSymbol ((r : ℂ) • p) j ((s : ℂ) • q) k) := by
  -- Realize the supplied pairings only for this algebraic argument.
  let := h₀
  let := h₁
  let := k₀
  let := k₁
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := E₀)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := E₁)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := F₀)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := F₁)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ E₀)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ E₁)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ F₀)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ F₁)
  have hpi : pi = p.adjoint := by
    have heq : p = pi.adjoint := (LinearMap.eq_adjoint_iff p pi).mpr hp
    rw [heq, LinearMap.adjoint_adjoint]
  have hqi : qi = q.adjoint := by
    have heq : q = qi.adjoint := (LinearMap.eq_adjoint_iff q qi).mpr hq
    rw [heq, LinearMap.adjoint_adjoint]
  rw [hpi, hqi]
  exact affine_reciprocal_bijective p j q k r s hr hs hj hj' hk hk' h t

end AtiyahSinger
