/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleExternalProduct

/-!
# Normalize reciprocal cutoffs of actual skew symbols

Public module ID: M2190.

A skew symbol and its actual negative-square reverse deform the original
reciprocal cutoff pair to the uncut pair consisting of the forward map
and the negative of its skew reverse. The scalar square is nonnegative
and positive outside the supplied enlarged set.
This gives the normalization needed before comparing the supported product
with a doubled Clifford symbol. The cutoff inverse is retained at the first
endpoint; it is not identified with the uncut reverse map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

attribute [local instance] isFiniteRank_pullback

private def linearCombinationHom {X : Type*} [TopologicalSpace X]
    {E F : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (a b : Hom E F) (r s : C(X, ℂ)) : Hom E F where
  linearMap x := r x • a.linearMap x + s x • b.linearMap x
  continuous_total := by
    let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
    let c : ∀ z : TotalSpace Unit E, (p *ᵖ F) z := fun z ↦ a.linearMap z.proj z.snd
    let d : ∀ z : TotalSpace Unit E, (p *ᵖ F) z := fun z ↦ b.linearMap z.proj z.snd
    have hc : Continuous (fun z ↦ (⟨z, c z⟩ : TotalSpace Unit (p *ᵖ F))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact continuous_id.prodMk a.continuous_total
    have hd : Continuous (fun z ↦ (⟨z, d z⟩ : TotalSpace Unit (p *ᵖ F))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact continuous_id.prodMk b.continuous_total
    have hr := continuous_smul_section (p *ᵖ F) (r.comp p) c hc
    have hs := continuous_smul_section (p *ᵖ F) (s.comp p) d hd
    exact (Pullback.continuous_lift Unit F p).comp
      (continuous_add_section (p *ᵖ F) _ _ hr hs)

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option maxHeartbeats 1000000 in
-- All four cross terms use the actual boundary and its inverse on the same original fiber.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The reciprocal cutoff pair deforms to the specified skew pair with one positive square. -/
theorem CompactSupportTriple.exists_skew_cutoff_homotopy
    (a : CompactSupportTriple E F) (c : Hom E F) (c' : Hom F E) (r : X → ℝ)
    (hc : ∀ (x : (a.controlᶜ : Set X)), (a.boundary.linearEquiv x).toLinearMap = c.linearMap x.val)
    (hsq : ∀ x, (c'.linearMap x).comp (c.linearMap x) = -(r x : ℂ) • LinearMap.id ∧
      (c.linearMap x).comp (c'.linearMap x) = -(r x : ℂ) • LinearMap.id)
    (hr : ∀ x, 0 ≤ r x) (hrpos : ∀ x ∉ a.control, 0 < r x)
    (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (haU : a.control ⊆ U)
    (hzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hUL : U ⊆ L)
    (hone : ∀ x ∉ L, ρ x = 1) :
    let p : C(I × X, X) := ContinuousMap.snd
    let q (z : I × X) : ℝ :=
      (1 - (z.1 : ℝ)) ^ 2 * (ρ z.2 : ℝ) ^ 2 +
        (z.1 : ℝ) * (1 - (z.1 : ℝ)) * (ρ z.2 : ℝ) * (1 + r z.2) +
        (z.1 : ℝ) ^ 2 * r z.2
    ∃ d : Hom (p *ᵖ E) (p *ᵖ F), ∃ d' : Hom (p *ᵖ F) (p *ᵖ E),
      (∀ z, d.linearMap z = ((1 - (z.1 : ℝ) : ℝ) : ℂ) • a.cutoffLinearMap ρ z.2 +
        ((z.1 : ℝ) : ℂ) • c.linearMap z.2) ∧
      (∀ z, d'.linearMap z = ((1 - (z.1 : ℝ) : ℝ) : ℂ) • a.inverse.cutoffLinearMap ρ z.2 -
        ((z.1 : ℝ) : ℂ) • c'.linearMap z.2) ∧
      (∀ z, (d'.linearMap z).comp (d.linearMap z) =
          (q z : ℂ) • (LinearMap.id : E z.2 →ₗ[ℂ] E z.2) ∧
        (d.linearMap z).comp (d'.linearMap z) =
          (q z : ℂ) • (LinearMap.id : F z.2 →ₗ[ℂ] F z.2)) ∧
      (∀ z, 0 ≤ q z) ∧ ∀ z, z.2 ∉ L → 0 < q z := by
  classical
  dsimp only
  let p : C(I × X, X) := ContinuousMap.snd
  let q (z : I × X) : ℝ :=
    (1 - (z.1 : ℝ)) ^ 2 * (ρ z.2 : ℝ) ^ 2 +
      (z.1 : ℝ) * (1 - (z.1 : ℝ)) * (ρ z.2 : ℝ) * (1 + r z.2) +
      (z.1 : ℝ) ^ 2 * r z.2
  let A := a.cutoffHom ρ U hU haU hzero
  let A' := a.inverse.cutoffHom ρ U hU haU hzero
  let f : C(I × X, ℂ) := ⟨fun z ↦ ((1 - (z.1 : ℝ) : ℝ) : ℂ), by fun_prop⟩
  let g : C(I × X, ℂ) := ⟨fun z ↦ ((z.1 : ℝ) : ℂ), by fun_prop⟩
  let d := linearCombinationHom (A.pullback p) (c.pullback p) f g
  let d' := linearCombinationHom (A'.pullback p) (c'.pullback p) f (-g)
  have hd (z : I × X) : d.linearMap z =
      ((1 - (z.1 : ℝ) : ℝ) : ℂ) • A.linearMap z.2 +
        ((z.1 : ℝ) : ℂ) • c.linearMap z.2 := rfl
  have hd' (z : I × X) : d'.linearMap z =
      ((1 - (z.1 : ℝ) : ℝ) : ℂ) • A'.linearMap z.2 -
        ((z.1 : ℝ) : ℂ) • c'.linearMap z.2 := by
    change _ + (-(g z)) • _ = _
    rw [neg_smul, sub_eq_add_neg]
    rfl
  refine ⟨d, d', hd, hd', ?_, ?_, ?_⟩
  · intro z
    let x := z.2
    let α : ℂ := ((1 - (z.1 : ℝ) : ℝ) : ℂ)
    let β : ℂ := ((z.1 : ℝ) : ℂ)
    let aρ : ℂ := ((ρ x : ℝ) : ℂ)
    have hcut : A.linearMap x = aρ • c.linearMap x := by
      by_cases hx : x ∈ a.control
      · have hz := hzero x (haU hx)
        simp [A, CompactSupportTriple.cutoffHom, CompactSupportTriple.cutoffLinearMap,
          hx, aρ, hz]
      · change a.cutoffLinearMap ρ x = _
        rw [CompactSupportTriple.cutoffLinearMap, dite_eq_right hx, hc ⟨x, hx⟩]
    have hcross₀ : (A'.linearMap x).comp (c.linearMap x) = aρ • LinearMap.id := by
      by_cases hx : x ∈ a.control
      · have hz := hzero x (haU hx)
        simp [A', CompactSupportTriple.cutoffHom, CompactSupportTriple.cutoffLinearMap,
          CompactSupportTriple.inverse, hx, aρ, hz]
      · change (a.inverse.cutoffLinearMap ρ x).comp (c.linearMap x) = _
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hx]
        rw [← hc ⟨x, hx⟩]
        apply LinearMap.ext
        intro v
        exact congrArg (aρ • ·) ((a.boundary.linearEquiv ⟨x, hx⟩).symm_apply_apply v)
    have hcross₁ : (c.linearMap x).comp (A'.linearMap x) = aρ • LinearMap.id := by
      by_cases hx : x ∈ a.control
      · have hz := hzero x (haU hx)
        simp [A', CompactSupportTriple.cutoffHom, CompactSupportTriple.cutoffLinearMap,
          CompactSupportTriple.inverse, hx, aρ, hz]
      · change (c.linearMap x).comp (a.inverse.cutoffLinearMap ρ x) = _
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hx]
        rw [← hc ⟨x, hx⟩]
        apply LinearMap.ext
        intro v
        change (a.boundary.linearEquiv ⟨x, hx⟩)
          (aρ • (a.boundary.linearEquiv ⟨x, hx⟩).symm v) = aρ • v
        rw [map_smul, LinearEquiv.apply_symm_apply]
    have hcut₀ := (a.cutoffHom_inverse_comp ρ U hU haU hzero x).1
    have hcut₁ := (a.cutoffHom_inverse_comp ρ U hU haU hzero x).2
    have hc₀ := (hsq x).1
    have hc₁ := (hsq x).2
    have hscalar : α ^ 2 * aρ ^ 2 + α * β * aρ * (1 + (r x : ℂ)) + β ^ 2 * (r x : ℂ) =
        (q z : ℂ) := by
      dsimp [α, β, aρ, q, x]
      push_cast
      ring
    constructor
    · rw [hd, hd']
      apply LinearMap.ext
      intro v
      change E x at v
      have ha₀ := LinearMap.congr_fun hcut₀ v
      have ha₁ := LinearMap.congr_fun hcross₀ v
      have hc₂ := LinearMap.congr_fun hc₀ v
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
        at ha₀ ha₁ hc₂
      change (α • A'.linearMap x - β • c'.linearMap x)
        ((α • A.linearMap x + β • c.linearMap x) v) = _
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        map_add, map_smul]
      change α • (α • A'.linearMap x (A.linearMap x v) -
          β • c'.linearMap x (A.linearMap x v)) +
        β • (α • A'.linearMap x (c.linearMap x v) -
          β • c'.linearMap x (c.linearMap x v)) = (q z : ℂ) • v
      rw [ha₀, ha₁, hc₂, hcut]
      simp only [LinearMap.smul_apply, map_smul]
      rw [hc₂]
      rw [← hscalar]
      module
    · rw [hd, hd']
      apply LinearMap.ext
      intro v
      change F x at v
      have ha₀ := LinearMap.congr_fun hcut₁ v
      have ha₁ := LinearMap.congr_fun hcross₁ v
      have hc₂ := LinearMap.congr_fun hc₁ v
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
        at ha₀ ha₁ hc₂
      change (α • A.linearMap x + β • c.linearMap x)
        ((α • A'.linearMap x - β • c'.linearMap x) v) = _
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        map_sub, map_smul]
      change α • (α • A.linearMap x (A'.linearMap x v) +
          β • c.linearMap x (A'.linearMap x v)) -
        β • (α • A.linearMap x (c'.linearMap x v) +
          β • c.linearMap x (c'.linearMap x v)) = (q z : ℂ) • v
      rw [ha₀, ha₁, hc₂, hcut]
      simp only [LinearMap.smul_apply]
      rw [hc₂]
      rw [← hscalar]
      module
  · intro z
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg z.1.property.1 (sub_nonneg.mpr z.1.property.2))
        (ρ z.2).property.1) (by linarith [hr z.2])))
      (mul_nonneg (sq_nonneg _) (hr z.2))
  · intro z hz
    have hx : z.2 ∉ a.control := fun h ↦ hz (hUL (haU h))
    have hpos := hrpos z.2 hx
    have hρ := hone z.2 hz
    rw [hρ]
    simp only [Set.Icc.coe_one, one_pow, mul_one]
    by_cases ht : (z.1 : ℝ) < 1
    · have hfirst : 0 < (1 - (z.1 : ℝ)) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht)
      have hmid : 0 ≤ (z.1 : ℝ) * (1 - (z.1 : ℝ)) * (1 + r z.2) :=
        mul_nonneg (mul_nonneg z.1.property.1 (sub_nonneg.mpr z.1.property.2)) (by linarith)
      have hlast := mul_nonneg (sq_nonneg (z.1 : ℝ)) (hr z.2)
      linarith
    · have ht' : (z.1 : ℝ) = 1 := le_antisymm z.1.property.2 (le_of_not_gt ht)
      simpa only [ht', sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
        one_mul, add_zero, zero_add, one_pow] using hpos

end AtiyahSinger.ComplexBundle
