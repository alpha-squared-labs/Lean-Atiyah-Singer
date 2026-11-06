/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ScalarSupportHomotopy
public import AtiyahSinger.Topology.SupportSkewProductClassNative

/-!
# The uncut external product of actual skew symbols

Public module ID: M2157.

The two original negative-square pairs give the exact positive tensor block
on the original pullback, tensor and sum bundles. Its control is the product
of the two original controls, and its class is their original supported product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback isFiniteRank_restrict

set_option maxHeartbeats 900000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The uncut positive tensor block has its original control and the original external K class. -/
theorem CompactSupportTriple.exists_skewExternalProduct
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    {E₀ E₁ : X → Type*} {F₀ F₁ : Y → Type*}
    [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
    [∀ y, AddCommGroup (F₀ y)] [∀ y, Module ℂ (F₀ y)]
    [∀ y, AddCommGroup (F₁ y)] [∀ y, Module ℂ (F₁ y)]
    [TopologicalSpace (TotalSpace Unit E₀)] [IsFiniteRank E₀]
    [TopologicalSpace (TotalSpace Unit E₁)] [IsFiniteRank E₁]
    [TopologicalSpace (TotalSpace Unit F₀)] [IsFiniteRank F₀]
    [TopologicalSpace (TotalSpace Unit F₁)] [IsFiniteRank F₁]
    (a : CompactSupportTriple E₀ E₁) (b : CompactSupportTriple F₀ F₁)
    (c : Hom E₀ E₁) (c' : Hom E₁ E₀) (e : Hom F₀ F₁) (e' : Hom F₁ F₀)
    (r : X → ℝ) (s : Y → ℝ)
    (hc : ∀ x : (a.controlᶜ : Set X),
      (a.boundary.linearEquiv x).toLinearMap = c.linearMap x.val)
    (he : ∀ y : (b.controlᶜ : Set Y),
      (b.boundary.linearEquiv y).toLinearMap = e.linearMap y.val)
    (hcq : ∀ x, (c'.linearMap x).comp (c.linearMap x) = -(r x : ℂ) • LinearMap.id ∧
      (c.linearMap x).comp (c'.linearMap x) = -(r x : ℂ) • LinearMap.id)
    (heq : ∀ y, (e'.linearMap y).comp (e.linearMap y) = -(s y : ℂ) • LinearMap.id ∧
      (e.linearMap y).comp (e'.linearMap y) = -(s y : ℂ) • LinearMap.id)
    (hr : ∀ x, 0 ≤ r x) (hs : ∀ y, 0 ≤ s y)
    (hrpos : ∀ x ∉ a.control, 0 < r x) (hspos : ∀ y ∉ b.control, 0 < s y) :
    let p₁ : C(X × Y, X) := ContinuousMap.fst
    let p₂ : C(X × Y, Y) := ContinuousMap.snd
    ∃ k : CompactSupportTriple
        (fun z ↦ (((p₁ *ᵖ E₀) z ⊗[ℂ] (p₂ *ᵖ F₀) z) ×
          ((p₁ *ᵖ E₁) z ⊗[ℂ] (p₂ *ᵖ F₁) z)))
        (fun z ↦ (((p₁ *ᵖ E₁) z ⊗[ℂ] (p₂ *ᵖ F₀) z) ×
          ((p₁ *ᵖ E₀) z ⊗[ℂ] (p₂ *ᵖ F₁) z))),
      k.control = a.control ×ˢ b.control ∧
      (∀ z : (k.controlᶜ : Set (X × Y)),
        (k.boundary.linearEquiv z).toLinearMap =
          reciprocalTensorSymbol (c.linearMap z.val.1) (-c'.linearMap z.val.1)
            (e.linearMap z.val.2) (-e'.linearMap z.val.2)) ∧
      k.compactSupportClass =
        compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  classical
  dsimp only
  let p₁ : C(X × Y, X) := ContinuousMap.fst
  let p₂ : C(X × Y, Y) := ContinuousMap.snd
  let cInv : Hom E₁ E₀ :=
    (Iso.scalar E₀ (ContinuousMap.const _ (-1)) (fun _ ↦ neg_ne_zero.mpr one_ne_zero)).toHom.comp c'
  let eInv : Hom F₁ F₀ :=
    (Iso.scalar F₀ (ContinuousMap.const _ (-1)) (fun _ ↦ neg_ne_zero.mpr one_ne_zero)).toHom.comp e'
  have hcInv (x : X) : cInv.linearMap x = -c'.linearMap x := by
    apply LinearMap.ext
    intro v
    change (-1 : ℂ) • c'.linearMap x v = -c'.linearMap x v
    exact neg_one_smul ℂ _
  have heInv (y : Y) : eInv.linearMap y = -e'.linearMap y := by
    apply LinearMap.ext
    intro v
    change (-1 : ℂ) • e'.linearMap y v = -e'.linearMap y v
    exact neg_one_smul ℂ _
  let Q := reciprocalTensorHom (c.pullback p₁) (cInv.pullback p₁)
    (e.pullback p₂) (eInv.pullback p₂)
  have hQ (z : X × Y) : Q.linearMap z =
      reciprocalTensorSymbol (c.linearMap z.1) (-c'.linearMap z.1)
        (e.linearMap z.2) (-e'.linearMap z.2) := by
    change reciprocalTensorSymbol (c.linearMap z.1) (cInv.linearMap z.1)
      (e.linearMap z.2) (eInv.linearMap z.2) = _
    rw [hcInv, heInv]
  let K := a.control ×ˢ b.control
  have hbij (z : (Kᶜ : Set (X × Y))) :
      Function.Bijective ((Q.restrict Kᶜ).linearMap z) := by
    change Function.Bijective (Q.linearMap z.val)
    rw [hQ]
    have hpos : 0 < r z.val.1 + s z.val.2 := by
      rcases not_and_or.mp z.property with hx | hy
      · exact add_pos_of_pos_of_nonneg (hrpos _ hx) (hs _)
      · exact add_pos_of_nonneg_of_pos (hr _) (hspos _ hy)
    have hnonzero : (r z.val.1 : ℂ) + (s z.val.2 : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hpos
    apply (reciprocalTensorSymbolEquiv _ _ _ _ _ _ ?_ ?_ ?_ ?_ hnonzero).bijective
    · rw [LinearMap.neg_comp, (hcq z.val.1).1, neg_smul, neg_neg]
    · rw [LinearMap.comp_neg, (hcq z.val.1).2, neg_smul, neg_neg]
    · rw [LinearMap.neg_comp, (heq z.val.2).1, neg_smul, neg_neg]
    · rw [LinearMap.comp_neg, (heq z.val.2).2, neg_smul, neg_neg]
  let k : CompactSupportTriple _ _ :=
    { control := K
      isCompact_control := a.isCompact_control.prod b.isCompact_control
      boundary := (Q.restrict Kᶜ).toIso hbij }
  have hk : ∀ z : (k.controlᶜ : Set (X × Y)),
      (k.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (c.linearMap z.val.1) (-c'.linearMap z.val.1)
          (e.linearMap z.val.2) (-e'.linearMap z.val.2) := fun z ↦ hQ z.val
  refine ⟨k, rfl, hk, ?_⟩
  exact a.compactSupportClass_externalProduct_of_skew b c c' e e' r s hc he hcq heq
    hr hs hrpos hspos k (Set.Subset.refl _) hk

end AtiyahSinger.ComplexBundle
