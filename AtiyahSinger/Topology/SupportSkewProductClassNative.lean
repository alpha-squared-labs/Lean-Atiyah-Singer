/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorTransport
public import AtiyahSinger.Topology.SupportSkewProductClass

/-!
# The skew product in the original bundle universes

Public module ID: M2189.

Conjugate the actual symbols by the existing small-bundle comparisons, apply
the supported product theorem, and return through the same tensor and sum
isomorphisms. The control sets and four original bundle fibers are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem transportSkewPair {X : Type*} [TopologicalSpace X]
    {E F : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (a : CompactSupportTriple E F) (c : Hom E F) (c' : Hom F E) (r : X → ℝ)
    (hc : ∀ x : (a.controlᶜ : Set X),
      (a.boundary.linearEquiv x).toLinearMap = c.linearMap x.val)
    (hq : ∀ x, (c'.linearMap x).comp (c.linearMap x) = -(r x : ℂ) • LinearMap.id ∧
      (c.linearMap x).comp (c'.linearMap x) = -(r x : ℂ) • LinearMap.id) :
    let i := smallBundleIso E
    let j := smallBundleIso F
    let d := j.toHom.comp (c.comp i.symm.toHom)
    let d' := i.toHom.comp (c'.comp j.symm.toHom)
    (∀ x : (a.controlᶜ : Set X),
      (a.toSupportBundleTriple.datum.boundary.linearEquiv x).toLinearMap = d.linearMap x.val) ∧
    (∀ x, (d'.linearMap x).comp (d.linearMap x) = -(r x : ℂ) • LinearMap.id ∧
      (d.linearMap x).comp (d'.linearMap x) = -(r x : ℂ) • LinearMap.id) := by
  dsimp only
  constructor
  · intro x
    apply LinearMap.ext
    intro v
    change (smallBundleIso F).linearEquiv x
      (a.boundary.linearEquiv x (((smallBundleIso E).linearEquiv x).symm v)) = _
    have h := LinearMap.congr_fun (hc x) (((smallBundleIso E).linearEquiv x).symm v)
    change a.boundary.linearEquiv x _ = _ at h
    rw [h]
    rfl
  · intro x
    constructor
    · apply LinearMap.ext
      intro v
      change (smallBundleIso E).linearEquiv x
        (c'.linearMap x (((smallBundleIso F).linearEquiv x).symm
          ((smallBundleIso F).linearEquiv x
            (c.linearMap x (((smallBundleIso E).linearEquiv x).symm v))))) = _
      rw [LinearEquiv.symm_apply_apply]
      have h := LinearMap.congr_fun (hq x).1 (((smallBundleIso E).linearEquiv x).symm v)
      change c'.linearMap x (c.linearMap x _) = -(r x : ℂ) • _ at h
      rw [h, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]
      rfl
    · apply LinearMap.ext
      intro v
      change (smallBundleIso F).linearEquiv x
        (c.linearMap x (((smallBundleIso E).linearEquiv x).symm
          ((smallBundleIso E).linearEquiv x
            (c'.linearMap x (((smallBundleIso F).linearEquiv x).symm v))))) = _
      rw [LinearEquiv.symm_apply_apply]
      have h := LinearMap.congr_fun (hq x).2 (((smallBundleIso F).linearEquiv x).symm v)
      change c.linearMap x (c'.linearMap x _) = -(r x : ℂ) • _ at h
      rw [h, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]
      rfl

set_option maxHeartbeats 900000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original-universe skew tensor symbol gives the product of the original support classes. -/
theorem CompactSupportTriple.compactSupportClass_externalProduct_of_skew
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
    ∀ (k : CompactSupportTriple
        (fun z ↦ (((p₁ *ᵖ E₀) z ⊗[ℂ] (p₂ *ᵖ F₀) z) ×
          ((p₁ *ᵖ E₁) z ⊗[ℂ] (p₂ *ᵖ F₁) z)))
        (fun z ↦ (((p₁ *ᵖ E₁) z ⊗[ℂ] (p₂ *ᵖ F₀) z) ×
          ((p₁ *ᵖ E₀) z ⊗[ℂ] (p₂ *ᵖ F₁) z))))
      (_hkcontrol : k.control ⊆ a.control ×ˢ b.control)
      (_hk : ∀ z : (k.controlᶜ : Set (X × Y)),
        (k.boundary.linearEquiv z).toLinearMap =
          reciprocalTensorSymbol (c.linearMap z.val.1) (-c'.linearMap z.val.1)
            (e.linearMap z.val.2) (-e'.linearMap z.val.2)),
    k.compactSupportClass =
      compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  classical
  dsimp only
  intro k hkcontrol hk
  let p₁ : C(X × Y, X) := ContinuousMap.fst
  let p₂ : C(X × Y, Y) := ContinuousMap.snd
  let i₀ := smallBundleIso E₀
  let i₁ := smallBundleIso E₁
  let j₀ := smallBundleIso F₀
  let j₁ := smallBundleIso F₁
  let d := i₁.toHom.comp (c.comp i₀.symm.toHom)
  let d' := i₀.toHom.comp (c'.comp i₁.symm.toHom)
  let f := j₁.toHom.comp (e.comp j₀.symm.toHom)
  let f' := j₀.toHom.comp (e'.comp j₁.symm.toHom)
  let iS := (((i₀.pullback p₁).tensor (j₀.pullback p₂)).sum
    ((i₁.pullback p₁).tensor (j₁.pullback p₂)))
  let iT := (((i₁.pullback p₁).tensor (j₀.pullback p₂)).sum
    ((i₀.pullback p₁).tensor (j₁.pullback p₂)))
  let small := k.congr iS iT
  have ha := transportSkewPair a c c' r hc hcq
  have hb := transportSkewPair b e e' s he heq
  -- The same four comparisons conjugate every block, including the two negative reverse maps.
  have hsmall : ∀ z : (small.controlᶜ : Set (X × Y)),
      (small.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (d.linearMap z.val.1) (-d'.linearMap z.val.1)
          (f.linearMap z.val.2) (-f'.linearMap z.val.2) := by
    intro z
    apply LinearMap.ext
    intro v
    change iT.linearEquiv z.val (k.boundary.linearEquiv z ((iS.linearEquiv z.val).symm v)) = _
    have hboundary := LinearMap.congr_fun (hk z) ((iS.linearEquiv z.val).symm v)
    change k.boundary.linearEquiv z _ = _ at hboundary
    rw [hboundary]
    have h := LinearMap.congr_fun
      (reciprocalTensorSymbol_congr (i₀.linearEquiv z.val.1) (i₁.linearEquiv z.val.1)
        (j₀.linearEquiv z.val.2) (j₁.linearEquiv z.val.2)
        (c.linearMap z.val.1) (-c'.linearMap z.val.1)
        (e.linearMap z.val.2) (-e'.linearMap z.val.2)) ((iS.linearEquiv z.val).symm v)
    simp only [LinearMap.comp_neg, LinearMap.neg_comp] at h
    change iT.linearEquiv z.val _ =
      reciprocalTensorSymbol (d.linearMap z.val.1) (-d'.linearMap z.val.1)
        (f.linearMap z.val.2) (-f'.linearMap z.val.2)
        (iS.linearEquiv z.val ((iS.linearEquiv z.val).symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hclass := SupportBundleTriple.compactSupportClass_externalProduct_of_skew
    a.toSupportBundleTriple b.toSupportBundleTriple d d' f f' r s
    ha.1 hb.1 ha.2 hb.2 hr hs hrpos hspos small hkcontrol hsmall
  exact (k.compactSupportClass_congr iS iT).symm.trans hclass

end AtiyahSinger.ComplexBundle
