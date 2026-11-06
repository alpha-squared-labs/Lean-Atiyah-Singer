/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantHermitianProductRealization
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The original full Hermitian supported product

Public module ID: M1905.

The full forward maps and their specified adjoints give the actual
reciprocal tensor block on the original tensor bundles. Its control is the product
of the original two controls. The existing equivariant product theorem, with
identity actions, supplies the ordinary class comparison. No compactness of
either base or global constant rank is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback isFiniteRank_restrict finite_fiber

@[instance_reducible]
private def identityMulAction (Z : Type*) : MulAction Unit Z where
  smul _ z := z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def identityEquivariantTriple {Z : Type*} [TopologicalSpace Z]
    (c : SupportBundleTriple Z) :
    letI := identityMulAction Z
    letI : ContinuousSMul Unit Z := ⟨continuous_snd⟩
    EquivariantSupportBundleTriple Unit Z := by
  letI := identityMulAction Z
  letI : ContinuousSMul Unit Z := ⟨continuous_snd⟩
  let action (E : FiniteBundle Z) : EquivariantStructure Unit E.Fiber :=
    { linearMap _ _ := LinearMap.id
      one_map _ _ := rfl
      mul_map _ _ _ _ := rfl
      continuous_action := continuous_snd }
  exact ⟨c, action c.source, action c.target,
    ⟨fun _ _ ↦ Iff.rfl, fun _ _ _ ↦ rfl⟩⟩

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The identity-action comparison retains the original dependent external-product bundles.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_small_hermitianSupportProduct
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y]
    (a : SupportBundleTriple X) (b : SupportBundleTriple Y)
    (h₀ : ∀ x, InnerProductSpace.Core ℂ (a.source.Fiber x))
    (h₁ : ∀ x, InnerProductSpace.Core ℂ (a.target.Fiber x))
    (k₀ : ∀ y, InnerProductSpace.Core ℂ (b.source.Fiber y))
    (k₁ : ∀ y, InnerProductSpace.Core ℂ (b.target.Fiber y))
    (p : Hom a.source.Fiber a.target.Fiber)
    (pi : Hom a.target.Fiber a.source.Fiber)
    (q : Hom b.source.Fiber b.target.Fiber)
    (qi : Hom b.target.Fiber b.source.Fiber)
    (hp : ∀ x u v, (h₁ x).inner (p.linearMap x u) v =
      (h₀ x).inner u (pi.linearMap x v))
    (hq : ∀ y u v, (k₁ y).inner (q.linearMap y u) v =
      (k₀ y).inner u (qi.linearMap y v))
    (ha : ∀ x : (a.datum.controlᶜ : Set X),
      (a.datum.boundary.linearEquiv x).toLinearMap = p.linearMap x.val)
    (hb : ∀ y : (b.datum.controlᶜ : Set Y),
      (b.datum.boundary.linearEquiv y).toLinearMap = q.linearMap y.val) :
    ∃ d : CompactSupportTriple (a.externalProductSource b).Fiber
        (a.externalProductTarget b).Fiber,
      d.control = a.datum.control ×ˢ b.datum.control ∧
      (∀ z : (d.controlᶜ : Set (X × Y)), (d.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (p.linearMap z.val.1) (pi.linearMap z.val.1)
          (q.linearMap z.val.2) (qi.linearMap z.val.2)) ∧
      d.compactSupportClass =
        compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  let := identityMulAction X
  let := identityMulAction Y
  let : ContinuousSMul Unit X := ⟨continuous_snd⟩
  let : ContinuousSMul Unit Y := ⟨continuous_snd⟩
  -- Identity actions keep the input bundles, full maps, and boundaries literally unchanged.
  obtain ⟨d, hd, hde, hformula, hclass⟩ :=
    exists_equivariantHermitianSupportProduct
      (identityEquivariantTriple a) (identityEquivariantTriple b) h₀ h₁ k₀ k₁
      p pi q qi hp hq (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
      (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) ha hb
  refine ⟨d, hd, hformula, ?_⟩
  -- The original forgetful theorem identifies this same matrix with the ordinary product.
  have H := congrArg
    (fun t ↦ supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget t))
    hclass
  rw [equivariantSupportKZeroExternalProduct_forget] at H
  simp only [equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply] at H
  exact (compactSupportTriple_compactSupportClass_ofBoundary
    (a.externalProductSource b) (a.externalProductTarget b) d).trans H

@[instance_reducible]
private def transportedHermitianCore {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (h : InnerProductSpace.Core ℂ V)
    (e : V ≃ₗ[ℂ] W) : InnerProductSpace.Core ℂ W :=
  { inner u v := h.inner (e.symm u) (e.symm v)
    conj_inner_symm u v := h.conj_inner_symm _ _
    re_inner_nonneg u := h.re_inner_nonneg _
    add_left u v w := by rw [map_add, h.add_left]
    smul_left u v c := by rw [map_smul, h.smul_left]
    definite u hu := e.symm.injective ((h.definite _ hu).trans (map_zero e.symm).symm) }


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y]
  {E₀ E₁ : X → Type*} {F₀ F₁ : Y → Type*}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ y, AddCommGroup (F₀ y)] [∀ y, Module ℂ (F₀ y)]
  [∀ y, AddCommGroup (F₁ y)] [∀ y, Module ℂ (F₁ y)]
  [TopologicalSpace (TotalSpace Unit E₀)] [IsFiniteRank E₀]
  [TopologicalSpace (TotalSpace Unit E₁)] [IsFiniteRank E₁]
  [TopologicalSpace (TotalSpace Unit F₀)] [IsFiniteRank F₀]
  [TopologicalSpace (TotalSpace Unit F₁)] [IsFiniteRank F₁]

local notation "πX" => (ContinuousMap.fst : C(X × Y, X))
local notation "πY" => (ContinuousMap.snd : C(X × Y, Y))
local notation "Source" => fun z : X × Y ↦
  ((πX *ᵖ E₀) z ⊗[ℂ] (πY *ᵖ F₀) z) × ((πX *ᵖ E₁) z ⊗[ℂ] (πY *ᵖ F₁) z)
local notation "Target" => fun z : X × Y ↦
  ((πX *ᵖ E₁) z ⊗[ℂ] (πY *ᵖ F₀) z) × ((πX *ᵖ E₀) z ⊗[ℂ] (πY *ᵖ F₁) z)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- Four independent universe levels are compared through their actual tensor bundle maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Full maps and their Hermitian adjoints realize the product class
on the original arbitrary-universe fibers. -/
theorem exists_hermitianSupportProduct
    (a : CompactSupportTriple E₀ E₁) (b : CompactSupportTriple F₀ F₁)
    (h₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
    (h₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
    (k₀ : ∀ y, InnerProductSpace.Core ℂ (F₀ y))
    (k₁ : ∀ y, InnerProductSpace.Core ℂ (F₁ y))
    (p : Hom E₀ E₁) (pi : Hom E₁ E₀) (q : Hom F₀ F₁) (qi : Hom F₁ F₀)
    (hp : ∀ x u v, (h₁ x).inner (p.linearMap x u) v =
      (h₀ x).inner u (pi.linearMap x v))
    (hq : ∀ y u v, (k₁ y).inner (q.linearMap y u) v =
      (k₀ y).inner u (qi.linearMap y v))
    (ha : ∀ x : (a.controlᶜ : Set X),
      (a.boundary.linearEquiv x).toLinearMap = p.linearMap x.val)
    (hb : ∀ y : (b.controlᶜ : Set Y),
      (b.boundary.linearEquiv y).toLinearMap = q.linearMap y.val) :
    ∃ d : CompactSupportTriple Source Target,
      d.control = a.control ×ˢ b.control ∧
      (∀ z : (d.controlᶜ : Set (X × Y)), (d.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (p.linearMap z.val.1) (pi.linearMap z.val.1)
          (q.linearMap z.val.2) (qi.linearMap z.val.2)) ∧
      d.compactSupportClass =
        compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  classical
  let e₀ := smallBundleIso E₀
  let e₁ := smallBundleIso E₁
  let f₀ := smallBundleIso F₀
  let f₁ := smallBundleIso F₁
  -- Resizing transports the specified forms and both directions of each full map together.
  let P := e₁.toHom.comp (p.comp e₀.symm.toHom)
  let Pi := e₀.toHom.comp (pi.comp e₁.symm.toHom)
  let Q := f₁.toHom.comp (q.comp f₀.symm.toHom)
  let Qi := f₀.toHom.comp (qi.comp f₁.symm.toHom)
  have hP (x : X) (u : (smallBundle E₀).Fiber x) (v : (smallBundle E₁).Fiber x) :
      (transportedHermitianCore (h₁ x) (e₁.linearEquiv x)).inner (P.linearMap x u) v =
        (transportedHermitianCore (h₀ x) (e₀.linearEquiv x)).inner u (Pi.linearMap x v) := by
    change (h₁ x).inner ((e₁.linearEquiv x).symm
      (e₁.linearEquiv x (p.linearMap x ((e₀.linearEquiv x).symm u))))
      ((e₁.linearEquiv x).symm v) =
        (h₀ x).inner ((e₀.linearEquiv x).symm u)
          ((e₀.linearEquiv x).symm
            (e₀.linearEquiv x (pi.linearMap x ((e₁.linearEquiv x).symm v))))
    simpa only [LinearEquiv.symm_apply_apply] using
      hp x ((e₀.linearEquiv x).symm u) ((e₁.linearEquiv x).symm v)
  have hQ (y : Y) (u : (smallBundle F₀).Fiber y) (v : (smallBundle F₁).Fiber y) :
      (transportedHermitianCore (k₁ y) (f₁.linearEquiv y)).inner (Q.linearMap y u) v =
        (transportedHermitianCore (k₀ y) (f₀.linearEquiv y)).inner u (Qi.linearMap y v) := by
    change (k₁ y).inner ((f₁.linearEquiv y).symm
      (f₁.linearEquiv y (q.linearMap y ((f₀.linearEquiv y).symm u))))
      ((f₁.linearEquiv y).symm v) =
        (k₀ y).inner ((f₀.linearEquiv y).symm u)
          ((f₀.linearEquiv y).symm
            (f₀.linearEquiv y (qi.linearMap y ((f₁.linearEquiv y).symm v))))
    simpa only [LinearEquiv.symm_apply_apply] using
      hq y ((f₀.linearEquiv y).symm u) ((f₁.linearEquiv y).symm v)
  have hA (x : (a.toSupportBundleTriple.datum.controlᶜ : Set X)) :
      (a.toSupportBundleTriple.datum.boundary.linearEquiv x).toLinearMap = P.linearMap x.val := by
    apply LinearMap.ext
    intro v
    exact congrArg (e₁.linearEquiv x)
      (LinearMap.congr_fun (ha x) ((e₀.linearEquiv x).symm v))
  have hB (y : (b.toSupportBundleTriple.datum.controlᶜ : Set Y)) :
      (b.toSupportBundleTriple.datum.boundary.linearEquiv y).toLinearMap = Q.linearMap y.val := by
    apply LinearMap.ext
    intro v
    exact congrArg (f₁.linearEquiv y)
      (LinearMap.congr_fun (hb y) ((f₀.linearEquiv y).symm v))
  obtain ⟨d₀, hd₀, hformula, hclass⟩ := exists_small_hermitianSupportProduct
    a.toSupportBundleTriple b.toSupportBundleTriple
    (fun x ↦ transportedHermitianCore (h₀ x) (e₀.linearEquiv x))
    (fun x ↦ transportedHermitianCore (h₁ x) (e₁.linearEquiv x))
    (fun y ↦ transportedHermitianCore (k₀ y) (f₀.linearEquiv y))
    (fun y ↦ transportedHermitianCore (k₁ y) (f₁.linearEquiv y)) P Pi Q Qi hP hQ hA hB
  let eS := ((e₀.pullback πX).tensor (f₀.pullback πY)).sum
    ((e₁.pullback πX).tensor (f₁.pullback πY))
  let eT := ((e₁.pullback πX).tensor (f₀.pullback πY)).sum
    ((e₀.pullback πX).tensor (f₁.pullback πY))
  let d : CompactSupportTriple Source Target := d₀.congr eS.symm eT.symm
  have hblock (z : X × Y) :
      (eT.linearEquiv z).toLinearMap.comp
          (reciprocalTensorSymbol (p.linearMap z.1) (pi.linearMap z.1)
            (q.linearMap z.2) (qi.linearMap z.2)) =
        (reciprocalTensorSymbol (P.linearMap z.1) (Pi.linearMap z.1)
          (Q.linearMap z.2) (Qi.linearMap z.2)).comp (eS.linearEquiv z).toLinearMap := by
    -- Compare the reciprocal blocks through the same specified fiber isomorphisms.
    change ((TensorProduct.congr (e₁.linearEquiv z.1) (f₀.linearEquiv z.2)).prodCongr
      (TensorProduct.congr (e₀.linearEquiv z.1) (f₁.linearEquiv z.2))).toLinearMap.comp
        (reciprocalTensorSymbol (p.linearMap z.1) (pi.linearMap z.1)
          (q.linearMap z.2) (qi.linearMap z.2)) =
      (reciprocalTensorSymbol (P.linearMap z.1) (Pi.linearMap z.1)
        (Q.linearMap z.2) (Qi.linearMap z.2)).comp
          ((TensorProduct.congr (e₀.linearEquiv z.1) (f₀.linearEquiv z.2)).prodCongr
            (TensorProduct.congr (e₁.linearEquiv z.1) (f₁.linearEquiv z.2))).toLinearMap
    -- The four pure-tensor squares retain the upper-right minus sign and base-first order.
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro u v
    all_goals
      simp [P, Pi, Q, Qi, Hom.comp, Iso.toHom, Iso.symm, reciprocalTensorSymbol,
        LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.coprod_apply]
  refine ⟨d, hd₀, ?_, ?_⟩
  · intro z
    apply LinearMap.ext
    intro v
    apply (eT.linearEquiv z).injective
    change eT.linearEquiv z ((eT.linearEquiv z).symm
      (d₀.boundary.linearEquiv z (eS.linearEquiv z v))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (LinearMap.congr_fun (hformula z) (eS.linearEquiv z v)).trans
      (LinearMap.congr_fun (hblock z.val) v).symm
  · -- Conjugation is the actual arbitrary-universe class comparison already used by the model.
    exact (d₀.compactSupportClass_congr eS.symm eT.symm).trans hclass

end AtiyahSinger.ComplexBundle
