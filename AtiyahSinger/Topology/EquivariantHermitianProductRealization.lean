/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantHermitianSupportProduct
public import AtiyahSinger.Topology.SupportSkewProductClass

/-!
# Realization of the equivariant full Hermitian product boundary

Public module ID: M1787.

The original continuous full factor maps and their given Hermitian adjoints
produce a continuous tensor boundary outside the product of the original
compact controls. Its original tensor actions make this actual triple
equivariant, and its class is the prescribed external product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback isFiniteRank_restrict finite_fiber

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [T2Space X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [T2Space Y] [LocallyCompactSpace Y]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The full factor maps stay defined inside either compact control as well as outside.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual full Hermitian block realizes the original equivariant supported product. -/
theorem exists_equivariantHermitianSupportProduct
    (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
    (h₀ : ∀ x, InnerProductSpace.Core ℂ (a.1.source.Fiber x))
    (h₁ : ∀ x, InnerProductSpace.Core ℂ (a.1.target.Fiber x))
    (k₀ : ∀ y, InnerProductSpace.Core ℂ (b.1.source.Fiber y))
    (k₁ : ∀ y, InnerProductSpace.Core ℂ (b.1.target.Fiber y))
    (p : Hom a.1.source.Fiber a.1.target.Fiber)
    (pi : Hom a.1.target.Fiber a.1.source.Fiber)
    (q : Hom b.1.source.Fiber b.1.target.Fiber)
    (qi : Hom b.1.target.Fiber b.1.source.Fiber)
    (hp : ∀ x u v, (h₁ x).inner (p.linearMap x u) v =
      (h₀ x).inner u (pi.linearMap x v))
    (hq : ∀ y u v, (k₁ y).inner (q.linearMap y u) v =
      (k₀ y).inner u (qi.linearMap y v))
    (hpg : p.IsEquivariant a.2.sourceAction a.2.targetAction)
    (hpig : pi.IsEquivariant a.2.targetAction a.2.sourceAction)
    (hqg : q.IsEquivariant b.2.sourceAction b.2.targetAction)
    (hqig : qi.IsEquivariant b.2.targetAction b.2.sourceAction)
    (ha : ∀ x : (a.1.datum.controlᶜ : Set X),
      (a.1.datum.boundary.linearEquiv x).toLinearMap = p.linearMap x.val)
    (hb : ∀ y : (b.1.datum.controlᶜ : Set Y),
      (b.1.datum.boundary.linearEquiv y).toLinearMap = q.linearMap y.val) :
    ∃ d : CompactSupportTriple (a.1.externalProductSource b.1).Fiber
        (a.1.externalProductTarget b.1).Fiber,
      d.control = a.1.datum.control ×ˢ b.1.datum.control ∧
      ∃ hd : d.IsEquivariant (a.externalProductSourceAction b) (a.externalProductTargetAction b),
        (∀ z : (d.controlᶜ : Set (X × Y)), (d.boundary.linearEquiv z).toLinearMap =
          reciprocalTensorSymbol (p.linearMap z.val.1) (pi.linearMap z.val.1)
            (q.linearMap z.val.2) (qi.linearMap z.val.2)) ∧
        (EquivariantSupportBundleTriple.ofBoundary (a.1.externalProductSource b.1)
          (a.1.externalProductTarget b.1) d
          (a.externalProductSourceAction b) (a.externalProductTargetAction b) hd).kZeroClass =
            equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass := by
  classical
  dsimp only [Hom.IsEquivariant] at hpg hpig hqg hqig
  let K := a.1.datum.control ×ˢ b.1.datum.control
  let A := reciprocalTensorHom (p.pullback (ContinuousMap.fst : C(X × Y, X)))
    (pi.pullback (ContinuousMap.fst : C(X × Y, X)))
    (q.pullback (ContinuousMap.snd : C(X × Y, Y)))
    (qi.pullback (ContinuousMap.snd : C(X × Y, Y)))
  -- At least one original boundary is invertible on the exact product-control complement.
  have hbij (z : (Kᶜ : Set (X × Y))) : Function.Bijective ((A.restrict Kᶜ).linearMap z) := by
    have hdom : Function.Bijective (p.linearMap z.val.1) ∨
        Function.Bijective (q.linearMap z.val.2) := by
      by_cases hx : z.val.1 ∈ a.1.datum.control
      · right
        have hy : z.val.2 ∉ b.1.datum.control := fun hy ↦ z.property ⟨hx, hy⟩
        rw [← hb ⟨z.val.2, hy⟩]
        exact (b.1.datum.boundary.linearEquiv ⟨z.val.2, hy⟩).bijective
      · left
        rw [← ha ⟨z.val.1, hx⟩]
        exact (a.1.datum.boundary.linearEquiv ⟨z.val.1, hx⟩).bijective
    have h := reciprocalTensorSymbol_bijective_of_hermitian_adjoint
      (h₀ z.val.1) (h₁ z.val.1) (k₀ z.val.2) (k₁ z.val.2)
      (p.linearMap z.val.1) (pi.linearMap z.val.1)
      (q.linearMap z.val.2) (qi.linearMap z.val.2) (hp z.val.1) (hq z.val.2) 1 1
      (hdom.elim (fun h ↦ Or.inl ⟨one_ne_zero, h⟩) (fun h ↦ Or.inr ⟨one_ne_zero, h⟩))
    change Function.Bijective (reciprocalTensorSymbol (p.linearMap z.val.1)
      (pi.linearMap z.val.1) (q.linearMap z.val.2) (qi.linearMap z.val.2))
    simpa only [Complex.ofReal_one, one_smul] using h
  let d : CompactSupportTriple (a.1.externalProductSource b.1).Fiber
      (a.1.externalProductTarget b.1).Fiber :=
    { control := K
      isCompact_control := a.1.datum.isCompact_control.prod b.1.datum.isCompact_control
      boundary := (A.restrict Kᶜ).toIso hbij }
  have hformula (z : (d.controlᶜ : Set (X × Y))) :
      (d.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (p.linearMap z.val.1) (pi.linearMap z.val.1)
          (q.linearMap z.val.2) (qi.linearMap z.val.2) := rfl
  have hd : d.IsEquivariant (a.externalProductSourceAction b)
      (a.externalProductTargetAction b) := by
    refine ⟨fun g z ↦ and_congr (a.2.isEquivariant.invariant_control g z.1)
      (b.2.isEquivariant.invariant_control g z.2), ?_⟩
    intro g z v
    -- All four full factor maps intertwine the original actions, including inside the controls.
    have hblock :
        (reciprocalTensorSymbol (p.linearMap (g • z.val.1))
          (pi.linearMap (g • z.val.1)) (q.linearMap (g • z.val.2))
          (qi.linearMap (g • z.val.2))).comp
            ((TensorProduct.map (a.2.sourceAction.linearMap g z.val.1)
              (b.2.sourceAction.linearMap g z.val.2)).prodMap
                (TensorProduct.map (a.2.targetAction.linearMap g z.val.1)
                  (b.2.targetAction.linearMap g z.val.2))) =
          ((TensorProduct.map (a.2.targetAction.linearMap g z.val.1)
            (b.2.sourceAction.linearMap g z.val.2)).prodMap
              (TensorProduct.map (a.2.sourceAction.linearMap g z.val.1)
                (b.2.targetAction.linearMap g z.val.2))).comp
            (reciprocalTensorSymbol (p.linearMap z.val.1) (pi.linearMap z.val.1)
              (q.linearMap z.val.2) (qi.linearMap z.val.2)) := by
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro u w <;> apply Prod.ext <;>
        simp [reciprocalTensorSymbol, hpg, hpig, hqg, hqig]
    exact LinearMap.congr_fun hblock v
  refine ⟨d, rfl, hd, hformula, ?_⟩
  exact (equivariantSupportKZeroExternalProduct_eq_of_hermitian a b h₀ h₁ k₀ k₁
    p.linearMap pi.linearMap q.linearMap qi.linearMap hp hq ha hb d hd hformula).symm

end AtiyahSinger.ComplexBundle
