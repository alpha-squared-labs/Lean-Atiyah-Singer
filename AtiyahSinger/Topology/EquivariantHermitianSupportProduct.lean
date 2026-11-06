/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianReciprocalCutoff
public import AtiyahSinger.Topology.EquivariantBundleAffineHomotopy
public import AtiyahSinger.Topology.EquivariantKExternalProduct

/-!
# The actual equivariant external product of Hermitian graded boundaries

Public module ID: M1788.

A graded boundary built from full forward maps and their prescribed Hermitian
adjoints represents the original equivariant support product. Its direct
homotopy to the original reciprocal-cutoff boundary has one compact invariant
control and retains all four bundles, actions, signs and forward maps.
The input triples need agree with the full maps only outside their own controls.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback finite_fiber

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [T2Space X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [T2Space Y] [LocallyCompactSpace Y]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The entire affine cylinder uses the original reciprocal product and its original actions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A prescribed full Hermitian graded boundary represents the actual equivariant product. -/
theorem equivariantSupportKZeroExternalProduct_eq_of_hermitian
    (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
    (h₀ : ∀ x, InnerProductSpace.Core ℂ (a.1.source.Fiber x))
    (h₁ : ∀ x, InnerProductSpace.Core ℂ (a.1.target.Fiber x))
    (k₀ : ∀ y, InnerProductSpace.Core ℂ (b.1.source.Fiber y))
    (k₁ : ∀ y, InnerProductSpace.Core ℂ (b.1.target.Fiber y))
    (p : ∀ x, a.1.source.Fiber x →ₗ[ℂ] a.1.target.Fiber x)
    (pi : ∀ x, a.1.target.Fiber x →ₗ[ℂ] a.1.source.Fiber x)
    (q : ∀ y, b.1.source.Fiber y →ₗ[ℂ] b.1.target.Fiber y)
    (qi : ∀ y, b.1.target.Fiber y →ₗ[ℂ] b.1.source.Fiber y)
    (hp : ∀ x u v, (h₁ x).inner (p x u) v = (h₀ x).inner u (pi x v))
    (hq : ∀ y u v, (k₁ y).inner (q y u) v = (k₀ y).inner u (qi y v))
    (ha : ∀ x : (a.1.datum.controlᶜ : Set X),
      (a.1.datum.boundary.linearEquiv x).toLinearMap = p x.val)
    (hb : ∀ y : (b.1.datum.controlᶜ : Set Y),
      (b.1.datum.boundary.linearEquiv y).toLinearMap = q y.val)
    (d : CompactSupportTriple (a.1.externalProductSource b.1).Fiber
      (a.1.externalProductTarget b.1).Fiber)
    (hd : d.IsEquivariant (a.externalProductSourceAction b) (a.externalProductTargetAction b))
    (hformula : ∀ z : (d.controlᶜ : Set (X × Y)),
      (d.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (p z.val.1) (pi z.val.1) (q z.val.2) (qi z.val.2)) :
    equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass =
      (EquivariantSupportBundleTriple.ofBoundary (a.1.externalProductSource b.1)
        (a.1.externalProductTarget b.1) d
        (a.externalProductSourceAction b) (a.externalProductTargetAction b) hd).kZeroClass := by
  classical
  -- Choose invariant cutoffs for the actual input triples, with their actual zero neighborhoods.
  obtain ⟨U, hU, haU, _, L, hL, hUL, hLi, ρ, hρi, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
  obtain ⟨V, hV, hbV, _, M, hM, hVM, hMi, τ, hτi, hτzero, hτone⟩ :=
    exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
  let e := supportedEquivariantExternalProductTriple a b
    ρ U hU haU hρzero L hL hρone τ V hV hbV hτzero M hM hτone hρi hLi hτi hMi
  let K : Set (X × Y) := (L ×ˢ M) ∪ d.control
  have hK : IsCompact K := (hL.prod hM).union d.isCompact_control
  have hKi (g : G) (z : X × Y) : g • z ∈ K ↔ z ∈ K :=
    or_congr (and_congr (hLi g z.1) (hMi g z.2)) (hd.invariant_control g z)
  have hdK : d.control ⊆ K := Set.subset_union_right
  have heK : e.1.datum.control ⊆ K := Set.subset_union_left
  -- The inverse cutoff composes with the full forward map to the original single cutoff.
  have hcutX (x : X) :
      a.1.datum.cutoffLinearMap ρ x = ((ρ x : ℝ) : ℂ) • p x ∧
      (a.1.datum.inverse.cutoffLinearMap ρ x).comp (p x) =
        ((ρ x : ℝ) : ℂ) • LinearMap.id ∧
      (p x).comp (a.1.datum.inverse.cutoffLinearMap ρ x) =
        ((ρ x : ℝ) : ℂ) • LinearMap.id := by
    by_cases hx : x ∈ a.1.datum.control
    · have hz : ρ x = 0 := hρzero x (haU hx)
      simp [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse, hx, hz]
    · have heq := ha ⟨x, hx⟩
      rw [← heq]
      simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        dite_eq_right hx]
      refine ⟨True.intro, ?_, ?_⟩
      · ext v
        change ((ρ x : ℝ) : ℂ) •
          (a.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm
            (a.1.datum.boundary.linearEquiv ⟨x, hx⟩ v) = _
        rw [LinearEquiv.symm_apply_apply]
        rfl
      · ext v
        change a.1.datum.boundary.linearEquiv ⟨x, hx⟩
          (((ρ x : ℝ) : ℂ) • (a.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm v) = _
        rw [map_smul, LinearEquiv.apply_symm_apply]
        rfl
  -- The inverse cutoff composes with the full forward map to the original single cutoff.
  have hcutY (x : Y) :
      b.1.datum.cutoffLinearMap τ x = ((τ x : ℝ) : ℂ) • q x ∧
      (b.1.datum.inverse.cutoffLinearMap τ x).comp (q x) =
        ((τ x : ℝ) : ℂ) • LinearMap.id ∧
      (q x).comp (b.1.datum.inverse.cutoffLinearMap τ x) =
        ((τ x : ℝ) : ℂ) • LinearMap.id := by
    by_cases hx : x ∈ b.1.datum.control
    · have hz : τ x = 0 := hτzero x (hbV hx)
      simp [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse, hx, hz]
    · have heq := hb ⟨x, hx⟩
      rw [← heq]
      simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        dite_eq_right hx]
      refine ⟨True.intro, ?_, ?_⟩
      · ext v
        change ((τ x : ℝ) : ℂ) •
          (b.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm
            (b.1.datum.boundary.linearEquiv ⟨x, hx⟩ v) = _
        rw [LinearEquiv.symm_apply_apply]
        rfl
      · ext v
        change b.1.datum.boundary.linearEquiv ⟨x, hx⟩
          (((τ x : ℝ) : ℂ) • (b.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm v) = _
        rw [map_smul, LinearEquiv.apply_symm_apply]
        rfl
  have H : d.EquivariantlyHomotopic e.1.datum
      (a.externalProductSourceAction b) (a.externalProductTargetAction b) := by
    apply d.equivariantlyHomotopic_of_affine e.1.datum
      (a.externalProductSourceAction b) (a.externalProductTargetAction b)
      hd e.2.isEquivariant K hK hKi hdK heK
    intro t z
    have hdom : ((ρ z.val.1 : ℝ) = 1 ∧ Function.Bijective (p z.val.1)) ∨
        ((τ z.val.2 : ℝ) = 1 ∧ Function.Bijective (q z.val.2)) := by
      have hout : z.val ∉ L ×ˢ M := fun h ↦ z.property (Or.inl h)
      by_cases hx : z.val.1 ∈ L
      · have hy : z.val.2 ∉ M := fun hy ↦ hout ⟨hx, hy⟩
        have hy' : z.val.2 ∉ b.1.datum.control := fun h ↦ hy (hVM (hbV h))
        right
        refine ⟨congrArg Subtype.val (hτone z.val.2 hy), ?_⟩
        rw [← hb ⟨z.val.2, hy'⟩]
        exact (b.1.datum.boundary.linearEquiv ⟨z.val.2, hy'⟩).bijective
      · have hx' : z.val.1 ∉ a.1.datum.control := fun h ↦ hx (hUL (haU h))
        left
        refine ⟨congrArg Subtype.val (hρone z.val.1 hx), ?_⟩
        rw [← ha ⟨z.val.1, hx'⟩]
        exact (a.1.datum.boundary.linearEquiv ⟨z.val.1, hx'⟩).bijective
    have hdmap : ((d.enlarge K hK hdK).boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (p z.val.1) (pi z.val.1) (q z.val.2) (qi z.val.2) := by
      ext v
      exact (d.enlarge_apply K hK hdK z v).trans
        (LinearMap.congr_fun (hformula ⟨z.val, fun h ↦ z.property (Or.inr h)⟩) v)
    have hemap : ((e.1.datum.enlarge K hK heK).boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (((ρ z.val.1 : ℝ) : ℂ) • p z.val.1)
          (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
          (((τ z.val.2 : ℝ) : ℂ) • q z.val.2)
          (b.1.datum.inverse.cutoffLinearMap τ z.val.2) := by
      ext v
      refine (e.1.datum.enlarge_apply K hK heK z v).trans ?_
      change reciprocalTensorSymbol (a.1.datum.cutoffLinearMap ρ z.val.1)
        (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
        (b.1.datum.cutoffLinearMap τ z.val.2)
        (b.1.datum.inverse.cutoffLinearMap τ z.val.2) v = _
      rw [(hcutX z.val.1).1, (hcutY z.val.2).1]
      rfl
    rw [hdmap, hemap]
    exact reciprocalTensorSymbol_hermitian_cutoff_affine_bijective
      (h₀ z.val.1) (h₁ z.val.1) (k₀ z.val.2) (k₁ z.val.2)
      (p z.val.1) (pi z.val.1) (q z.val.2) (qi z.val.2) (hp z.val.1) (hq z.val.2)
      (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
      (b.1.datum.inverse.cutoffLinearMap τ z.val.2) (ρ z.val.1) (τ z.val.2)
      (ρ z.val.1).property.1 (τ z.val.2).property.1
      (hcutX z.val.1).2.1 (hcutX z.val.1).2.2
      (hcutY z.val.2).2.1 (hcutY z.val.2).2.2 hdom t
  -- Evaluate the original product constructor, then use this fixed-action support homotopy.
  have hclass := equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (a.1.externalProductSource b.1) (a.1.externalProductTarget b.1)
    (a.externalProductSourceAction b) (a.externalProductTargetAction b)
    d e.1.datum hd e.2.isEquivariant H
  exact (equivariantSupportKZeroExternalProduct_class a b
    ρ U hU haU hρzero L hL hρone τ V hV hbV hτzero M hM hτone hρi hLi hτi hMi).trans
      hclass.symm

end AtiyahSinger.ComplexBundle
