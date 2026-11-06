/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantBundleTensor
public import AtiyahSinger.Topology.EquivariantSupportBundleTriple
public import AtiyahSinger.Topology.SupportTripleExternalProduct

/-!
# The actual equivariant external product of two support triples

Public module ID: M1782.

The original even and odd tensor bundles carry their diagonal actions. The
boundary is the same reciprocal-cutoff block as in the ordinary construction.
Invariant cutoffs make its actual fiber maps equivariant, and the chosen
control is precisely the product of the two enlarged invariant compact sets.
The projection pullbacks here are bundle pullbacks and require no properness.

This is the equivariant form of the graded product of Karoubi II.5.21--5.22
and SG Appendix C.1, in the compact-support framework of ASI I section 2.
The explicit reciprocal realization is a project supplement. The supplied
cutoff version does not need a compact group, Haar measure, a global metric
or a paracompact base. Compact groups and locally compact bases will supply
invariant cutoffs for the subsequent group operation. The equivariance proof
below retains the actual ordinary construction and its specified inverse.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The original even tensor bundle carries the sum of the two diagonal tensor actions. -/
def EquivariantSupportBundleTriple.externalProductSourceAction
    (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y) :
    EquivariantStructure G (a.1.externalProductSource b.1).Fiber :=
  ((a.2.sourceAction.pullback ⟨Prod.fst, continuous_fst⟩ (fun _ _ ↦ rfl)).tensor
    (b.2.sourceAction.pullback ⟨Prod.snd, continuous_snd⟩ (fun _ _ ↦ rfl))).sum
      ((a.2.targetAction.pullback ⟨Prod.fst, continuous_fst⟩ (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback ⟨Prod.snd, continuous_snd⟩ (fun _ _ ↦ rfl)))

/-- The original odd tensor bundle uses the same actions in its specified target order. -/
def EquivariantSupportBundleTriple.externalProductTargetAction
    (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y) :
    EquivariantStructure G (a.1.externalProductTarget b.1).Fiber :=
  ((a.2.targetAction.pullback ⟨Prod.fst, continuous_fst⟩ (fun _ _ ↦ rfl)).tensor
    (b.2.sourceAction.pullback ⟨Prod.snd, continuous_snd⟩ (fun _ _ ↦ rfl))).sum
      ((a.2.sourceAction.pullback ⟨Prod.fst, continuous_fst⟩ (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback ⟨Prod.snd, continuous_snd⟩ (fun _ _ ↦ rfl)))

variable [T2Space X] [T2Space Y]
  (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
  (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (ha : a.1.datum.control ⊆ U)
  (hρzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
  (hρone : ∀ x ∉ L, ρ x = 1)
  (τ : C(Y, I)) (V : Set Y) (hV : IsOpen V) (hb : b.1.datum.control ⊆ V)
  (hτzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (hM : IsCompact M)
  (hτone : ∀ y ∉ M, τ y = 1)
  (hρinv : ∀ (g : G) (x : X), ρ (g • x) = ρ x)
  (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
  (hτinv : ∀ (g : G) (y : Y), τ (g • y) = τ y)
  (hMinv : ∀ (g : G) (y : Y), g • y ∈ M ↔ y ∈ M)

set_option backward.isDefEq.respectTransparency.types false in
include hρinv hLinv hτinv hMinv in
/-- The same cutoff block intertwines the specified moving-fiber tensor actions. -/
theorem supportedExternalProductTriple_isEquivariant :
    (supportedExternalProductTriple a.1 b.1
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone).datum.IsEquivariant
        (a.externalProductSourceAction b) (a.externalProductTargetAction b) := by
  /- Stage 1: each original control is invariant. Inside it the cutoff map is
  zero; outside it the original boundary intertwines the specified actions.
  The same intertwining equation holds for the actual inverse boundary, by
  composing with its inverse and the moving-fiber action bijections. Invariance
  of the scalar cutoff therefore makes both original global cutoff maps
  equivariant. No independently averaged replacement map is used.
  Stage 2: the two projections intertwine the diagonal base action. The original
  pullback, tensor and sum actions consequently intertwine each block, with the
  displayed signs and fixed even/odd order. Check pure tensors and extend by
  linearity. The ordinary boundary's forward map is exactly this block.
  Stage 3: L times M is invariant because both given controls are invariant.
  Combine this fact with the preceding boundary square on its complement.
  Its inverse and continuity are already those of the same ordinary triple;
  no compactness of G, invariant metric or properness of a projection is needed. -/
  classical
  -- The original cutoff and its inverse intertwine the moving fibers on X.
  have hcutoffX : ∀ (E F : FiniteBundle X) (c : CompactSupportTriple E.Fiber F.Fiber)
      (sourceAction : EquivariantStructure G E.Fiber)
      (targetAction : EquivariantStructure G F.Fiber)
      (_hc : c.IsEquivariant sourceAction targetAction) (g : G) (x : X) (v : E.Fiber x),
      c.cutoffLinearMap ρ (g • x) (sourceAction.linearMap g x v) =
        targetAction.linearMap g x (c.cutoffLinearMap ρ x v) := by
    intro E F c sourceAction targetAction hc g x v
    by_cases hx : x ∈ c.control
    · have hgx := (hc.invariant_control g x).mpr hx
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hx,
        dite_eq_left hgx, LinearMap.zero_apply, map_zero]
    · have hgx : g • x ∉ c.control := fun h ↦ hx ((hc.invariant_control g x).mp h)
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hx,
        dite_eq_right hgx]
      change ((ρ (g • x) : ℝ) : ℂ) •
        c.boundary.linearEquiv ⟨g • x, hgx⟩ (sourceAction.linearMap g x v) =
          targetAction.linearMap g x
            (((ρ x : ℝ) : ℂ) • c.boundary.linearEquiv ⟨x, hx⟩ v)
      rw [hρinv g x, hc.boundary_intertwines g ⟨x, hx⟩ v]
      exact ((targetAction.linearMap g x).map_smul
        ((ρ x : ℝ) : ℂ) (c.boundary.linearEquiv ⟨x, hx⟩ v)).symm
  -- The same argument on Y retains its own original boundary and cutoff.
  have hcutoffY : ∀ (E F : FiniteBundle Y) (c : CompactSupportTriple E.Fiber F.Fiber)
      (sourceAction : EquivariantStructure G E.Fiber)
      (targetAction : EquivariantStructure G F.Fiber)
      (_hc : c.IsEquivariant sourceAction targetAction) (g : G) (y : Y) (v : E.Fiber y),
      c.cutoffLinearMap τ (g • y) (sourceAction.linearMap g y v) =
        targetAction.linearMap g y (c.cutoffLinearMap τ y v) := by
    intro E F c sourceAction targetAction hc g y v
    by_cases hy : y ∈ c.control
    · have hgy := (hc.invariant_control g y).mpr hy
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hy,
        dite_eq_left hgy, LinearMap.zero_apply, map_zero]
    · have hgy : g • y ∉ c.control := fun h ↦ hy ((hc.invariant_control g y).mp h)
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hy,
        dite_eq_right hgy]
      change ((τ (g • y) : ℝ) : ℂ) •
        c.boundary.linearEquiv ⟨g • y, hgy⟩ (sourceAction.linearMap g y v) =
          targetAction.linearMap g y
            (((τ y : ℝ) : ℂ) • c.boundary.linearEquiv ⟨y, hy⟩ v)
      rw [hτinv g y, hc.boundary_intertwines g ⟨y, hy⟩ v]
      exact ((targetAction.linearMap g y).map_smul
        ((τ y : ℝ) : ℂ) (c.boundary.linearEquiv ⟨y, hy⟩ v)).symm
  have hD := hcutoffX a.1.source a.1.target a.1.datum
    a.2.sourceAction a.2.targetAction a.2.isEquivariant
  have hD' := hcutoffX a.1.target a.1.source a.1.datum.inverse
    a.2.targetAction a.2.sourceAction a.2.isEquivariant.inverse
  have hE := hcutoffY b.1.source b.1.target b.1.datum
    b.2.sourceAction b.2.targetAction b.2.isEquivariant
  have hE' := hcutoffY b.1.target b.1.source b.1.datum.inverse
    b.2.targetAction b.2.sourceAction b.2.isEquivariant.inverse
  -- Keep precisely the supplied product control and its diagonal invariance.
  have hInv (g : G) (z : X × Y) : g • z ∈ Set.prod L M ↔ z ∈ Set.prod L M :=
    and_congr (hLinv g z.1) (hMinv g z.2)
  refine ⟨hInv, ?_⟩
  intro g z v
  -- Pure tensors determine the original signed block, including both target summands.
  have hblock :
      (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap ρ (g • z.val.1))
        (a.1.datum.inverse.cutoffLinearMap ρ (g • z.val.1))
        (b.1.datum.cutoffLinearMap τ (g • z.val.2))
        (b.1.datum.inverse.cutoffLinearMap τ (g • z.val.2))).comp
          ((TensorProduct.map (a.2.sourceAction.linearMap g z.val.1)
            (b.2.sourceAction.linearMap g z.val.2)).prodMap
              (TensorProduct.map (a.2.targetAction.linearMap g z.val.1)
                (b.2.targetAction.linearMap g z.val.2))) =
        ((TensorProduct.map (a.2.targetAction.linearMap g z.val.1)
          (b.2.sourceAction.linearMap g z.val.2)).prodMap
            (TensorProduct.map (a.2.sourceAction.linearMap g z.val.1)
              (b.2.targetAction.linearMap g z.val.2))).comp
          (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap ρ z.val.1)
            (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
            (b.1.datum.cutoffLinearMap τ z.val.2)
            (b.1.datum.inverse.cutoffLinearMap τ z.val.2)) := by
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro u w <;> apply Prod.ext <;>
      simp [reciprocalTensorSymbol, hD, hD', hE, hE']
  exact LinearMap.congr_fun hblock v

/-- The equivariant product retains exactly the ordinary tensor triple and its chosen control. -/
def supportedEquivariantExternalProductTriple : EquivariantSupportBundleTriple G (X × Y) :=
  ⟨supportedExternalProductTriple a.1 b.1
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone,
    { sourceAction := a.externalProductSourceAction b
      targetAction := a.externalProductTargetAction b
      isEquivariant := supportedExternalProductTriple_isEquivariant a b
        ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
        hρinv hLinv hτinv hMinv }⟩

end AtiyahSinger.ComplexBundle
