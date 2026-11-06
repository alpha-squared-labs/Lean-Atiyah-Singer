/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantKExternalProduct
public import AtiyahSinger.Topology.EquivariantRestriction

/-!
# Compact-support external products for two independent groups

Public module ID: M1780.

Restrict the original G action along `G times H -> G` and the original H
action along `G times H -> H`, then apply the existing equivariant external
product. The native diagonal action on these two inflated bases is precisely
the independent action `(g, h) (x, y) = (g x, h y)`. No new action, quotient,
tensor bundle or compact control is selected.

The original reciprocal-cutoff construction retains both input triples and
uses the product of their enlarged compact controls. Compactness of the two
groups and local compactness of the Hausdorff bases enter only through that
existing construction's invariant-cutoff existence and presentation descent.

Sources: ASI I sections 2, 4 and 9, printed pp.494--495, 504--505 and 526--529,
give the equivariant support framework and different-group multiplicativity.
The projection-restriction construction and its forgetful compatibility are
standard explicit expansions, not separately numbered source lemmas. This
module constructs the topological product; it does not identify the cotangent
bundle of a product manifold or assert the analytic index formula.
The forgetful compatibility is proved for the original projection restrictions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

variable {G H X Y : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [T2Space X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [MulAction H Y] [ContinuousSMul H Y]
  [T2Space Y] [LocallyCompactSpace Y]

/-- The original support external product with the independent action of the product group. -/
def equivariantSupportKZeroDifferentGroupExternalProduct :
    letI : MulAction (G × H) X :=
      MulAction.compHom X (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) X :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) Y :=
      MulAction.compHom Y (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) Y :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    EquivariantSupportTripleKZero G X →+
      EquivariantSupportTripleKZero H Y →+
        EquivariantSupportTripleKZero (G × H) (X × Y) := by
  letI : MulAction (G × H) X :=
    MulAction.compHom X (ContinuousMonoidHom.fst G H).toMonoidHom
  letI : ContinuousSMul (G × H) X :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  letI : MulAction (G × H) Y :=
    MulAction.compHom Y (ContinuousMonoidHom.snd G H).toMonoidHom
  letI : ContinuousSMul (G × H) Y :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  -- Restriction retains the original fibers, boundaries and compact controls.
  let rX := equivariantSupportTripleKZeroRestrict (X := X) (ContinuousMonoidHom.fst G H)
  let rY := equivariantSupportTripleKZeroRestrict (X := Y) (ContinuousMonoidHom.snd G H)
  let μ := equivariantSupportKZeroExternalProduct (G := G × H) (X := X) (Y := Y)
  -- The old product's diagonal action on these inflated factors is the independent action.
  exact
    { toFun := fun a ↦ (μ (rX a)).comp rY
      map_zero' := by
        ext b
        simp
      map_add' := by
        intro a b
        ext c
        simp }

/-- Forgetting both actions recovers the same ordinary compact-support external product. -/
theorem equivariantSupportKZeroDifferentGroupExternalProduct_forget
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero H Y) :
    letI : MulAction (G × H) X :=
      MulAction.compHom X (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) X :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) Y :=
      MulAction.compHom Y (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) Y :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportKZeroDifferentGroupExternalProduct a b)) =
      compactSupportKZeroExternalProduct
        (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget a))
        (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget b)) := by
  /- Stage 1: apply the existing forgetful compatibility of the same-group
  external product to the two classes restricted along fst and snd. Its
  representative equation retains the original four tensor blocks, reciprocal
  cutoffs and product compact control; the group action has simply been erased.
  Stage 2: restriction and forgetting commute on the original support-group
  presentation. Apply those two equalities for the exact projection maps.
  The two ordinary input classes therefore are the original a and b after
  forgetting, with no properness requirement on either product projection.
  The existing compact-support comparison gives the displayed formula on
  arbitrary virtual classes, including empty bases and varying local ranks. -/
  let : MulAction (G × H) X :=
    MulAction.compHom X (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) X :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) Y :=
    MulAction.compHom Y (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) Y :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  -- The chosen product is the existing product of the two exact restricted classes.
  change supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportKZeroExternalProduct
          (equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.fst G H) a)
          (equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.snd G H) b))) = _
  rw [equivariantSupportKZeroExternalProduct_forget]
  -- Each restriction erases to its original input class under the same forgetful map.
  have ha := DFunLike.congr_fun
    (equivariantSupportRestriction_compatibility (X := X) (ContinuousMonoidHom.fst G H)).1 a
  have hb := DFunLike.congr_fun
    (equivariantSupportRestriction_compatibility (X := Y) (ContinuousMonoidHom.snd G H)).1 b
  simpa only [AddMonoidHom.comp_apply] using congrArg₂
    (fun x y ↦ compactSupportKZeroExternalProduct x y)
    (congrArg supportTripleKZeroToCompactSupport ha)
    (congrArg supportTripleKZeroToCompactSupport hb)

end AtiyahSinger.ComplexBundle
