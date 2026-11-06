/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantDifferentGroupProduct
public import AtiyahSinger.Topology.EquivariantOpenRestriction

/-!
# Open extension and the independent-group support product

Public module ID: M1779.

Restricting to the two group projections commutes with the actual open
extensions. Thus the existing external-product naturality also retains the
two independent group actions. This is used in the common-open sphere
comparison and in the corresponding equivariant product assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Topology

variable {G H X Y Z W : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [T2Space X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [T2Space Y] [LocallyCompactSpace Y]
  [TopologicalSpace Z] [MulAction H Z] [ContinuousSMul H Z]
  [T2Space Z] [LocallyCompactSpace Z]
  [TopologicalSpace W] [MulAction H W] [ContinuousSMul H W]
  [T2Space W] [LocallyCompactSpace W]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open extension in the two factors preserves the original independent-group product. -/
theorem equivariantSupportKZeroDifferentGroupExternalProduct_openPushforward
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (hfe : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (k : C(Z, W)) (hk : IsOpenEmbedding k)
    (hke : ∀ (h : H) (z : Z), k (h • z) = h • k z)
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero H Z) :
    letI : MulAction (G × H) X :=
      MulAction.compHom X (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) X :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) Y :=
      MulAction.compHom Y (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) Y :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) Z :=
      MulAction.compHom Z (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) Z :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI : MulAction (G × H) W :=
      MulAction.compHom W (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) W :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    equivariantSupportTripleKZeroOpenPushforward (f.prodMap k) (hf.prodMap hk)
        (fun (g : G × H) (z : X × Z) ↦ Prod.ext (hfe g.1 z.1) (hke g.2 z.2))
        (equivariantSupportKZeroDifferentGroupExternalProduct a b) =
      equivariantSupportKZeroDifferentGroupExternalProduct
        (equivariantSupportTripleKZeroOpenPushforward f hf hfe a)
        (equivariantSupportTripleKZeroOpenPushforward k hk hke b) := by
  let : MulAction (G × H) X :=
    MulAction.compHom X (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) X :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) Y :=
    MulAction.compHom Y (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) Y :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) Z :=
    MulAction.compHom Z (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) Z :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let : MulAction (G × H) W :=
    MulAction.compHom W (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) W :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  -- Use the old same-group product on the two specified projection restrictions.
  change equivariantSupportTripleKZeroOpenPushforward (f.prodMap k) (hf.prodMap hk)
    (fun (g : G × H) (z : X × Z) ↦ Prod.ext (hfe g.1 z.1) (hke g.2 z.2))
    (equivariantSupportKZeroExternalProduct
      (equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.fst G H) a)
      (equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.snd G H) b)) = _
  rw [equivariantSupportKZeroExternalProduct_openPushforward
    f hf (fun (g : G × H) x ↦ hfe g.1 x) k hk (fun (g : G × H) z ↦ hke g.2 z)]
  -- Each restricted target triple is extended through the same original map.
  change equivariantSupportKZeroExternalProduct _ _ =
    equivariantSupportKZeroExternalProduct
      (equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.fst G H)
        (equivariantSupportTripleKZeroOpenPushforward f hf hfe a))
      (equivariantSupportTripleKZeroRestrict (ContinuousMonoidHom.snd G H)
        (equivariantSupportTripleKZeroOpenPushforward k hk hke b))
  rw [equivariantSupportTripleKZeroRestrict_openPushforward,
    equivariantSupportTripleKZeroRestrict_openPushforward]

end AtiyahSinger.ComplexBundle
