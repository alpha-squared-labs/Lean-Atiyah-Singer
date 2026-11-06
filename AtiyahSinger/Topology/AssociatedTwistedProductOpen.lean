/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedOpenExtension
public import AtiyahSinger.Topology.AssociatedTwistedProduct
public import AtiyahSinger.Topology.CompactSupportOpenBaseChange

/-!
# Open naturality of the original associated twisted product

Public module ID: M1558.

The original proper paired map forms a cartesian square with an equivariant
open embedding of the fiber. Associated descent and external multiplication
commute with that open extension, and proper/open base change gives the same
law after restriction to the principal pullback. The coefficient base remains
arbitrary LCH and its map to the compact principal base need not be proper.

This is the open naturality of SG III.13 (13.16), needed when the exterior
normal fiber is extended into the original associated sphere cotangent space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle Topology

private theorem associatedBundleMap_mk_mem_range_iff
    {G P Y Z : Type*} [Group G] [TopologicalSpace P] [MulAction Gᵐᵒᵖ P]
    [TopologicalSpace Y] [MulAction G Y] [TopologicalSpace Z] [MulAction G Z]
    (j : C(Y, Z)) (heq : ∀ (g : G) (y : Y), j (g • y) = g • j y)
    (p : P) (z : Z) :
    associatedBundleMk G P Z p z ∈ Set.range (associatedBundleMap (P := P) j heq) ↔
      z ∈ Set.range j := by
  constructor
  · rintro ⟨w, hw⟩
    induction w using Quotient.inductionOn with
    | h a =>
      obtain ⟨g, hg⟩ := Quotient.exact hw
      exact ⟨g⁻¹ • a.2, (heq g⁻¹ a.2).trans (congrArg Prod.snd hg).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨associatedBundleMk G P Y p y, rfl⟩

variable {G P B X Y Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]
  [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [hP : IsPrincipalBundle G projection] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
  [LocallyCompactSpace Z] [T2Space Z]

set_option maxHeartbeats 800000 in
-- Retain both original principal pullbacks and the same product-square witnesses.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original twisted product commutes with open extension of its equivariant fiber factor. -/
theorem associatedSupportTwistedProduct_openPushforward
    (p : C(X, B)) (j : C(Y, Z)) (heq : ∀ (g : G) (y : Y), j (g • y) = g • j y)
    (hj : IsOpenEmbedding j) (a : CompactSupportKZero X)
    (b : EquivariantSupportTripleKZero G Y) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Z) hP
    letI := associatedBundle_locallyCompactSpace (Y := Z) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) p)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) p)
    letI := associatedBundle_t2Space (Y := Z)
      (isPrincipalBundle_pullback (G := G) (projection := projection) p)
    letI := associatedBundle_locallyCompactSpace (Y := Z)
      (isPrincipalBundle_pullback (G := G) (projection := projection) p)
    associatedSupportTwistedProduct (G := G) (Y := Z) p a
      (equivariantSupportTripleKZeroOpenPushforward j hj heq b) =
      compactSupportKZeroOpenPushforward
        (associatedBundleMap (P := PrincipalBundlePullback p projection) j heq)
        (isOpenEmbedding_associatedBundleMap j heq hj)
        (associatedSupportTwistedProduct (G := G) (Y := Y) p a b) := by
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := Z) hP
  let := associatedBundle_locallyCompactSpace (Y := Z) hP
  let := associatedBundle_t2Space (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) p)
  let := associatedBundle_locallyCompactSpace (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) p)
  let := associatedBundle_t2Space (Y := Z)
    (isPrincipalBundle_pullback (G := G) (projection := projection) p)
  let := associatedBundle_locallyCompactSpace (Y := Z)
    (isPrincipalBundle_pullback (G := G) (projection := projection) p)
  let AY := AssociatedBundle G P Y
  let AZ := AssociatedBundle G P Z
  let QY := AssociatedBundle G (PrincipalBundlePullback p projection) Y
  let QZ := AssociatedBundle G (PrincipalBundlePullback p projection) Z
  let jB := associatedBundleMap (P := P) j heq
  let jP := associatedBundleMap (P := PrincipalBundlePullback p projection) j heq
  have hjB : IsOpenEmbedding jB := isOpenEmbedding_associatedBundleMap j heq hj
  have hjP : IsOpenEmbedding jP := isOpenEmbedding_associatedBundleMap j heq hj
  let jX : X × AY → X × AZ := Prod.map id jB
  have hjX : IsOpenEmbedding jX := IsOpenEmbedding.id.prodMap hjB
  let pY : C(QY, X × AY) := associatedBundlePullbackProdMap (G := G) (Y := Y) p
  let pZ : C(QZ, X × AZ) := associatedBundlePullbackProdMap (G := G) (Y := Z) p
  have hpY : IsProperMap pY := (associatedBundlePullbackProdMap_isClosedEmbedding p).isProperMap
  have hpZ : IsProperMap pZ := (associatedBundlePullbackProdMap_isClosedEmbedding p).isProperMap
  have hsquare (w : QY) : pZ (jP w) = jX (pY w) := by
    induction w using Quotient.inductionOn with
    | h w => rfl
  -- The same fiber coordinate lies in the open image on both original paired spaces.
  have himage (w : QZ) : pZ w ∈ Set.range jX ↔ w ∈ Set.range jP := by
    induction w using Quotient.inductionOn with
    | h w =>
      have hleft : pZ (associatedBundleMk G (PrincipalBundlePullback p projection) Z w.1 w.2)
          ∈ Set.range jX ↔ associatedBundleMk G P Z w.1.val.2 w.2 ∈ Set.range jB := by
        constructor
        · rintro ⟨z, hz⟩
          exact ⟨z.2, congrArg Prod.snd hz⟩
        · rintro ⟨z, hz⟩
          exact ⟨(w.1.val.1, z), Prod.ext rfl hz⟩
      exact hleft.trans ((associatedBundleMap_mk_mem_range_iff j heq w.1.val.2 w.2).trans
        (associatedBundleMap_mk_mem_range_iff j heq w.1 w.2).symm)
  have hbaseChange := DFunLike.congr_fun
    (compactSupportKZeroPullback_openPushforward_square jX hjX jP hjP pZ hpZ pY hpY
      hsquare himage) (compactSupportKZeroExternalProduct a (associatedSupportKZero hP b))
  have hdesc := associatedSupportKZero_openPushforward hP j heq hj b
  have hprod := compactSupportKZeroExternalProduct_openPushforward id IsOpenEmbedding.id
    jB hjB a (associatedSupportKZero hP b)
  rw [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at hprod
  change compactSupportKZeroPullback pZ hpZ
    (compactSupportKZeroExternalProduct a
      (associatedSupportKZero hP (equivariantSupportTripleKZeroOpenPushforward j hj heq b))) =
    compactSupportKZeroOpenPushforward jP hjP
      (compactSupportKZeroPullback pY hpY
        (compactSupportKZeroExternalProduct a (associatedSupportKZero hP b)))
  rw [hdesc, ← hprod]
  exact hbaseChange

end AtiyahSinger
