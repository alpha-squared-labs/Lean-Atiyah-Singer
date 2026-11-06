/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# The actual associated product as the fiber product over the principal base

Public module ID: M1528.

The original quotient of P times (X times Y) maps to the product of the two
associated quotients by retaining the same principal representative in both
coordinates. Its image consists exactly of pairs with the same base projection.
The original principal charts identify it homeomorphically with that subspace.
If the principal base is Hausdorff, this is a closed embedding and hence proper.

Sources: the associated quotient and local products of HU IV.5 and IV.7,
SG II.3 and Appendix A. The explicit product/fiber-product comparison is a
standard supplement to those constructions, needed to compare associated
support external products on the original carriers. No compactness of the
group, principal space or base, and no separation or local compactness of
X or Y, is needed. The comparison and its exact closed range are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

variable (G P X Y : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The original associated projections retain the same principal point in both coordinates. -/
def associatedBundleProdMap :
    C(AssociatedBundle G P (X × Y), AssociatedBundle G P X × AssociatedBundle G P Y) :=
  (associatedBundleMap (G := G) (P := P) (ContinuousMap.fst : C(X × Y, X))
    (fun _ _ ↦ rfl)).prodMk
      (associatedBundleMap (G := G) (P := P) (ContinuousMap.snd : C(X × Y, Y))
        (fun _ _ ↦ rfl))

variable {G P X Y} {B : Type*} [TopologicalSpace B] [T2Space B]
  {projection : P → B}

/-- The associated product is the closed fiber product of the original associated projections. -/
theorem associatedBundleProdMap_properties (hP : IsPrincipalBundle G projection) :
    IsClosedEmbedding (associatedBundleProdMap G P X Y) ∧
      Set.range (associatedBundleProdMap G P X Y) =
        {z | associatedBundleProjection (F := X) hP z.1 =
          associatedBundleProjection (F := Y) hP z.2} := by
  /- First prove injectivity: the two quotient equalities give group elements
  moving the same principal point, and principal freeness makes them equal.
  The two fiber relations then form one diagonal relation on X × Y.
  Next identify the range with the equal-base locus. For a pair of classes
  over the same base, write q = p*g and use [q,y] = [p,g*y] to obtain
  the preimage [p,(x,g*y)].
  On that locus one principal chart supplies the same local section for
  both factors. Its two associated coordinates give a continuous local
  inverse, establishing the homeomorphism onto the range.
  Finally the equal-base locus is closed because the two projections are
  continuous and B is Hausdorff. The comparison is therefore a closed embedding.
  No compactness or separation of X or Y is required. -/
  classical
  let a := associatedBundleProdMap G P X Y
  -- Stage 1: effectiveness and principal freeness make the diagonal comparison injective.
  have hinj : Function.Injective a := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | h u =>
      induction r using Quotient.inductionOn with
      | h v =>
        have hx : associatedBundleMk G P X u.1 u.2.1 =
            associatedBundleMk G P X v.1 v.2.1 := congrArg Prod.fst hqr
        have hy : associatedBundleMk G P Y u.1 u.2.2 =
            associatedBundleMk G P Y v.1 v.2.2 := congrArg Prod.snd hqr
        obtain ⟨g, hg⟩ := Quotient.exact hx
        obtain ⟨k, hk⟩ := Quotient.exact hy
        have hgp : MulOpposite.op g • u.1 = v.1 := (congrArg Prod.fst hg).symm
        have hkp : MulOpposite.op k • u.1 = v.1 := (congrArg Prod.fst hk).symm
        have hbase : projection u.1 = projection v.1 :=
          (hP.projection_smul g u.1).symm.trans (congrArg projection hgp)
        obtain ⟨g₀, _, huniq⟩ := hP.existsUnique_smul u.1 v.1 hbase
        have hgk : g = k := (huniq g hgp).trans (huniq k hkp).symm
        apply Quotient.sound
        refine ⟨g, ?_⟩
        apply Prod.ext
        · exact hgp.symm
        · apply Prod.ext
          · exact congrArg (fun z : P × X ↦ z.2) hg
          · rw [hgk]
            exact congrArg (fun z : P × Y ↦ z.2) hk
  let S : Set (AssociatedBundle G P X × AssociatedBundle G P Y) :=
    {z | associatedBundleProjection (F := X) hP z.1 =
      associatedBundleProjection (F := Y) hP z.2}
  have hrange : Set.range a = S := by
    apply Set.Subset.antisymm
    · rintro z ⟨q, rfl⟩
      induction q using Quotient.inductionOn with
      | h u => rfl
    · rintro ⟨q, r⟩ hbase
      induction q using Quotient.inductionOn with
      | h u =>
        induction r using Quotient.inductionOn with
        | h v =>
          obtain ⟨g, hg, _⟩ := hP.existsUnique_smul u.1 v.1 hbase
          refine ⟨associatedBundleMk G P (X × Y) u.1 (u.2, g • v.2), ?_⟩
          apply Prod.ext
          · rfl
          · change associatedBundleMk G P Y u.1 (g • v.2) =
              associatedBundleMk G P Y v.1 v.2
            rw [← associatedBundleMk_smul, hg]
  let m : AssociatedBundle G P (X × Y) → S :=
    fun q ↦ ⟨a q, hrange ▸ Set.mem_range_self q⟩
  have hm : Function.Bijective m := by
    refine ⟨fun q r h ↦ hinj (congrArg Subtype.val h), ?_⟩
    intro z
    have hz : z.val ∈ Set.range a := by
      rw [hrange]
      exact z.property
    obtain ⟨q, hq⟩ := hz
    exact ⟨q, Subtype.ext hq⟩
  let eComp := Equiv.ofBijective m hm
  have hinverse : Continuous eComp.symm := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    obtain ⟨e, he₀, he⟩ := hP.exists_trivialization
      (associatedBundleProjection (F := X) hP z₀.val.1)
    obtain ⟨eX, hXbase, _, hXinv⟩ := exists_associatedBundleTrivialization (F := X) hP e he
    obtain ⟨eY, hYbase, _, hYinv⟩ := exists_associatedBundleTrivialization (F := Y) hP e he
    let W : Set S := {z | associatedBundleProjection (F := X) hP z.val.1 ∈ e.baseSet}
    have hW : IsOpen W := e.open_baseSet.preimage
      ((associatedBundleProjection (F := X) hP).continuous.comp continuous_subtype_val.fst)
    have hx (z : W) : z.val.val.1 ∈ eX.source := by
      apply eX.mem_source.mpr
      rw [hXbase]
      exact z.property
    have hy (z : W) : z.val.val.2 ∈ eY.source := by
      apply eY.mem_source.mpr
      rw [hYbase, ← z.val.property]
      exact z.property
    -- Stage 2: the same original principal section combines both associated coordinates.
    let localInv (z : W) : AssociatedBundle G P (X × Y) :=
      associatedBundleMk G P (X × Y)
        (e.toOpenPartialHomeomorph.symm
          (associatedBundleProjection (F := X) hP z.val.val.1, 1))
        ((eX z.val.val.1).2, (eY z.val.val.2).2)
    have hlocal : Continuous localInv := by
      have hp : Continuous (fun z : W ↦ e.toOpenPartialHomeomorph.symm
          (associatedBundleProjection (F := X) hP z.val.val.1, 1)) :=
        e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          (((associatedBundleProjection (F := X) hP).continuous.comp
            continuous_subtype_val.subtype_val.fst).prodMk continuous_const)
          (fun z : W ↦ e.mem_target.mpr z.property)
      have hxc : Continuous (fun z : W ↦ (eX z.val.val.1).2) :=
        continuous_snd.comp (eX.toOpenPartialHomeomorph.continuousOn.comp_continuous
          continuous_subtype_val.subtype_val.fst hx)
      have hyc : Continuous (fun z : W ↦ (eY z.val.val.2).2) :=
        continuous_snd.comp (eY.toOpenPartialHomeomorph.continuousOn.comp_continuous
          continuous_subtype_val.subtype_val.snd hy)
      exact continuous_quot_mk.comp (hp.prodMk (hxc.prodMk hyc))
    have hlocalInv (z : W) : m (localInv z) = z.val := by
      apply Subtype.ext
      apply Prod.ext
      · change associatedBundleMk G P X
          (e.toOpenPartialHomeomorph.symm
            (associatedBundleProjection (F := X) hP z.val.val.1, 1))
          (eX z.val.val.1).2 = z.val.val.1
        rw [← hXinv _ _ z.property]
        exact eX.symm_apply_mk_proj (hx z)
      · change associatedBundleMk G P Y
          (e.toOpenPartialHomeomorph.symm
            (associatedBundleProjection (F := X) hP z.val.val.1, 1))
          (eY z.val.val.2).2 = z.val.val.2
        rw [← hYinv _ _ z.property, z.val.property]
        exact eY.symm_apply_mk_proj (hy z)
    have hcontOn : ContinuousOn eComp.symm W := by
      rw [continuousOn_iff_continuous_domRestrict]
      apply hlocal.congr
      intro z
      apply eComp.injective
      change m (localInv z) = eComp (eComp.symm z.val)
      rw [Equiv.apply_symm_apply]
      exact hlocalInv z
    exact hcontOn.continuousAt (hW.mem_nhds he₀)
  let comparison : AssociatedBundle G P (X × Y) ≃ₜ S :=
    { toEquiv := eComp
      continuous_toFun := a.continuous.subtype_mk _
      continuous_invFun := hinverse }
  -- Stage 3: the Hausdorff base makes precisely this equal-base range closed.
  have hclosed : IsClosed S := isClosed_eq
    ((associatedBundleProjection (F := X) hP).continuous.comp continuous_fst)
    ((associatedBundleProjection (F := Y) hP).continuous.comp continuous_snd)
  exact ⟨⟨IsEmbedding.subtypeVal.comp comparison.isEmbedding, hrange.symm ▸ hclosed⟩, hrange⟩

end AtiyahSinger
