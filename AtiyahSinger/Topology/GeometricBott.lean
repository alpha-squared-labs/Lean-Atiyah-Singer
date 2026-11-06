/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BottInverse
public import AtiyahSinger.Topology.BottClutchingComparison
public import AtiyahSinger.Topology.CompactSupportCompact
public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.CompactSupportSplitPair
public import AtiyahSinger.Topology.LoopClutching
public import AtiyahSinger.Topology.OpenEmbeddingKZero
public import AtiyahSinger.Topology.RelativeKZeroExcision

/-!
# Geometric complex-line Bott periodicity

Public module ID: M1861.

Karoubi III.1.2--1.10: the loop Bott equivalence for C(X,ℂ), followed by the
specified disk-triple comparison, is external product with the actual complex-line
symbol already defined in `BottLine`. The positive boundary map is z*p+(1-p).
The radial disk-to-plane map preserves its phase, fixing the sign without choosing
a hemisphere convention for a sphere generator.

The compact case passes to locally compact Hausdorff bases through their actual
one-point compactifications and a split restriction kernel. No CW or well-pointed
hypothesis is imposed. This gives the one-complex-dimensional external-product map;
general exterior powers, higher-dimensional Thom classes and the index theorem
are separate obligations. The actual line comparison and its split-pair extension are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint Topology

/-- The compact-base Bott equivalence through the actual loop and disk comparisons. -/
def compactBottEquiv (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ComplexKZero X ≃+ CompactSupportKZero (X × ℂ) :=
  ((kZeroBottLoopEquiv C(X, ℂ)).trans (stableMatrixLoopDiskRelativeEquiv X)).trans
    (complexDiskRelativeKZeroEquiv X)

/-- Karoubi III.1.10: the specified compact Bott map is the existing geometric product. -/
theorem compactBottEquiv_apply (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (a : ComplexKZero X) :
    compactBottEquiv X a =
      bottLineExternalProduct ((compactSupportKZeroCompactEquiv X).symm a) := by
  /- On each original finite-idempotent generator, kZeroBottLoop_class gives
  the specified positive loop. The imported disk comparison identifies this
  same loop with the original complex-line external product; it keeps the
  boundary multiplication by z and the phase-preserving radial coordinates.
  The finite-idempotent universal property then makes the two additive maps
  equal on every virtual class. -/
  -- The generator comparison keeps the original loop, disk boundary, and positive line class.
  let F := (compactBottEquiv X).toAddMonoidHom
  let G := bottLineExternalProduct.comp (compactSupportKZeroCompactEquiv X).symm.toAddMonoidHom
  have hgenerator (p : IdempotentMatrix C(X, ℂ)) :
      F (kZeroClass C(X, ℂ) p) = G (kZeroClass C(X, ℂ) p) := by
    change complexDiskRelativeKZeroEquiv X
      (stableMatrixLoopDiskRelativeEquiv X (kZeroBottLoop C(X, ℂ)
        (kZeroClass C(X, ℂ) p))) = _
    rw [kZeroBottLoop_class]
    exact complexDiskRelativeKZeroEquiv_bottMatrixLoop p
  -- Equality extends through the original finite-idempotent group presentation.
  have hhom : F = G :=
    (kZero_universal_property (fun p : IdempotentMatrix C(X, ℂ) ↦ G (kZeroClass C(X, ℂ) p))
      (fun p q h ↦ congrArg G (kZeroClass_eq_of_isEquivalent p q h))
      (fun p q ↦ by rw [kZeroClass_blockSum, map_add])).unique hgenerator (fun _ ↦ rfl)
  exact DFunLike.congr_fun hhom a

/-- Karoubi III.1.4, on compact bases, for the specified complex-line external product. -/
theorem bottLineExternalProduct_bijective_of_compactSpace (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] :
    Function.Bijective (bottLineExternalProduct (X := X)) := by
  /- The preceding generator comparison identifies this homomorphism with the
  composite of compactSupportKZeroCompactEquiv and compactBottEquiv. Both are
  the specified additive equivalences, so their composite is bijective. This
  establishes bijectivity of the existing external product, not an unrelated map. -/
  -- The original product is pointwise the composite of the two specified equivalences.
  let e := (compactSupportKZeroCompactEquiv X).trans (compactBottEquiv X)
  have he : (bottLineExternalProduct (X := X)) = e.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro a
    change bottLineExternalProduct a =
      compactBottEquiv X (compactSupportKZeroCompactEquiv X a)
    have h := compactBottEquiv_apply X (compactSupportKZeroCompactEquiv X a)
    simpa only [AddEquiv.symm_apply_apply] using h.symm
  rw [he]
  exact e.bijective

/-- Karoubi III.1.3 in degree zero: Bott external product for every LCH base. -/
theorem bottLineExternalProduct_bijective (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    Function.Bijective (bottLineExternalProduct (X := X)) := by
  /- Stage 1: set B=X⁺ with distinguished point infinity. Apply the compact-base
  result to B and to a point. The source reduced group is the kernel of evaluation
  at infinity, exactly the existing definition of CompactSupportKZero X.
  Stage 2: on Z=B×ℂ, the section s(w)=(infinity,w) is a closed embedding and
  hence proper; projection r(x,w)=w is proper because B is compact. Also r∘s=id.
  Extend them to the actual one-point
  compactifications. The image of s⁺ is a closed retract of Z⁺, including its
  infinity; its complement is canonically X×ℂ. Apply relative-K exactness and
  injectivity of the relative forgetful map for this retract to identify open
  extension j!:Kc(X×ℂ)→Kc(B×ℂ) with the kernel of restriction along s.
  This is a special split pair, not a claim that all open extensions are injective.
  Stage 3: verify the two product squares for these actual maps. Proper pullback
  along s commutes with product by the line class; extension along j=coe×id
  commutes with it as well. For each square compare the pointed one-point maps
  and smash-collapse maps, then use absolute product naturality and uniqueness
  of the reduced product lift. Thus the squares concern the original
  bottLineExternalProduct and the prescribed open extension, not just isomorphic
  abstract groups. On the source the corresponding open extension is the kernel
  inclusion of reduced K⁰(B) into K⁰(B), after compact-to-absolute comparison.
  Stage 4: the commuting square of compact Bott bijections restricts to a
  bijection of the two kernels. Transport through the preceding actual kernel
  identifications to obtain the asserted map on X. All spaces used are compact
  Hausdorff compactifications or their LCH open complements. No basepoint
  cofibration, local contractibility, connectedness or finite-CW assumption enters. -/
  classical
  let B := OnePoint X
  let i : X → B := OnePoint.some
  have hi : IsOpenEmbedding i := OnePoint.isOpenEmbedding_coe
  let i₂ : X × ℂ → B × ℂ := Prod.map i id
  have hi₂ : IsOpenEmbedding i₂ := hi.prodMap IsOpenEmbedding.id
  let A : Set B := (Set.range i)ᶜ
  have hA : IsClosed A := hi.isOpen_range.isClosed_compl
  let N : Set (B × ℂ) := (Set.range i₂)ᶜ
  have hN : IsClosed N := hi₂.isOpen_range.isClosed_compl
  let := hA.locallyCompactSpace
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let := hN.locallyCompactSpace
  let a₀ : A := ⟨OnePoint.infty, by rintro ⟨x, hx⟩; cases hx⟩
  have hpoint (a : A) : a.val = OnePoint.infty := by
    rcases a with ⟨a, ha⟩
    cases a using OnePoint.rec with
    | infty => rfl
    | coe x => exact (ha ⟨x, rfl⟩).elim
  -- The closed complement of the product inclusion is the same infinity fiber times the line.
  have hnot (a : A) (z : ℂ) : (a.val, z) ∈ N := by
    rintro ⟨⟨x, w⟩, h⟩
    exact a.property ⟨x, congrArg Prod.fst h⟩
  have hbase (z : N) : z.val.1 ∈ A := by
    rintro ⟨x, hx⟩
    exact z.property ⟨(x, z.val.2), Prod.ext hx rfl⟩
  let e : N ≃ₜ A × ℂ :=
    { toFun z := (⟨z.val.1, hbase z⟩, z.val.2)
      invFun z := ⟨(z.1.val, z.2), hnot z.1 z.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        (continuous_subtype_val.fst.subtype_mk hbase).prodMk continuous_subtype_val.snd
      continuous_invFun :=
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk
          (fun z ↦ hnot z.1 z.2) }
  let r : C(B, A) := ContinuousMap.const B a₀
  have hr : ∀ a : A, r a.val = a := by
    intro a
    apply Subtype.ext
    exact (hpoint a).symm
  let r₂ : C(B × ℂ, N) :=
    ⟨fun z ↦ e.symm (a₀, z.2),
      e.symm.continuous.comp (continuous_const.prodMk continuous_snd)⟩
  have hr₂ : ∀ a : N, r₂ a.val = a := by
    intro a
    apply e.injective
    change e (e.symm (a₀, a.val.2)) = e a
    rw [e.apply_symm_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact (hpoint (e a).1).symm
    · rfl
  have hproper₂ : IsProperMap r₂ :=
    isProperMap_of_comp_of_t2 r₂.continuous
      (continuous_subtype_val.snd : Continuous (fun a : N ↦ a.val.2))
      (show IsProperMap ((fun a : N ↦ a.val.2) ∘ r₂) from
        isProperMap_snd_of_compactSpace)
  let J := compactSupportKZeroOpenPushforward i hi
  let J₂ := compactSupportKZeroOpenPushforward i₂ hi₂
  have hJ : Function.Injective J :=
    compactSupportKZeroOpenPushforward_injective_of_retraction i hi r
      r.continuous.isProperMap hr
  have hJ₂ : Function.Injective J₂ :=
    compactSupportKZeroOpenPushforward_injective_of_retraction i₂ hi₂ r₂ hproper₂ hr₂
  -- Both squares use the original open embeddings and the very same line class.
  have hsquare (a : CompactSupportKZero X) :
      J₂ (bottLineExternalProduct a) = bottLineExternalProduct (J a) := by
    have h := compactSupportKZeroExternalProduct_openPushforward i hi id
      IsOpenEmbedding.id a bottLineClass
    rw [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at h
    exact h
  have hB := bottLineExternalProduct_bijective_of_compactSpace B
  have hAbij := bottLineExternalProduct_bijective_of_compactSpace A
  constructor
  · -- Compact Bott injectivity and the split extension detect equality on the original space.
    intro a b hab
    apply hJ
    apply hB.injective
    rw [← hsquare, ← hsquare, hab]
  · intro u
    obtain ⟨v, hv⟩ := hB.surjective (J₂ u)
    let incA : C(A, B) := ⟨Subtype.val, continuous_subtype_val⟩
    let incN : C(N, B × ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
    have hincA : IsProperMap incA := hA.isClosedEmbedding_subtypeVal.isProperMap
    have hincN : IsProperMap incN := hN.isClosedEmbedding_subtypeVal.isProperMap
    let k : C(A × ℂ, N) := ⟨e.symm, e.symm.continuous⟩
    -- Exactness kills restriction of this actual extended class to the infinity fiber.
    have hz : compactSupportKZeroPullback incN hincN (J₂ u) = 0 :=
      (mem_range_compactSupportKZeroOpenPushforward_iff i₂ hi₂ (J₂ u)).mp ⟨u, rfl⟩
    rw [← hv] at hz
    have hz' := congrArg (compactSupportKZeroPullback k e.symm.isProperMap) hz
    rw [map_zero, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp] at hz'
    change compactSupportKZeroPullback (incA.prodMap (ContinuousMap.id ℂ))
      (hincA.prodMap isProperMap_id) (bottLineExternalProduct v) = 0 at hz'
    have hproduct := compactSupportKZeroExternalProduct_properPullback incA hincA
      (ContinuousMap.id ℂ) isProperMap_id v bottLineClass
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
    have hrestricted : bottLineExternalProduct
        (compactSupportKZeroPullback incA hincA v) = 0 := hproduct.symm.trans hz'
    have hAv : compactSupportKZeroPullback incA hincA v = 0 := by
      apply hAbij.injective
      exact hrestricted.trans (map_zero bottLineExternalProduct).symm
    -- Source exactness supplies an original class; target injectivity verifies its actual product.
    obtain ⟨a, ha⟩ :=
      (mem_range_compactSupportKZeroOpenPushforward_iff i hi v).mpr hAv
    refine ⟨a, hJ₂ ?_⟩
    rw [hsquare, ha, hv]

/-- Complex-line periodicity with the original external product as forward map. -/
def bottLineEquiv (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] :
    CompactSupportKZero X ≃+ CompactSupportKZero (X × ℂ) :=
  AddEquiv.ofBijective bottLineExternalProduct (bottLineExternalProduct_bijective X)

/-- The plane's integer coordinate, induced by the same positive complex-line Bott map. -/
def bottLineClassEquivInt : CompactSupportKZero ℂ ≃+ ℤ :=
  (((compactSupportKZeroHomeomorphEquiv (Homeomorph.uniqueProd PUnit.{1} ℂ)).symm.trans
    (bottLineEquiv PUnit.{1}).symm).trans
      (compactSupportKZeroCompactEquiv PUnit.{1})).trans complexKZeroPointEquivInt

/-- The specified multiplication-by-z class is the positive generator of the plane group. -/
theorem bottLineClassEquivInt_bottLineClass : bottLineClassEquivInt bottLineClass = 1 := by
  /- Stage 1: the rank-one trivial bundle on a point is the positive generator
  under the existing complexKZeroPointEquivInt. Restriction from its compact
  one-point compactification gives exactly that rank-one class on the point.
  Stage 2: its external product with the actual line triple has the same boundary
  multiplication by z and the same support {0}, after the specified projection
  PUnit×ℂ→ℂ. Tensoring with the one-dimensional trivial fiber is the identity.
  Stage 3: unfold the displayed composite inverse and use the Bott equivalence
  inverse law. Its result is the original positive rank-one integer, with no
  sign inferred from an unspecified sphere homeomorphism or generator convention. -/
  -- The actual point-unit product is sent to the same line class by the stated projection.
  let e := compactSupportKZeroHomeomorphEquiv (Homeomorph.uniqueProd PUnit.{1} ℂ)
  have hline : e.symm bottLineClass = bottLineEquiv PUnit.{1} compactSupportKZeroPointOne := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (compactSupportKZeroExternalProduct_one_left bottLineClass).symm
  change complexKZeroPointEquivInt (compactSupportKZeroCompactEquiv PUnit.{1}
    ((bottLineEquiv PUnit.{1}).symm (e.symm bottLineClass))) = 1
  rw [hline, AddEquiv.symm_apply_apply]
  change complexKZeroPointEquivInt (compactSupportKZeroCompactEquiv PUnit.{1}
    ((compactSupportKZeroCompactEquiv PUnit.{1}).symm
      (kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1)))) = 1
  rw [AddEquiv.apply_symm_apply]
  -- Evaluate the original rank-one identity matrix at the unique point.
  rw [complexKZeroPointEquivInt, AddEquiv.ofBijective_apply, complexKZeroRankAt,
    AddMonoidHom.comp_apply, kZeroMap_class, kZeroRank_class]
  change (Module.finrank ℂ (Matrix.mulVecLin
    ((ContinuousMap.evalAlgHom ℂ ℂ PUnit.unit).toRingHom.mapMatrix
      (1 : Matrix (Fin 1) (Fin 1) C(PUnit.{1}, ℂ)))).range : ℤ) = 1
  rw [map_one, Matrix.mulVecLin_one, LinearMap.range_id]
  simp

end AtiyahSinger
