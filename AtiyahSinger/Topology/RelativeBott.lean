/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BottDisk
public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.GeometricBott
public import AtiyahSinger.Topology.RelativeKZeroProduct

/-!
# Relative complex-line Bott periodicity

Public module ID: M2053.

The actual product with the disk-boundary triple d(1,1,z) induces
K(X,A) -> K(X × D, (A × D) union (X × S¹)) for compact Hausdorff closed
pairs. The multiplication is by the positive boundary coordinate z,
not its conjugate or inverse. The forward map of the resulting additive
equivalence is this specified relative external product.

The complement of the product boundary has coordinates (X minus A) ×
the open disk. Positive radial rescaling identifies it with (X minus A) × ℂ.
The product comparison then reduces bijectivity to the already constructed
geometric bottLineEquiv, without an index theorem or a forgetful-map argument.
Naturality uses arbitrary continuous maps of closed pairs. Such a map need
not preserve their open complements, and no complement pullback is assumed.

Sources: Karoubi, K-Theory, III.1.2--1.4, pp.112--113, for the specified
generator and relative periodicity; III.1.6--1.10 for the existing loop/disk
and geometric Bott comparisons. Compact parameter pairs are instances of
these same relative groups and maps, with the original factor order retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] complexUnitClosedDisc_compactSpace complexUnitClosedDisc_t2Space
  trivialTopology isFiniteRank_trivial

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

/-- Relative Bott multiplication is external product with the specified disk-boundary class. -/
def relativeBottProduct (A : Set X) (hA : IsClosed A) :
    RelativeKZero A hA →+
      RelativeKZero (relativeProductSubset A complexDiskBoundary)
        (isClosed_relativeProductSubset A hA complexDiskBoundary isClosed_complexDiskBoundary) :=
  (relativeKZeroExternalProduct A hA complexDiskBoundary isClosed_complexDiskBoundary).flip
    bottDiskClass

/-- The target relative group in original complement coordinates and positive radial coordinates. -/
def relativeBottComplementEquiv (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    RelativeKZero (relativeProductSubset A complexDiskBoundary)
        (isClosed_relativeProductSubset A hA complexDiskBoundary isClosed_complexDiskBoundary) ≃+
      CompactSupportKZero ((Aᶜ : Set X) × ℂ) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  letI := (isClosed_relativeProductSubset A hA complexDiskBoundary
    isClosed_complexDiskBoundary).isOpen_compl.locallyCompactSpace
  (relativeKZeroCompactSupportEquiv (relativeProductSubset A complexDiskBoundary)
    (isClosed_relativeProductSubset A hA complexDiskBoundary
      isClosed_complexDiskBoundary)).trans
    (compactSupportKZeroHomeomorphEquiv
      ((relativeProductComplementHomeomorph A complexDiskBoundary).trans
        ((Homeomorph.refl (Aᶜ : Set X)).prodCongr complexDiskInteriorHomeomorph)))

/-- Complement comparison sends this same relative product to the original line Bott product. -/
theorem relativeBottProduct_complement (A : Set X) (hA : IsClosed A)
    (a : RelativeKZero A hA) :
    letI := hA.isOpen_compl.locallyCompactSpace
    relativeBottComplementEquiv A hA (relativeBottProduct A hA a) =
      bottLineExternalProduct (relativeKZeroCompactSupportEquiv A hA a) := by
  /- Stage 1: apply relativeKZeroExternalProduct_complement to a and
  bottDiskClass. It computes the actual relative external product through
  the original complement coordinates, as the product of the two actual
  compact-support classes. Stage 2: naturality of compact-support external
  product under the identity and the radial homeomorphism transports the
  second factor. bottDiskClass_toCompactSupport identifies that factor
  with bottLineClass. The first factor is the unchanged complement class
  of a, giving exactly the existing bottLineExternalProduct. -/
  let := hA.isOpen_compl.locallyCompactSpace
  let := isClosed_complexDiskBoundary.isOpen_compl.locallyCompactSpace
  let := (isClosed_relativeProductSubset A hA complexDiskBoundary
    isClosed_complexDiskBoundary).isOpen_compl.locallyCompactSpace
  let e := relativeProductComplementHomeomorph A complexDiskBoundary
  let f := (Homeomorph.refl (Aᶜ : Set X)).prodCongr complexDiskInteriorHomeomorph
  -- Factor the original target coordinates using proper pullback composition.
  have hcomp (u : CompactSupportKZero
      ((relativeProductSubset A complexDiskBoundary)ᶜ : Set (X × Complex.UnitClosedDisc))) :
      compactSupportKZeroHomeomorph (e.trans f) u =
        compactSupportKZeroHomeomorph f (compactSupportKZeroHomeomorph e u) := by
    change compactSupportKZeroPullback
      ⟨(e.trans f).symm, (e.trans f).symm.continuous⟩ (e.trans f).symm.isProperMap u =
        compactSupportKZeroPullback ⟨f.symm, f.symm.continuous⟩ f.symm.isProperMap
          (compactSupportKZeroPullback ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap u)
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  change compactSupportKZeroHomeomorph (e.trans f)
    (relativeKZeroCompactSupportEquiv (relativeProductSubset A complexDiskBoundary)
      (isClosed_relativeProductSubset A hA complexDiskBoundary isClosed_complexDiskBoundary)
      (relativeKZeroExternalProduct A hA complexDiskBoundary isClosed_complexDiskBoundary
        a bottDiskClass)) = _
  rw [hcomp]
  have hrel := relativeKZeroExternalProduct_complement A hA complexDiskBoundary
    isClosed_complexDiskBoundary a bottDiskClass
  change compactSupportKZeroHomeomorph e
    (relativeKZeroCompactSupportEquiv (relativeProductSubset A complexDiskBoundary)
      (isClosed_relativeProductSubset A hA complexDiskBoundary isClosed_complexDiskBoundary)
      (relativeKZeroExternalProduct A hA complexDiskBoundary isClosed_complexDiskBoundary
        a bottDiskClass)) = _ at hrel
  rw [hrel]
  -- Naturality transports precisely the original positive disk generator.
  rw [compactSupportKZeroExternalProduct_homeomorph
    (Homeomorph.refl (Aᶜ : Set X)) complexDiskInteriorHomeomorph]
  have hid (u : CompactSupportKZero (Aᶜ : Set X)) :
      compactSupportKZeroHomeomorph (Homeomorph.refl (Aᶜ : Set X)) u = u := by
    change compactSupportKZeroPullback (ContinuousMap.id (Aᶜ : Set X)) isProperMap_id u = u
    rw [compactSupportKZeroPullback_id]
    rfl
  rw [hid]
  change compactSupportKZeroExternalProduct (relativeKZeroCompactSupportEquiv A hA a)
    (compactSupportKZeroHomeomorphEquiv complexDiskInteriorHomeomorph
      (relativeKZeroCompactSupportEquiv complexDiskBoundary isClosed_complexDiskBoundary
        bottDiskClass)) = bottLineExternalProduct (relativeKZeroCompactSupportEquiv A hA a)
  rw [bottDiskClass_toCompactSupport]
  rfl

/-- Relative Bott periodicity for the specified product on every compact Hausdorff closed pair. -/
theorem relativeBottProduct_bijective (A : Set X) (hA : IsClosed A) :
    Function.Bijective (relativeBottProduct A hA) := by
  /- The open complement Aᶜ is locally compact Hausdorff. The preceding
  commuting identity conjugates relativeBottProduct by the two specified
  relative/complement equivalences to bottLineExternalProduct on Aᶜ.
  That map is bijective by the already constructed bottLineEquiv.
  Transport injectivity and surjectivity through these equivalences.
  This includes empty A, A=X, empty X and disconnected spaces, with no
  CW, basepoint cofibration, relative-forgetful injectivity or index theorem. -/
  let := hA.isOpen_compl.locallyCompactSpace
  let e := relativeBottComplementEquiv A hA
  let f := relativeKZeroCompactSupportEquiv A hA
  have hB := bottLineExternalProduct_bijective (Aᶜ : Set X)
  constructor
  · -- The given complement square detects equality by its two original equivalences.
    intro a b hab
    apply f.injective
    apply hB.injective
    have h := congrArg e hab
    rw [relativeBottProduct_complement, relativeBottProduct_complement] at h
    exact h
  · intro b
    obtain ⟨a, ha⟩ := hB.surjective (e b)
    refine ⟨f.symm a, e.injective ?_⟩
    rw [relativeBottProduct_complement]
    change bottLineExternalProduct (f (f.symm a)) = e b
    rw [f.apply_symm_apply]
    exact ha

/-- The relative Bott equivalence whose forward map is the actual specified external product. -/
def relativeBottEquiv (A : Set X) (hA : IsClosed A) :
    RelativeKZero A hA ≃+
      RelativeKZero (relativeProductSubset A complexDiskBoundary)
        (isClosed_relativeProductSubset A hA complexDiskBoundary isClosed_complexDiskBoundary) :=
  AddEquiv.ofBijective (relativeBottProduct A hA) (relativeBottProduct_bijective A hA)

/-- Relative Bott multiplication is natural for arbitrary continuous maps of closed pairs. -/
theorem relativeBottProduct_natural (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (b : RelativeKZero B hB) :
    relativeKZeroPullback
      (relativeProductSubset A complexDiskBoundary)
      (isClosed_relativeProductSubset A hA complexDiskBoundary isClosed_complexDiskBoundary)
      (relativeProductSubset B complexDiskBoundary)
      (isClosed_relativeProductSubset B hB complexDiskBoundary isClosed_complexDiskBoundary)
      (f.prodMap (ContinuousMap.id Complex.UnitClosedDisc))
      (by
        intro z hz
        exact hz.elim (fun h ↦ Or.inl (hf h)) (fun h ↦ Or.inr h))
      (relativeBottProduct B hB b) =
        relativeBottProduct A hA (relativeKZeroPullback A hA B hB f hf b) := by
  /- Apply relative external-product naturality to the original pair map
  f and the identity map of the disk pair. Pullback of bottDiskClass by
  that identity is itself. This gives the displayed formula in the actual
  relative quotient groups with the same f and boundary generator.
  No map Aᶜ -> Bᶜ is required: f may send points outside A into B.
  The proof uses pointed-quotient naturality, rather than injectivity of
  a forgetful map or an unjustified proper pullback of open complements. -/
  -- Specialize the original product formula to the identity on the disk pair.
  have h := relativeKZeroExternalProduct_natural A hA
    complexDiskBoundary isClosed_complexDiskBoundary B hB
    complexDiskBoundary isClosed_complexDiskBoundary f
    (ContinuousMap.id Complex.UnitClosedDisc) hf (fun _ h ↦ h) b bottDiskClass
  have hid := DFunLike.congr_fun
    (relativeKZeroPullback_id complexDiskBoundary isClosed_complexDiskBoundary) bottDiskClass
  simpa only [relativeBottProduct, AddMonoidHom.flip_apply, hid, AddMonoidHom.id_apply] using h

end AtiyahSinger
