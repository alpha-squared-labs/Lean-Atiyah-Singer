/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The actual comparison from compact supports to the one-point relative pair

Public module ID: M1964.

For each compact support K in a locally compact Hausdorff space X, the
original inclusion X -> OnePoint X gives an excision isomorphism of the
original relative singular cohomology groups. Its inverse, followed by
restriction of the relative condition to infinity, is compatible with
enlarging K. Descent through the original compact-support colimit gives
the comparison to H^n(OnePoint X,{infinity};R).

Sources: Hatcher, Algebraic Topology, sections 2.1, 3.1 and 3.3, for
singular excision, its cohomological form and the compact-support colimit.
The displayed combination with the actual one-point compactification is
a supplementary construction. No change of cohomology theory occurs.

There is deliberately no general isomorphism assertion. For an infinite
discrete space, degree-zero compactly supported singular cohomology is a
direct sum, whereas the relative degree-zero group of its one-point
compactification permits arbitrary values on the finite points. Additional
control near infinity is needed for bijectivity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits OnePoint TopologicalSpace

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The original pair pullback across inclusion in the one-point compactification. -/
def onePointCohomologySupportPullback (K : Compacts X) (n : ℕ) :
    relativeSingularCohomology R (((↑) : X → OnePoint X) '' (K : Set X))ᶜ n ⟶
      relativeSingularCohomology R ((K : Set X)ᶜ) n :=
  relativeSingularCohomologyPullback R
    ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
    (fun x hx ↦ by
      -- The original inclusion is injective and retains exactly the same compact support.
      rintro ⟨y, hy, hyx⟩
      exact hx ((OnePoint.coe_injective hyx) ▸ hy)) n

variable [hLocal : LocallyCompactSpace X] [hHausdorff : T2Space X]

include hLocal hHausdorff in
/-- Removing infinity is excision for the complement of the same compact support. -/
theorem isIso_onePointCohomologySupportPullback (K : Compacts X) (n : ℕ) :
    IsIso (onePointCohomologySupportPullback R X K n) := by
  /- Stage 1: the image of K is compact in the Hausdorff one-point
  compactification, hence closed, and it does not contain infinity.
  Its complement is an open neighborhood of infinity. The closed set
  {infinity} therefore has closure contained in the interior of that
  relative subspace, exactly the hypothesis of singular excision.
  Stage 2: excise that point. The actual open inclusion identifies the
  remaining pair with (X,X minus K), retaining the original topology
  and the original compact subset. The standard small-chain subdivision
  comparison and its chain homotopies give cohomological excision with
  coefficients in the same arbitrary commutative ring R. No flatness,
  tensor-cohomology identification or field hypothesis is used.
  Stage 3: the induced cohomology morphism is precisely the displayed
  original relative pullback, so this proves its IsIso certificate. -/
  -- Apply open excision to the original inclusion, retaining exactly its image of K.
  exact isIso_openEmbeddingCohomologySupportPullback R
    ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩ OnePoint.isOpenEmbedding_coe K n

/-- A compact-support representative extended across infinity and restricted to that point. -/
def onePointCohomologySupportMap (K : Compacts X) (n : ℕ) :
    relativeSingularCohomology R ((K : Set X)ᶜ) n ⟶
      relativeSingularCohomology R ({∞} : Set (OnePoint X)) n := by
  letI := isIso_onePointCohomologySupportPullback R X K n
  exact (asIso (onePointCohomologySupportPullback R X K n)).inv ≫
    relativeSingularCohomologyRestriction R {∞}
      (((↑) : X → OnePoint X) '' (K : Set X))ᶜ (by
        intro z hz
        have hz' : z = ∞ := hz
        subst z
        exact OnePoint.infty_notMem_image_coe) n

/-- The same excision extension is compatible with enlarging the compact support. -/
theorem onePointCohomologySupportMap_naturality
    (K L : Compacts X) (h : K ≤ L) (n : ℕ) :
    (compactSupportCohomologyFunctor R X n).map (homOfLE h) ≫
        onePointCohomologySupportMap R X L n =
      onePointCohomologySupportMap R X K n := by
  /- The original inclusions of the complements form a commuting square
  with the same inclusion X -> OnePoint X. Functoriality of the actual
  relative chain maps, dualization and homology gives the corresponding
  square for both excision pullbacks. Invert these two actual isomorphisms.
  Finally compose with restriction to the same singleton infinity;
  transitivity of relative restriction yields the displayed equality.
  No new compact support or separate choice of extension is involved. -/
  let f : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let AK : Set (OnePoint X) := (f '' (K : Set X))ᶜ
  let AL : Set (OnePoint X) := (f '' (L : Set X))ᶜ
  let hImage : AL ⊆ AK := Set.compl_subset_compl.mpr (Set.image_mono h)
  let hInfinity : ({∞} : Set (OnePoint X)) ⊆ AL := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact OnePoint.infty_notMem_image_coe
  let pK := onePointCohomologySupportPullback R X K n
  let pL := onePointCohomologySupportPullback R X L n
  let rX := (compactSupportCohomologyFunctor R X n).map (homOfLE h)
  let rY := relativeSingularCohomologyRestriction R AL AK hImage n
  let hK : IsIso pK := isIso_onePointCohomologySupportPullback R X K n
  let hL : IsIso pL := isIso_onePointCohomologySupportPullback R X L n
  -- The square retains the same finite-point inclusion and original supports.
  have hsquare : rY ≫ pL = pK ≫ rX :=
    relativeSingularCohomologyPullback_restriction R f
      (Set.compl_subset_compl.mpr h) hImage _ _ n
  change rX ≫ ((asIso pL).inv ≫ relativeSingularCohomologyRestriction R {∞} AL _ n) =
    (asIso pK).inv ≫ relativeSingularCohomologyRestriction R {∞} AK _ n
  apply (cancel_epi pK).mp
  erw [← Category.assoc pK rX, ← hsquare, Category.assoc rY pL,
    (asIso pL).hom_inv_id_assoc, (asIso pK).hom_inv_id_assoc]
  -- Restricting twice is restriction to that same singleton infinity.
  let H := relativeSingularCohomologyFunctor R (OnePoint X) n
  change H.map (homOfLE hImage).op ≫ H.map (homOfLE hInfinity).op =
    H.map (homOfLE (hInfinity.trans hImage)).op
  rw [← H.map_comp]
  rfl

/-- The original compact-support colimit comparison with the one-point relative group. -/
def compactSupportCohomologyToOnePoint (n : ℕ) :
    compactSupportCohomology R X n ⟶
      relativeSingularCohomology R ({∞} : Set (OnePoint X)) n :=
  colimit.desc (compactSupportCohomologyFunctor R X n)
    { pt := relativeSingularCohomology R ({∞} : Set (OnePoint X)) n
      ι :=
        { app := fun K ↦ onePointCohomologySupportMap R X K n
          naturality := by
            intro K L f
            change (compactSupportCohomologyFunctor R X n).map f ≫
                onePointCohomologySupportMap R X L n =
              onePointCohomologySupportMap R X K n ≫ 𝟙 _
            rw [Category.comp_id]
            have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
            simpa only [hf] using
              onePointCohomologySupportMap_naturality R X K L (leOfHom f) n } }

/-- Every original representative has precisely its original excision extension as image. -/
theorem compactSupportCohomologyToOnePoint_representative
    (K : Compacts X) (n : ℕ) (a : relativeSingularCohomology R ((K : Set X)ᶜ) n) :
    compactSupportCohomologyToOnePoint R X n (compactSupportCohomologyClass R X K n a) =
      onePointCohomologySupportMap R X K n a := by
  /- Evaluate the defining colimit descent on its K-th original cocone
  leg. Its value is the inverse of the original excision pullback,
  followed by the same restriction to infinity used in that leg. -/
  have h : compactSupportCohomologyClass R X K n ≫
      compactSupportCohomologyToOnePoint R X n =
      onePointCohomologySupportMap R X K n := colimit.ι_desc _ K
  exact congrArg (fun k ↦ k a) h

/-- Restricting the comparison's ordinary class to X is the original forget-support map. -/
theorem compactSupportCohomologyToOnePoint_toOrdinary
    (n : ℕ) (a : compactSupportCohomology R X n) :
    singularCohomologyPullback R
        ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩ n
        (relativeSingularCohomologyToOrdinary R ({∞} : Set (OnePoint X)) n
          (compactSupportCohomologyToOnePoint R X n a)) =
      compactSupportCohomologyToOrdinary R X n a := by
  /- Stage 1: represent a on one original compact subset K. The
  comparison is its original excision inverse followed by restriction
  to infinity. Forgetting the relative condition and pulling back along
  the same inclusion commute with that restriction.
  Stage 2: cancel the actual excision inverse against its original pair
  pullback. The result is the original relative-to-ordinary image of
  the K-supported representative, which is exactly the compact-support
  forgetful map by its defining colimit cocone. -/
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R X n a
  rw [compactSupportCohomologyToOnePoint_representative]
  let f : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let A : Set (OnePoint X) := (f '' (K : Set X))ᶜ
  let hInfinity : ({∞} : Set (OnePoint X)) ⊆ A := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact OnePoint.infty_notMem_image_coe
  let pK := onePointCohomologySupportPullback R X K n
  let hK : IsIso pK := isIso_onePointCohomologySupportPullback R X K n
  -- Forgetting the relative condition commutes with restriction to infinity.
  have hrestrict : relativeSingularCohomologyRestriction R {∞} A hInfinity n ≫
      relativeSingularCohomologyToOrdinary R {∞} n =
      relativeSingularCohomologyToOrdinary R A n := by
    have h := (relativeSingularCohomologyToOrdinaryNatTrans R (OnePoint X) n).naturality
      (homOfLE hInfinity).op
    change relativeSingularCohomologyRestriction R {∞} A hInfinity n ≫
        relativeSingularCohomologyToOrdinary R {∞} n =
      relativeSingularCohomologyToOrdinary R A n ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h
  have hpull : pK ≫ relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) n =
      relativeSingularCohomologyToOrdinary R A n ≫ singularCohomologyPullback R f n :=
    relativeSingularCohomologyPullback_toOrdinary R f _ n
  have hmap : onePointCohomologySupportMap R X K n ≫
        relativeSingularCohomologyToOrdinary R {∞} n ≫
        singularCohomologyPullback R f n =
      relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) n := by
    change ((asIso pK).inv ≫ _) ≫ _ ≫ _ = _
    erw [Category.assoc (asIso pK).inv,
      ← Category.assoc (relativeSingularCohomologyRestriction R {∞} A hInfinity n),
      hrestrict, ← hpull, (asIso pK).inv_hom_id_assoc]
  -- Evaluate this equality on b, and the ordinary colimit cocone on the same b.
  have hclass : compactSupportCohomologyClass R X K n ≫
      compactSupportCohomologyToOrdinary R X n =
      relativeSingularCohomologyToOrdinary R ((K : Set X)ᶜ) n := colimit.ι_desc _ K
  exact (congrArg (fun k ↦ k b) hmap).trans (congrArg (fun k ↦ k b) hclass).symm

end AtiyahSinger
