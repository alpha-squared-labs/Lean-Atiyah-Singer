/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomology
public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import AtiyahSinger.Topology.RelativeSingularOpenExcision

/-!
# Open extension on the original compact-support cohomology colimit

Public module ID: M1681.

An open embedding sends a compact support to its actual compact image.
Restriction to the open image is an excision isomorphism on the corresponding
relative singular cohomology groups. Its inverse, followed by the original
colimit injection at that image, defines extension by zero. The construction
uses the specified relative pullback, rather than defining open extension by
Poincaré duality and then obtaining its duality comparison tautologically.

Sources: Hatcher, Algebraic Topology, sections 2.1, 3.1 and 3.3, for excision
and compactly supported singular cohomology; Lawson--Michelsohn, Spin Geometry,
section III.12, pp.238--240, for compact-support covariant functoriality in the
index theorem. The representative construction spells out these standard
operations on the project's original chain quotients and support colimit.

The coefficient ring is arbitrary. Only the ambient space is assumed
Hausdorff, so the actual compact image is closed and excision applies.
Neither compactness nor properness of the open embedding is required.
The original excision, support naturality, and composition statements are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] {X Y Z : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The unchanged compact support mapped into the ambient space. -/
def openEmbeddingCompactImage (f : C(X, Y)) (K : Compacts X) : Compacts Y :=
  K.map f f.continuous

/-- Restriction along the actual open embedding at its actual compact-image support. -/
def openEmbeddingCohomologySupportPullback
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (K : Compacts X) (p : ℕ) :
    relativeSingularCohomology R ((openEmbeddingCompactImage f K : Set Y)ᶜ) p ⟶
      relativeSingularCohomology R ((K : Set X)ᶜ) p :=
  relativeSingularCohomologyPullback R f
    (fun x hx ↦ by
      -- Injectivity identifies the inverse image of the compact image with K itself.
      rintro ⟨z, hz, hzx⟩
      exact hx ((hf.injective hzx) ▸ hz)) p

/-- The original compact-image restriction is the cohomological excision isomorphism. -/
theorem isIso_openEmbeddingCohomologySupportPullback [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (K : Compacts X) (p : ℕ) :
    IsIso (openEmbeddingCohomologySupportPullback R f hf K p) := by
  /- Stage 1: the compact image f(K) is closed in the Hausdorff ambient
  space. The complement of the open image f(X) is closed, disjoint from
  f(K), and therefore contained in the interior of Y minus f(K).
  Stage 2: excise that complement from (Y,Y minus f(K)). The given open
  embedding identifies the remaining pair with (X,X minus K). The small
  singular-chain comparison and its chain homotopies yield excision after
  taking cochains over any commutative ring R and then cohomology.
  Stage 3: this map is precisely the displayed original relative pullback.
  No properness, field coefficients, or cofinality of image supports is used. -/
  let L := openEmbeddingCompactImage f K
  have hL : IsClosed (L : Set Y) := L.isCompact.isClosed
  have hRange : (L : Set Y) ⊆ Set.range f := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hPre : f ⁻¹' (L : Set Y) = (K : Set X) := Set.preimage_image_eq _ hf.injective
  have hexc {A : Set X} (hA : A = (f ⁻¹' (L : Set Y))ᶜ)
      (h : Set.MapsTo f A ((L : Set Y)ᶜ)) :
      HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f h) := by
    subst A
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f hf L hL hRange
  -- Dualize a genuine homotopy equivalence, so no field or flatness hypothesis is needed.
  exact isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R _
    (hexc (congrArg Set.compl hPre.symm) _) p

/-- Excision extends a representative and places it at its actual compact-image support. -/
def openEmbeddingCompactSupportCohomologyLeg [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (K : Compacts X) (p : ℕ) :
    relativeSingularCohomology R ((K : Set X)ᶜ) p ⟶
      compactSupportCohomology R Y p := by
  letI := isIso_openEmbeddingCohomologySupportPullback R f hf K p
  exact (asIso (openEmbeddingCohomologySupportPullback R f hf K p)).inv ≫
    compactSupportCohomologyClass R Y (openEmbeddingCompactImage f K) p

/-- Excision extension commutes with enlargement of the original compact support. -/
theorem openEmbeddingCompactSupportCohomologyLeg_naturality [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (K L : Compacts X) (h : K ≤ L) (p : ℕ) :
    (compactSupportCohomologyFunctor R X p).map (homOfLE h) ≫
        openEmbeddingCompactSupportCohomologyLeg R f hf L p =
      openEmbeddingCompactSupportCohomologyLeg R f hf K p := by
  /- Stage 1: f(K) is contained in f(L). Relative pullback for the same
  map f commutes with both inclusions of complement pairs. Invert the two
  excision isomorphisms in that square.
  Stage 2: compose with the original compact-image colimit injections.
  Their cocone relation is exactly the asserted support naturality. -/
  let hImage : openEmbeddingCompactImage f K ≤ openEmbeddingCompactImage f L :=
    Set.image_mono h
  let pK := openEmbeddingCohomologySupportPullback R f hf K p
  let pL := openEmbeddingCohomologySupportPullback R f hf L p
  let rX := (compactSupportCohomologyFunctor R X p).map (homOfLE h)
  let rY := (compactSupportCohomologyFunctor R Y p).map (homOfLE hImage)
  let hK : IsIso pK := isIso_openEmbeddingCohomologySupportPullback R f hf K p
  let hL : IsIso pL := isIso_openEmbeddingCohomologySupportPullback R f hf L p
  -- Invert the square for this same f and the original two compact images.
  have hsquare : rY ≫ pL = pK ≫ rX :=
    relativeSingularCohomologyPullback_restriction R f
      (Set.compl_subset_compl.mpr h) (Set.compl_subset_compl.mpr hImage) _ _ p
  change rX ≫ ((asIso pL).inv ≫ compactSupportCohomologyClass R Y _ p) =
    (asIso pK).inv ≫ compactSupportCohomologyClass R Y _ p
  apply (cancel_epi pK).mp
  erw [← Category.assoc pK rX, ← hsquare, Category.assoc rY pL,
    (asIso pL).hom_inv_id_assoc, (asIso pK).hom_inv_id_assoc]
  exact colimit.w (compactSupportCohomologyFunctor R Y p) (homOfLE hImage)

/-- Extension by zero along an open embedding, on the original compact-support colimit. -/
def compactSupportCohomologyOpenExtension [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (p : ℕ) :
    compactSupportCohomology R X p ⟶ compactSupportCohomology R Y p :=
  colimit.desc (compactSupportCohomologyFunctor R X p)
    { pt := compactSupportCohomology R Y p
      ι :=
        { app := fun K ↦ openEmbeddingCompactSupportCohomologyLeg R f hf K p
          naturality := by
            intro K L g
            change (compactSupportCohomologyFunctor R X p).map g ≫
                openEmbeddingCompactSupportCohomologyLeg R f hf L p =
              openEmbeddingCompactSupportCohomologyLeg R f hf K p ≫ 𝟙 _
            rw [Category.comp_id]
            have hg : homOfLE (leOfHom g) = g := Subsingleton.elim _ _
            simpa only [hg] using
              openEmbeddingCompactSupportCohomologyLeg_naturality R f hf K L (leOfHom g) p } }

/-- Every supported representative retains its specified excision extension in the colimit. -/
theorem compactSupportCohomologyOpenExtension_representative [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (K : Compacts X) (p : ℕ)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) p) :
    compactSupportCohomologyOpenExtension R f hf p
        (compactSupportCohomologyClass R X K p a) =
      openEmbeddingCompactSupportCohomologyLeg R f hf K p a := by
  /- Evaluate the defining colimit descent on its K-th injection. Its
  leg is the inverse of the actual pair restriction followed by the
  original injection at f(K); no new extension witness is chosen. -/
  have h : compactSupportCohomologyClass R X K p ≫
      compactSupportCohomologyOpenExtension R f hf p =
      openEmbeddingCompactSupportCohomologyLeg R f hf K p := colimit.ι_desc _ K
  exact congrArg (fun k ↦ k a) h

/-- Open extension is covariantly functorial for the actual composite open embedding. -/
theorem compactSupportCohomologyOpenExtension_comp [T2Space Y] [T2Space Z]
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (g : C(Y, Z)) (hg : IsOpenEmbedding g) (p : ℕ) :
    compactSupportCohomologyOpenExtension R (g.comp f) (hg.comp hf) p =
      compactSupportCohomologyOpenExtension R f hf p ≫
        compactSupportCohomologyOpenExtension R g hg p := by
  /- Stage 1: represent a compactly supported class on a compact K.
  Its image supports are f(K) and g(f(K)), the latter equal to (g o f)(K).
  Functoriality of the original pair pullbacks identifies restriction
  along g o f with the composite restrictions. Inverting these specified
  excision isomorphisms gives the equality of extension representatives.
  Stage 2: descend that identity through the original support colimit.
  No comparison between arbitrary chosen isomorphisms is being asserted. -/
  apply colimit.hom_ext
  intro K
  change compactSupportCohomologyClass R X K p ≫
    compactSupportCohomologyOpenExtension R (g.comp f) (hg.comp hf) p =
    compactSupportCohomologyClass R X K p ≫
      (compactSupportCohomologyOpenExtension R f hf p ≫
        compactSupportCohomologyOpenExtension R g hg p)
  erw [← Category.assoc, colimit.ι_desc, colimit.ι_desc]
  let Kf := openEmbeddingCompactImage f K
  let Kg := openEmbeddingCompactImage g Kf
  let Kc := openEmbeddingCompactImage (g.comp f) K
  have hImage : Kc ≤ Kg := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  let hF : Set.MapsTo f ((K : Set X)ᶜ) ((Kf : Set Y)ᶜ) := fun x hx h ↦ by
    obtain ⟨y, hy, heq⟩ := h
    exact hx ((hf.injective heq) ▸ hy)
  let hG : Set.MapsTo g ((Kf : Set Y)ᶜ) ((Kg : Set Z)ᶜ) := fun y hy h ↦ by
    obtain ⟨z, hz, heq⟩ := h
    exact hy ((hg.injective heq) ▸ hz)
  let hGc : Set.MapsTo g ((Kf : Set Y)ᶜ) ((Kc : Set Z)ᶜ) := fun y hy h ↦ by
    obtain ⟨x, hx, heq⟩ := h
    exact hy ⟨x, hx, hg.injective heq⟩
  let pF := relativeSingularCohomologyPullback R f hF p
  let pG := relativeSingularCohomologyPullback R g hG p
  let pGc := relativeSingularCohomologyPullback R g hGc p
  let pC := openEmbeddingCohomologySupportPullback R (g.comp f) (hg.comp hf) K p
  let r := (compactSupportCohomologyFunctor R Z p).map (homOfLE hImage)
  have hFiso : IsIso pF := isIso_openEmbeddingCohomologySupportPullback R f hf K p
  have hGiso : IsIso pG := isIso_openEmbeddingCohomologySupportPullback R g hg Kf p
  have hCiso : IsIso pC :=
    isIso_openEmbeddingCohomologySupportPullback R (g.comp f) (hg.comp hf) K p
  have hcomp : pC = pGc ≫ pF :=
    relativeSingularCohomologyPullback_comp R f g hF hGc p
  have hsquare : r ≫ pG = pGc := by
    have h := relativeSingularCohomologyPullback_restriction R g
      (Set.Subset.refl ((Kf : Set Y)ᶜ)) (Set.compl_subset_compl.mpr hImage) hG hGc p
    have hid : relativeSingularCohomologyRestriction R ((Kf : Set Y)ᶜ)
        ((Kf : Set Y)ᶜ) (Set.Subset.refl _) p = 𝟙 _ := by
      change (relativeSingularCohomologyFunctor R Y p).map (𝟙 _) = _
      exact CategoryTheory.Functor.map_id _ _
    rw [hid, Category.comp_id] at h
    exact h
  -- Compare the actual image supports through their inclusion in the same colimit.
  -- This keeps the dependent relative subspaces and the specified inverse maps intact.
  dsimp only [openEmbeddingCompactSupportCohomologyLeg]
  erw [Category.assoc, colimit.ι_desc]
  change (asIso pC).inv ≫ compactSupportCohomologyClass R Z Kc p =
    (asIso pF).inv ≫ ((asIso pG).inv ≫ compactSupportCohomologyClass R Z Kg p)
  apply (cancel_epi pC).mp
  erw [(asIso pC).hom_inv_id_assoc, hcomp, Category.assoc,
    (asIso pF).hom_inv_id_assoc, ← hsquare, Category.assoc,
    (asIso pG).hom_inv_id_assoc]
  exact (colimit.w (compactSupportCohomologyFunctor R Z p) (homOfLE hImage)).symm

end AtiyahSinger
