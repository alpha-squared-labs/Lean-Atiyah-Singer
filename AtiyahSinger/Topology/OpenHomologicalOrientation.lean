/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HomologicalOrientation
public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import Mathlib.Topology.Separation.Regular

/-!
# Restriction of a homological orientation along an open embedding

Public module ID: M1974.

The actual map of punctured pairs induces a local-homology equivalence.
Transporting the target's prescribed integral generator through its inverse
constructs the restricted orientation. Local compatibility follows from
the same excision maps; no global fundamental class, duality identity, or
integration comparison is included as an assumption.

Source: Hatcher, Algebraic Topology, section 3.3, local-homology definition
of orientation and restriction to open submanifolds; section 2.1, excision.
The open-embedding presentation is the standard form that also handles an
open subset via its original inclusion. Disconnected spaces, the empty
space, and signed zero-dimensional orientations are retained.
The neighborhood representative construction assumes a regular ambient
space; Hausdorff Euclidean manifolds satisfy this condition automatically.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Excision makes the actual open embedding bijective on the original local homology. -/
theorem relativeSingularHomologyMap_openEmbedding_bijective [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (x : X) (n : ℕ) :
    Function.Bijective (relativeSingularHomologyMap ℤ f
      (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
      (fun _y hy h ↦ hy (hf.injective h)) n) := by
  /- Stage 1: factor the given embedding as its homeomorphism onto its
  actual open image followed by the subtype inclusion. The singleton
  {f(x)} is closed in Y and belongs to that image.
  Stage 2: the homeomorphism induces an equivalence of punctured pairs;
  excision makes the open-image inclusion a local-homology equivalence.
  Relative functoriality identifies their composite with the exact map
  displayed here. This works in degree zero and for every positive degree. -/
  let e := hf.isEmbedding.toHomeomorph
  let i : C(Set.range f, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have he := relativeSingularHomologyMap_homeomorph_bijective e x n
  have hi := relativeSingularHomologyMap_openInclusion_bijective
    (Set.range f) hf.isOpen_range (e x) n
  -- Functoriality identifies these specific pair maps with the given f.
  have hcomp : relativeSingularHomologyMap ℤ f
      (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
      (fun _y hy h ↦ hy (hf.injective h)) n =
      relativeSingularHomologyMap ℤ (⟨e, e.continuous⟩ : C(X, Set.range f))
        (A := ({x}ᶜ : Set X)) (B := ({e x}ᶜ : Set (Set.range f)))
        (fun y hy h ↦ hy (e.injective h)) n ≫
      relativeSingularHomologyMap ℤ i
        (A := ({e x}ᶜ : Set (Set.range f))) (B := ({f x}ᶜ : Set Y))
        (fun y hy h ↦ hy (Subtype.ext h)) n := by
    change HomologicalComplex.homologyMap
      (relativeSingularChainsMap ℤ (i.comp ⟨e, e.continuous⟩)
        ((show Set.MapsTo i ({e x}ᶜ) ({f x}ᶜ) from
          fun y hy h ↦ hy (Subtype.ext h)).comp
          (show Set.MapsTo e ({x}ᶜ) ({e x}ᶜ) from
            fun y hy h ↦ hy (e.injective h)))) n = _
    rw [relativeSingularChainsMap_comp ℤ ⟨e, e.continuous⟩ i
      (show Set.MapsTo e ({x}ᶜ) ({e x}ᶜ) from fun y hy h ↦ hy (e.injective h))
      (show Set.MapsTo i ({e x}ᶜ) ({f x}ᶜ) from fun y hy h ↦ hy (Subtype.ext h)),
      HomologicalComplex.homologyMap_comp]
    rfl
  rw [hcomp]
  exact hi.comp he

/-- Local-homology equivalence whose forward map is the specified open embedding. -/
def localHomologyOpenEmbeddingEquiv [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (x : X) (n : ℕ) :
    relativeSingularHomology ℤ ({x}ᶜ : Set X) n ≃ₗ[ℤ]
      relativeSingularHomology ℤ ({f x}ᶜ : Set Y) n :=
  LinearEquiv.ofBijective
    (relativeSingularHomologyMap ℤ f
      (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
      (fun _y hy h ↦ hy (hf.injective h)) n).hom
    (relativeSingularHomologyMap_openEmbedding_bijective f hf x n)

/-- Restricting the specified integral local generators preserves their local compatibility. -/
theorem homologicalOrientationOpenPullback_locally_compatible [T2Space Y] [RegularSpace Y]
    {n : ℕ} (O : HomologicalOrientation n Y) (f : C(X, Y)) (hf : IsOpenEmbedding f) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ c : relativeSingularHomology ℤ Uᶜ n, ∀ (y : X) (hy : y ∈ U),
        relativeSingularHomologyInclusion ℤ Uᶜ ({y}ᶜ)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n c =
            ((O.localGenerator (f y)).trans
              (localHomologyOpenEmbeddingEquiv f hf y n).symm) 1 := by
  /- Stage 1: choose a neighborhood carrying the target orientation class at
  f(x). Regularity gives a closed neighborhood K inside both that neighborhood
  and the open image of f, and an open V contained in K that contains f(x).
  Stage 2: restrict the original class to H_n(Y,Y minus K). Open excision for
  this same K lifts it through f. Restrict the lift to the complement of
  f-inverse-image(V), producing a common local class on the source.
  Stage 3: the actual relative inclusion squares identify its local values
  with the inverse images of the prescribed target generators. Their signs
  and integral normalization are therefore retained. -/
  intro x
  obtain ⟨U, hU, hxU, c, hc⟩ := O.locally_compatible (f x)
  -- Regularity provides a closed neighborhood inside both the chosen orientation
  -- neighborhood and this very open image. Its interior need not be compact.
  obtain ⟨K, hxK, hKclosed, hKsub⟩ := exists_mem_nhds_isClosed_subset
    ((hU.inter hf.isOpen_range).mem_nhds ⟨hxU, ⟨x, rfl⟩⟩)
  obtain ⟨V, hVK, hVopen, hxV⟩ := mem_nhds_iff.mp hxK
  have hKU : K ⊆ U := fun _ h ↦ (hKsub h).1
  have hKr : K ⊆ Set.range f := fun _ h ↦ (hKsub h).2
  let W := f ⁻¹' V
  let A := (f ⁻¹' K)ᶜ
  let pK := relativeSingularHomologyMap ℤ f (A := A) (B := Kᶜ) (fun _ h ↦ h) n
  obtain ⟨e, he⟩ :=
    homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ f hf K hKclosed hKr
  have hpK : IsIso pK := by
    change IsIso (HomologicalComplex.homologyMap _ n)
    erw [← he]
    change IsIso (e.toHomologyIso n).hom
    infer_instance
  obtain ⟨d, hd⟩ := ((ConcreteCategory.isIso_iff_bijective pK).mp hpK).surjective
    (relativeSingularHomologyInclusion ℤ Uᶜ Kᶜ (Set.compl_subset_compl.mpr hKU) n c)
  have hAW : A ⊆ Wᶜ := Set.compl_subset_compl.mpr (Set.preimage_mono hVK)
  let cW := relativeSingularHomologyInclusion ℤ A Wᶜ hAW n d
  refine ⟨W, hVopen.preimage f.continuous, hxV, cW, ?_⟩
  intro y hy
  have hfyK : f y ∈ K := hVK hy
  have hAy : A ⊆ ({y}ᶜ : Set X) :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hfyK)
  have hKy : Kᶜ ⊆ ({f y}ᶜ : Set Y) :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hfyK)
  have hWy : Wᶜ ⊆ ({y}ᶜ : Set X) :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)
  -- Composition of actual relative inclusions is the inclusion of the same pair.
  have hinc {Z : Type u} [TopologicalSpace Z] (A B C : Set Z)
      (hAB : A ⊆ B) (hBC : B ⊆ C) :
      relativeSingularHomologyInclusion ℤ A B hAB n ≫
          relativeSingularHomologyInclusion ℤ B C hBC n =
        relativeSingularHomologyInclusion ℤ A C (hAB.trans hBC) n := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
    erw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hsquare := relativeSingularHomologyMap_inclusion ℤ f hAy hKy
    (fun _ (h : _ ∈ A) ↦ h) (fun z hz h ↦ hz (hf.injective h)) n
  -- Excision transports the neighborhood class; naturality fixes each prescribed generator.
  have hsource : relativeSingularHomologyInclusion ℤ Wᶜ {y}ᶜ hWy n cW =
      relativeSingularHomologyInclusion ℤ A {y}ᶜ hAy n d :=
    congrArg (fun t ↦ t d) (hinc A Wᶜ {y}ᶜ hAW hWy)
  have htarget : relativeSingularHomologyInclusion ℤ Kᶜ {f y}ᶜ hKy n
      (relativeSingularHomologyInclusion ℤ Uᶜ Kᶜ (Set.compl_subset_compl.mpr hKU) n c) =
      relativeSingularHomologyInclusion ℤ Uᶜ {f y}ᶜ
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (hKU hfyK))) n c :=
    congrArg (fun t ↦ t c) (hinc Uᶜ Kᶜ {f y}ᶜ (Set.compl_subset_compl.mpr hKU) hKy)
  apply (localHomologyOpenEmbeddingEquiv f hf y n).injective
  conv_rhs => rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  calc
    _ = relativeSingularHomologyMap ℤ f
        (A := ({y}ᶜ : Set X)) (B := ({f y}ᶜ : Set Y))
        (fun z hz h ↦ hz (hf.injective h)) n
        (relativeSingularHomologyInclusion ℤ Wᶜ {y}ᶜ hWy n cW) := rfl
    _ = relativeSingularHomologyMap ℤ f
        (A := ({y}ᶜ : Set X)) (B := ({f y}ᶜ : Set Y))
        (fun z hz h ↦ hz (hf.injective h)) n
        (relativeSingularHomologyInclusion ℤ A {y}ᶜ hAy n d) := congrArg _ hsource
    _ = relativeSingularHomologyInclusion ℤ Kᶜ {f y}ᶜ hKy n (pK d) :=
      congrArg (fun t ↦ t d) hsquare
    _ = relativeSingularHomologyInclusion ℤ Kᶜ {f y}ᶜ hKy n
        (relativeSingularHomologyInclusion ℤ Uᶜ Kᶜ
          (Set.compl_subset_compl.mpr hKU) n c) := congrArg _ hd
    _ = relativeSingularHomologyInclusion ℤ Uᶜ {f y}ᶜ
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (hKU hfyK))) n c := htarget
    _ = O.localGenerator (f y) 1 := hc (f y) (hKU hfyK)

/-- The orientation transported through the inverse of the actual local open-embedding map. -/
def homologicalOrientationOpenPullback [T2Space Y] [RegularSpace Y]
    {n : ℕ} (O : HomologicalOrientation n Y) (f : C(X, Y)) (hf : IsOpenEmbedding f) :
    HomologicalOrientation n X where
  localGenerator x := (O.localGenerator (f x)).trans
    (localHomologyOpenEmbeddingEquiv f hf x n).symm
  locally_compatible := homologicalOrientationOpenPullback_locally_compatible O f hf

/-- The specified open embedding preserves exactly the chosen integral local generators. -/
def IsOrientationPreservingOpenEmbedding {n : ℕ}
    (OX : HomologicalOrientation n X) (OY : HomologicalOrientation n Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f) : Prop :=
  ∀ x : X, relativeSingularHomologyMap ℤ f
    (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
    (fun _y hy h ↦ hy (hf.injective h)) n (OX.localGenerator x 1) =
      OY.localGenerator (f x) 1

/-- The actual restricted orientation makes the same open embedding orientation preserving. -/
theorem homologicalOrientationOpenPullback_orientationPreserving [T2Space Y] [RegularSpace Y]
    {n : ℕ} (O : HomologicalOrientation n Y) (f : C(X, Y)) (hf : IsOpenEmbedding f) :
    IsOrientationPreservingOpenEmbedding (homologicalOrientationOpenPullback O f hf) O f hf := by
  /- The source generator is defined as the inverse image of the target
  generator under the exact local-homology equivalence. Its forward map
  is the displayed original relative map, so the inverse identity gives
  the prescribed integral generator, including its componentwise sign. -/
  intro x
  exact (localHomologyOpenEmbeddingEquiv f hf x n).apply_symm_apply (O.localGenerator (f x) 1)

end AtiyahSinger
