/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactDualityNaturality
public import AtiyahSinger.Topology.CompactSupportCohomologyMayerVietoris
public import AtiyahSinger.Topology.RelativeCapMayerVietorisGluing
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# The connecting square for the specified compact-support duality

Public module ID: M1636.

The fixed-support cap computation is evaluated on the same normalized fundamental
classes over a union and an intersection of compact controls. Their compatibility
and open-embedding normalization identify the overlap class. Compact shrinking
then supplies these controls for every original compact-support representative.

Source: Hatcher, Algebraic Topology, section 3.3, the cap-product gluing argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace Topology

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [SecondCountableTopology M] [RegularSpace M]

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
/-- The actual compact-support cap-duality maps intertwine the two connecting maps
with the native cap boundary sign and the same restricted orientation. -/
theorem compactPoincareDuality_mayerVietoris
    (O : HomologicalOrientation n M) (U V : Opens M) (hcover : (U : Set M) ∪ V = Set.univ)
    (p q : ℕ) (h : p + (q + 1) = n) (a : compactSupportCohomology ℚ M p) :
    singularHomologyMayerVietorisBoundary ℚ U V U.isOpen V.isOpen hcover q
      (compactPoincareDuality O p (q + 1) h a) =
    (-1 : ℚ) ^ (p + 1) • compactPoincareDuality
      (homologicalOrientationOpenPullback (X := ↥(U ⊓ V)) O
        (ContinuousMap.subtypeVal ((U ⊓ V) : Set M))
        (U ⊓ V).isOpen.isOpenEmbedding_subtypeVal) (p + 1) q (by omega)
      (compactSupportCohomologyMayerVietorisBoundary ℚ U V U.isOpen V.isOpen hcover p a) := by
  subst n
  let f : C(↥(U ⊓ V), M) := ⟨Subtype.val, continuous_subtype_val⟩
  let hf : IsOpenEmbedding f := (U ⊓ V).isOpen.isOpenEmbedding_subtypeVal
  let OI := homologicalOrientationOpenPullback (X := ↥(U ⊓ V)) O f hf
  have ho := homologicalOrientationOpenPullback_orientationPreserving (X := ↥(U ⊓ V)) O f hf
  -- Fix compact pieces in the two open sets and their actual intersection control.
  have hfixed (K : Compacts U) (L : Compacts V)
      (I : Compacts ↥(U ⊓ V))
      (hI : openEmbeddingCompactImage f I =
        openEmbeddingCompactImage (ContinuousMap.subtypeVal (U : Set M)) K ⊓
          openEmbeddingCompactImage (ContinuousMap.subtypeVal (V : Set M)) L)
      (b : relativeSingularCohomology ℚ
        (((openEmbeddingCompactImage (ContinuousMap.subtypeVal (U : Set M)) K : Set M)ᶜ) ∩
          ((openEmbeddingCompactImage (ContinuousMap.subtypeVal (V : Set M)) L : Set M)ᶜ)) p) :
      let A := openEmbeddingCompactImage (ContinuousMap.subtypeVal (U : Set M)) K
      let B := openEmbeddingCompactImage (ContinuousMap.subtypeVal (V : Set M)) L
      let c := compactSupportCohomologyClass ℚ M (A ⊔ B) p
        (relativeSingularCohomologyRestriction ℚ ((A ⊔ B : Compacts M) : Set M)ᶜ
          ((A : Set M)ᶜ ∩ (B : Set M)ᶜ) (Set.compl_union _ _).subset p b)
      singularHomologyMayerVietorisBoundary ℚ U V U.isOpen V.isOpen hcover q
        (compactPoincareDuality O p (q + 1) rfl c) =
      (-1 : ℚ) ^ (p + 1) • compactPoincareDuality OI (p + 1) q (by omega)
        (compactSupportCohomologyMayerVietorisBoundary ℚ U V U.isOpen V.isOpen hcover p c) := by
    let A := openEmbeddingCompactImage (ContinuousMap.subtypeVal (U : Set M)) K
    let B := openEmbeddingCompactImage (ContinuousMap.subtypeVal (V : Set M)) L
    let S : Set M := (A : Set M)ᶜ ∩ (B : Set M)ᶜ
    let T : Set M := (A : Set M)ᶜ ∪ (B : Set M)ᶜ
    let J := openEmbeddingCompactImage f I
    have hS : ((A ⊔ B : Compacts M) : Set M)ᶜ ⊆ S := (Set.compl_union _ _).subset
    have hT : (J : Set M)ᶜ ⊆ T := by
      rw [show J = A ⊓ B from hI]
      exact (Set.compl_inter _ _).subset
    have hD : (I : Set ↥(U ⊓ V))ᶜ ⊆ f ⁻¹' T := by
      intro x hx
      apply hT
      rintro ⟨y, hy, hyx⟩
      exact hx ((hf.injective hyx) ▸ hy)
    have hpair : Set.MapsTo f (I : Set ↥(U ⊓ V))ᶜ (J : Set M)ᶜ := by
      intro x hx
      rintro ⟨y, hy, hyx⟩
      exact hx ((hf.injective hyx) ▸ hy)
    let z : relativeSingularHomology ℚ S (p + (q + 1)) :=
      relativeSingularHomologyInclusion ℚ ((A ⊔ B : Compacts M) : Set M)ᶜ S
      hS (p + (q + 1)) (rationalCompactRelativeFundamentalClass O (A ⊔ B))
    let d : p + (q + 1) = (p + 1) + q :=
      (Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1)
    let zI : relativeSingularHomology ℚ (I : Set ↥(U ⊓ V))ᶜ ((p + 1) + q) :=
      (eqToIso (congrArg (relativeSingularHomology ℚ (I : Set ↥(U ⊓ V))ᶜ) d)).hom
        (rationalCompactRelativeFundamentalClass OI I)
    let w : relativeSingularHomology ℚ
        ((Subtype.val : ↥((U : Set M) ∩ (V : Set M)) → M) ⁻¹'
          ((A : Set M)ᶜ ∪ (B : Set M)ᶜ)) ((p + 1) + q) :=
      relativeSingularHomologyInclusion ℚ (I : Set ↥(U ⊓ V))ᶜ (f ⁻¹' T) hD ((p + 1) + q) zI
    have hfund := rationalCompactRelativeFundamentalClass_openEmbedding OI O f hf ho I
    have hJI : J ≤ A ⊔ B := by
      rw [show J = A ⊓ B from hI]
      exact inf_le_left.trans le_sup_left
    have hinc := rationalCompactRelativeFundamentalClass_inclusion O hJI
    have hcomp (D E F : Set M) (hDE : D ⊆ E) (hEF : E ⊆ F) (k : ℕ) :
        relativeSingularHomologyInclusion ℚ D E hDE k ≫
          relativeSingularHomologyInclusion ℚ E F hEF k =
        relativeSingularHomologyInclusion ℚ D F (hDE.trans hEF) k := by
      exact relativeSingularHomologyInclusion_comp ℚ D E F hDE hEF k
    -- Both descriptions of the overlap class have the same specified relative image.
    have hw : relativeSingularHomologyMap ℚ f (A := f ⁻¹' T) (B := T)
        (Set.mapsTo_preimage f T) ((p + 1) + q) w =
      (eqToIso (congrArg (relativeSingularHomology ℚ T) d)).hom
        (relativeSingularHomologyInclusion ℚ S T
          (Set.inter_subset_left.trans Set.subset_union_left) (p + (q + 1)) z) := by
      have hbase : relativeSingularHomologyMap ℚ f (Set.mapsTo_preimage f T)
          (p + (q + 1)) (relativeSingularHomologyInclusion ℚ
            (I : Set ↥(U ⊓ V))ᶜ (f ⁻¹' T) hD (p + (q + 1))
              (rationalCompactRelativeFundamentalClass OI I)) =
        relativeSingularHomologyInclusion ℚ S T
          (Set.inter_subset_left.trans Set.subset_union_left) (p + (q + 1)) z := by
        have hnat := congrArg (fun t ↦ t (rationalCompactRelativeFundamentalClass OI I))
          (relativeSingularHomologyMap_inclusion ℚ f hD hT hpair (Set.mapsTo_preimage f T)
            (p + (q + 1)))
        change _ = relativeSingularHomologyInclusion ℚ (J : Set M)ᶜ T hT (p + (q + 1))
          (relativeSingularHomologyMap ℚ f hpair (p + (q + 1))
            (rationalCompactRelativeFundamentalClass OI I)) at hnat
        rw [ModuleCat.comp_apply, hfund] at hnat
        rw [hnat, ← hinc]
        dsimp only [z]
        simp only [← ModuleCat.comp_apply, hcomp]
      have hdegree (k l : ℕ) (e : k = l)
          (x : relativeSingularHomology ℚ (I : Set ↥(U ⊓ V))ᶜ k) :
          relativeSingularHomologyMap ℚ f (Set.mapsTo_preimage f T) l
            (relativeSingularHomologyInclusion ℚ (I : Set ↥(U ⊓ V))ᶜ (f ⁻¹' T) hD l
              ((eqToIso (congrArg (relativeSingularHomology ℚ (I : Set ↥(U ⊓ V))ᶜ) e)).hom x)) =
          (eqToIso (congrArg (relativeSingularHomology ℚ T) e)).hom
            (relativeSingularHomologyMap ℚ f (Set.mapsTo_preimage f T) k
              (relativeSingularHomologyInclusion ℚ (I : Set ↥(U ⊓ V))ᶜ (f ⁻¹' T) hD k x)) := by
        subst l
        rfl
      exact (hdegree _ _ d (rationalCompactRelativeFundamentalClass OI I)).trans
        (congrArg (eqToIso (congrArg (relativeSingularHomology ℚ T) d)).hom hbase)
    have hAU : ((A : Set M)ᶜ)ᶜ ⊆ U := by
      simpa only [compl_compl] using
        (show (A : Set M) ⊆ U from fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property)
    have hBV : ((B : Set M)ᶜ)ᶜ ⊆ V := by
      simpa only [compl_compl] using
        (show (B : Set M) ⊆ V from fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property)
    dsimp only [f, S, T, d] at hw
    have hcap := relativeSingularCapProduct_mayerVietoris (X := M) ℚ
      (U : Set M) (V : Set M) (A : Set M)ᶜ (B : Set M)ᶜ
      U.isOpen V.isOpen A.isCompact.isClosed.isOpen_compl B.isCompact.isClosed.isOpen_compl
      hcover hAU hBV p q b z w (by exact hw)
    -- The representative formula uses the same compact image and the same excision map.
    have hδ := compactSupportCohomologyMayerVietorisBoundary_representative (X := M) ℚ
      (U : Set M) (V : Set M) U.isOpen V.isOpen hcover K L I hI p b
    dsimp only at hδ ⊢
    rw [hδ, compactPoincareDuality_representative O (A ⊔ B) p (q + 1) rfl]
    erw [compactPoincareDuality_representative OI I (p + 1) q]
    change _ = (-1 : ℚ) ^ (p + 1) • relativeSingularCapProduct ℚ (I : Set ↥(U ⊓ V))ᶜ (p + 1) q
      (openEmbeddingCohomologySupportPullback ℚ f hf I (p + 1)
        (relativeSingularCohomologyRestriction ℚ (J : Set M)ᶜ T hT (p + 1)
          (relativeSingularCohomologyMayerVietorisBoundary ℚ (A : Set M)ᶜ (B : Set M)ᶜ
            A.isCompact.isClosed.isOpen_compl B.isCompact.isClosed.isOpen_compl p b))) zI
    have hsource := relativeSingularCapProduct_inclusion ℚ
      ((A ⊔ B : Compacts M) : Set M)ᶜ S hS p (q + 1) b
      (rationalCompactRelativeFundamentalClass O (A ⊔ B))
    change compactRelativeDuality O (A ⊔ B) p (q + 1) rfl
        (relativeSingularCohomologyRestriction ℚ ((A ⊔ B : Compacts M) : Set M)ᶜ S hS p b) =
      relativeSingularCapProduct ℚ S p (q + 1) b z at hsource
    rw [hsource]
    rw [hcap]
    congr 1
    let δb := relativeSingularCohomologyMayerVietorisBoundary ℚ (A : Set M)ᶜ (B : Set M)ᶜ
      A.isCompact.isClosed.isOpen_compl B.isCompact.isClosed.isOpen_compl p b
    have hpull := congrArg (fun t ↦ t δb)
      (relativeSingularCohomologyPullback_restriction ℚ f hD hT hpair
        (Set.mapsTo_preimage f T) (p + 1))
    change relativeSingularCohomologyPullback ℚ f hpair (p + 1)
        (relativeSingularCohomologyRestriction ℚ (J : Set M)ᶜ T hT (p + 1) δb) =
      relativeSingularCohomologyRestriction ℚ (I : Set ↥(U ⊓ V))ᶜ (f ⁻¹' T) hD (p + 1)
        (relativeSingularCohomologyPullback ℚ f (Set.mapsTo_preimage f T) (p + 1) δb) at hpull
    change relativeSingularCapProduct ℚ (f ⁻¹' T) (p + 1) q
        (relativeSingularCohomologyPullback ℚ f (Set.mapsTo_preimage f T) (p + 1) δb) w =
      relativeSingularCapProduct ℚ (I : Set ↥(U ⊓ V))ᶜ (p + 1) q
        (relativeSingularCohomologyPullback ℚ f hpair (p + 1)
          (relativeSingularCohomologyRestriction ℚ (J : Set M)ᶜ T hT (p + 1) δb)) zI
    rw [hpull]
    exact (relativeSingularCapProduct_inclusion ℚ (I : Set ↥(U ⊓ V))ᶜ (f ⁻¹' T) hD
      (p + 1) q (relativeSingularCohomologyPullback ℚ f
        (Set.mapsTo_preimage f T) (p + 1) δb) zI).symm
  -- Enlarge one arbitrary compact representative to the union of compact open-set controls.
  obtain ⟨C, b, hb⟩ := compactSupportCohomology_exists_representative ℚ M p a
  obtain ⟨K, L, hC⟩ := exists_compacts_cover_of_isOpen_union_eq_univ
    (U : Set M) V U.isOpen V.isOpen hcover C
  let A := openEmbeddingCompactImage (ContinuousMap.subtypeVal (U : Set M)) K
  let B := openEmbeddingCompactImage (ContinuousMap.subtypeVal (V : Set M)) L
  have hrange : ((A ⊓ B : Compacts M) : Set M) ⊆ Set.range f := by
    rintro x ⟨⟨u, _, rfl⟩, ⟨v, _, hvu⟩⟩
    change v.val = u.val at hvu
    exact ⟨⟨u.val, u.property, hvu ▸ v.property⟩, rfl⟩
  let I : Compacts ↥(U ⊓ V) := ⟨f ⁻¹' ((A ⊓ B : Compacts M) : Set M),
    hf.isInducing.isCompact_preimage' (A ⊓ B).isCompact hrange⟩
  have hI : openEmbeddingCompactImage f I = A ⊓ B := by
    apply Compacts.ext
    exact Set.image_preimage_eq_of_subset hrange
  let c := (compactSupportCohomologyFunctor ℚ M p).map (homOfLE hC) b
  let S : Set M := (A : Set M)ᶜ ∩ (B : Set M)ᶜ
  let r := relativeSingularCohomologyRestriction ℚ ((A ⊔ B : Compacts M) : Set M)ᶜ S
    (Set.compl_union _ _).subset p
  have hsurj : Function.Surjective r := by
    have hsame : ((A ⊔ B : Compacts M) : Set M)ᶜ = S := Set.compl_union _ _
    have hbij (D E : Set M) (h : D = E) : Function.Bijective
        (relativeSingularCohomologyRestriction ℚ D E h.subset p) := by
      subst E
      change Function.Bijective ((relativeSingularCohomologyFunctor ℚ M p).map (𝟙 _))
      rw [CategoryTheory.Functor.map_id]
      exact Function.bijective_id
    exact (hbij _ _ hsame).surjective
  obtain ⟨d, hd⟩ := hsurj c
  have hc : compactSupportCohomologyClass ℚ M (A ⊔ B) p (r d) = a := by
    rw [hd]
    exact (congrArg (fun t ↦ t b)
      (colimit.w (compactSupportCohomologyFunctor ℚ M p) (homOfLE hC))).trans hb
  rw [← hc]
  exact hfixed K L I hI d

end AtiyahSinger
