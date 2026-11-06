/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactPoincareDualityDirectedUnion
public import AtiyahSinger.Topology.CompactSupportCohomologyMayerVietoris
public import AtiyahSinger.Topology.SingularHomologyMayerVietorisRows

/-!
# Mayer--Vietoris transfer for the original compact cap duality

Public module ID: M1647.

The two inclusion squares follow from naturality of the specified cap maps.
The connecting square is a separate signed hypothesis, and the actual exact
rows transfer bijectivity by the five lemma. Degree-zero homology is treated
by the right-exact endpoint and the already proved high-degree vanishing.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
variable [T2Space X] [RegularSpace X] [SecondCountableTopology X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual exact rows and the signed connecting square transfer cap duality across two opens. -/
theorem compactPoincareDuality_bijective_of_mayerVietoris_square
    (O : HomologicalOrientation n X) (U V : Opens X)
    (hcover : (U : Set X) ∪ (V : Set X) = Set.univ)
    (hcap : ∀ (p q : ℕ) (h : p + (q + 1) = n)
      (a : compactSupportCohomology ℚ X p),
      singularHomologyMayerVietorisBoundary ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover q
          (compactPoincareDuality O p (q + 1) h a) =
        (-1 : ℚ) ^ (p + 1) • compactPoincareDuality
          (homologicalOrientationOpenPullback (X := ↥(U ⊓ V)) O
            (ContinuousMap.subtypeVal ((U ⊓ V) : Set X))
            (U ⊓ V).isOpen.isOpenEmbedding_subtypeVal)
          (p + 1) q (by omega)
          (compactSupportCohomologyMayerVietorisBoundary
            ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover p a))
    (hU : ∀ (OU : HomologicalOrientation n U) (p q : ℕ) (h : p + q = n),
      Function.Bijective (compactPoincareDuality OU p q h))
    (hV : ∀ (OV : HomologicalOrientation n V) (p q : ℕ) (h : p + q = n),
      Function.Bijective (compactPoincareDuality OV p q h))
    (hI : ∀ (OI : HomologicalOrientation n ↥(U ⊓ V)) (p q : ℕ) (h : p + q = n),
      Function.Bijective (compactPoincareDuality OI p q h))
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  have hRows (k : ℕ) := exact_compactSupportCohomologyMayerVietoris
    ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover k
  let OU := homologicalOrientationOpenPullback (X := U) O
    (ContinuousMap.subtypeVal (U : Set X)) U.isOpen.isOpenEmbedding_subtypeVal
  let OV := homologicalOrientationOpenPullback (X := V) O
    (ContinuousMap.subtypeVal (V : Set X)) V.isOpen.isOpenEmbedding_subtypeVal
  let OI := homologicalOrientationOpenPullback (X := ↥(U ⊓ V)) O
    (ContinuousMap.subtypeVal ((U ⊓ V) : Set X))
    (U ⊓ V).isOpen.isOpenEmbedding_subtypeVal
  let dC (k : ℕ) :=
    compactSupportCohomologyMayerVietorisDifference ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen k
  let sC (k : ℕ) :=
    compactSupportCohomologyMayerVietorisSum ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen k
  let bC (k : ℕ) :=
    compactSupportCohomologyMayerVietorisBoundary
      ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover k
  let dH (k : ℕ) := singularHomologyMayerVietorisDifference ℚ (U : Set X) (V : Set X) k
  let sH (k : ℕ) := singularHomologyMayerVietorisSum ℚ (U : Set X) (V : Set X) k
  let bH (k : ℕ) :=
    singularHomologyMayerVietorisBoundary ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover k
  let pair (p q : ℕ) (h : p + q = n) :=
    (compactPoincareDuality OU p q h).hom.prodMap (compactPoincareDuality OV p q h).hom
  have hpair (p q : ℕ) (h : p + q = n) : Function.Bijective (pair p q h) :=
    (hU OU p q h).prodMap (hV OV p q h)
  let iU : C(↥(U ⊓ V), U) := ContinuousMap.inclusion Set.inter_subset_left
  let iV : C(↥(U ⊓ V), V) := ContinuousMap.inclusion Set.inter_subset_right
  have hiU : IsOpenEmbedding iU :=
    IsOpenEmbedding.inclusion Set.inter_subset_left
      ((U ⊓ V).isOpen.preimage continuous_subtype_val)
  have hiV : IsOpenEmbedding iV :=
    IsOpenEmbedding.inclusion Set.inter_subset_right
      ((U ⊓ V).isOpen.preimage continuous_subtype_val)
  -- The first two squares use the same restricted orientations and actual inclusions.
  have hd (p q : ℕ) (h : p + q = n) :
      (dH q).hom.comp (compactPoincareDuality OI p q h).hom =
        (pair p q h).comp (dC p).hom := by
    apply LinearMap.ext
    intro a
    change singularHomologyMayerVietorisDifference ℚ (U : Set X) (V : Set X) q
        (compactPoincareDuality OI p q h a) = pair p q h
          (compactSupportCohomologyMayerVietorisDifference
            ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen p a)
    rw [compactSupportCohomologyMayerVietorisDifference_apply]
    apply Prod.ext
    · exact (compactPoincareDuality_openExtension OI OU iU hiU
        (isOrientationPreservingOpenEmbedding_openInclusion O (U ⊓ V) U inf_le_left)
        p q h a).symm
    · change -(singularHomologyMap ℚ iV q (compactPoincareDuality OI p q h a)) =
        compactPoincareDuality OV p q h
          (-(compactSupportCohomologyOpenExtension ℚ iV hiV p a))
      rw [map_neg]
      exact congrArg Neg.neg (compactPoincareDuality_openExtension OI OV iV hiV
        (isOrientationPreservingOpenEmbedding_openInclusion O (U ⊓ V) V inf_le_right)
        p q h a).symm
  have hs (p q : ℕ) (h : p + q = n) :
      (sH q).hom.comp (pair p q h) =
        (compactPoincareDuality O p q h).hom.comp (sC p).hom := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change singularHomologyMayerVietorisSum ℚ (U : Set X) (V : Set X) q
        (compactPoincareDuality OU p q h a, compactPoincareDuality OV p q h b) =
      compactPoincareDuality O p q h
        (compactSupportCohomologyMayerVietorisSum
          ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen p (a, b))
    rw [compactSupportCohomologyMayerVietorisSum_apply, map_add]
    exact congrArg₂ (fun x y ↦ x + y)
      (compactPoincareDuality_openExtension OU O (ContinuousMap.subtypeVal (U : Set X))
        U.isOpen.isOpenEmbedding_subtypeVal
        (homologicalOrientationOpenPullback_orientationPreserving O
          (ContinuousMap.subtypeVal (U : Set X)) U.isOpen.isOpenEmbedding_subtypeVal)
        p q h a).symm
      (compactPoincareDuality_openExtension OV O (ContinuousMap.subtypeVal (V : Set X))
        V.isOpen.isOpenEmbedding_subtypeVal
        (homologicalOrientationOpenPullback_orientationPreserving O
          (ContinuousMap.subtypeVal (V : Set X)) V.isOpen.isOpenEmbedding_subtypeVal)
        p q h b).symm
  cases q with
  | zero =>
    -- The zero-homology endpoint is right exact; its next cohomology group vanishes.
    have : Subsingleton (compactSupportCohomology ℚ ↥(U ⊓ V) (p + 1)) :=
      compactSupportCohomology_subsingleton_above_dim OI (p + 1) (by omega)
    have hsurj : Function.Surjective (sC p) := by
      intro a
      exact ((hRows p).2.1 a).mp (Subsingleton.elim _ _)
    exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
      (dC p).hom (sC p).hom (dH 0).hom (sH 0).hom
      (compactPoincareDuality OI p 0 h).hom (pair p 0 h)
      (compactPoincareDuality O p 0 h).hom (hd p 0 h) (hs p 0 h)
      (hRows p).1
      (singularHomologyMayerVietoris_exact_difference_sum
        ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover 0)
      (hI OI p 0 h).2 (hpair p 0 h) hsurj
      (singularHomologyMayerVietorisSum_zero_surjective
        ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover)
  | succ q =>
    -- The connecting square is signed. Scale both later vertical arrows by this same unit.
    have h' : (p + 1) + q = n := by omega
    let sign : ℚ := (-1) ^ (p + 1)
    have hsign : sign ≠ 0 := pow_ne_zero _ (by norm_num)
    let i4 := sign • (compactPoincareDuality OI (p + 1) q h').hom
    let i5 := sign • pair (p + 1) q h'
    have hc : (bH q).hom.comp (compactPoincareDuality O p (q + 1) h).hom =
        i4.comp (bC p).hom := by
      apply LinearMap.ext
      intro a
      exact hcap p q h a
    have hd' : (dH q).hom.comp i4 = i5.comp (dC (p + 1)).hom := by
      apply LinearMap.ext
      intro a
      change dH q (sign • compactPoincareDuality OI (p + 1) q h' a) =
        sign • pair (p + 1) q h' (dC (p + 1) a)
      rw [map_smul]
      exact congrArg (fun b ↦ sign • b) (LinearMap.congr_fun (hd (p + 1) q h') a)
    have hi4 : Function.Bijective i4 :=
      (LinearEquiv.smulOfNeZero ℚ (singularHomology ℚ ↥(U ⊓ V) q) sign hsign).bijective.comp
        (hI OI (p + 1) q h')
    have hi5 : Function.Bijective i5 :=
      (LinearEquiv.smulOfNeZero ℚ
        (singularHomology ℚ U q × singularHomology ℚ V q) sign hsign).bijective.comp
          (hpair (p + 1) q h')
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (dC p).hom (sC p).hom (bC p).hom (dC (p + 1)).hom
      (dH (q + 1)).hom (sH (q + 1)).hom (bH q).hom (dH q).hom
      (compactPoincareDuality OI p (q + 1) h).hom (pair p (q + 1) h)
      (compactPoincareDuality O p (q + 1) h).hom i4 i5
      (hd p (q + 1) h) (hs p (q + 1) h) hc hd'
      (hRows p).1 (hRows p).2.1 (hRows p).2.2
      (singularHomologyMayerVietoris_exact_difference_sum
        ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover
        (q + 1))
      (singularHomologyMayerVietoris_exact_sum_boundary
        ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover q)
      (singularHomologyMayerVietoris_exact_boundary_difference
        ℚ (U : Set X) (V : Set X) U.isOpen V.isOpen hcover q)
      (hI OI p (q + 1) h).2 (hpair p (q + 1) h) hi4 hi5.1

end AtiyahSinger
