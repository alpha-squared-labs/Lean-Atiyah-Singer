/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactPoincareDualityLocal
public import AtiyahSinger.Topology.CompactSupportCohomologyDirectedUnion
public import AtiyahSinger.Topology.SingularHomologyDirectedUnion

/-!
# Directed-open-union induction for compact Poincaré duality

Public module ID: M1644.

Restriction of one ambient orientation gives compatible cap maps on all open
stages. Finite-stage representatives and eventual zero detection for the
original compact-support cohomology and singular homology then transfer
bijectivity to their directed open union.

Source: the directed-union step in Hatcher, *Algebraic Topology*, section 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

universe u

section Orientation

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Inclusions preserve the orientations restricted from the same ambient orientation. -/
theorem isOrientationPreservingOpenEmbedding_openInclusion
    (O : HomologicalOrientation n X) (U V : Opens X) (hUV : U ≤ V) :
    IsOrientationPreservingOpenEmbedding
      (homologicalOrientationOpenPullback O (ContinuousMap.subtypeVal (U : Set X))
        U.isOpen.isOpenEmbedding_subtypeVal)
      (homologicalOrientationOpenPullback O (ContinuousMap.subtypeVal (V : Set X))
        V.isOpen.isOpenEmbedding_subtypeVal)
      (ContinuousMap.inclusion hUV)
      (IsOpenEmbedding.inclusion hUV (U.isOpen.preimage continuous_subtype_val)) := by
  intro x
  let f := ContinuousMap.inclusion hUV
  let g := ContinuousMap.subtypeVal (V : Set X)
  let h := ContinuousMap.subtypeVal (U : Set X)
  have hf : IsOpenEmbedding f :=
    IsOpenEmbedding.inclusion hUV (U.isOpen.preimage continuous_subtype_val)
  have hg : IsOpenEmbedding g := V.isOpen.isOpenEmbedding_subtypeVal
  have hh : IsOpenEmbedding h := U.isOpen.isOpenEmbedding_subtypeVal
  let OX := homologicalOrientationOpenPullback O h hh
  let OY := homologicalOrientationOpenPullback O g hg
  let pf : Set.MapsTo f ({x}ᶜ) ({f x}ᶜ) := fun y hy heq ↦ hy (hf.injective heq)
  let pg : Set.MapsTo g ({f x}ᶜ) ({g (f x)}ᶜ) := fun y hy heq ↦ hy (hg.injective heq)
  have hcomp : relativeSingularHomologyMap ℤ f pf n ≫
      relativeSingularHomologyMap ℤ g pg n =
        relativeSingularHomologyMap ℤ h (pg.comp pf) n := by
    simp only [relativeSingularHomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← relativeSingularChainsMap_comp]
    rfl
  -- The common ambient local-homology isomorphism detects the chosen integral generators.
  apply (relativeSingularHomologyMap_openEmbedding_bijective g hg (f x) n).1
  change relativeSingularHomologyMap ℤ g pg n
      (relativeSingularHomologyMap ℤ f pf n (OX.localGenerator x 1)) =
    relativeSingularHomologyMap ℤ g pg n (OY.localGenerator (f x) 1)
  exact (congrArg (fun a ↦ a (OX.localGenerator x 1)) hcomp).trans
    ((homologicalOrientationOpenPullback_orientationPreserving O h hh x).trans
      (homologicalOrientationOpenPullback_orientationPreserving O g hg (f x)).symm)

end Orientation

section DirectedUnion

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
variable [T2Space X] [RegularSpace X] [SecondCountableTopology X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Bijective cap duality on every stage of a directed open cover gives ambient cap duality. -/
theorem compactPoincareDuality_bijective_of_directedCover
    {ι : Type u} [Nonempty ι] (U : ι → Opens X)
    (hdir : Directed (· ≤ ·) U) (hcover : ⋃ i, (U i : Set X) = Set.univ)
    (O : HomologicalOrientation n X) (p q : ℕ) (h : p + q = n)
    (hU : ∀ i, Function.Bijective (compactPoincareDuality
      (homologicalOrientationOpenPullback (X := U i) O
        (ContinuousMap.subtypeVal (U i : Set X))
        (U i).isOpen.isOpenEmbedding_subtypeVal) p q h)) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  let f (i : ι) : C(U i, X) := ContinuousMap.subtypeVal (U i : Set X)
  have hf (i : ι) : IsOpenEmbedding (f i) := (U i).isOpen.isOpenEmbedding_subtypeVal
  let O' (i : ι) : HomologicalOrientation n (U i) :=
    homologicalOrientationOpenPullback O (f i) (hf i)
  have hnat (i : ι) (a : compactSupportCohomology ℚ (U i) p) :
      compactPoincareDuality O p q h
          (compactSupportCohomologyOpenExtension ℚ (f i) (hf i) p a) =
        singularHomologyMap ℚ (f i) q (compactPoincareDuality (O' i) p q h a) :=
    compactPoincareDuality_openExtension (O' i) O (f i) (hf i)
      (homologicalOrientationOpenPullback_orientationPreserving O (f i) (hf i)) p q h a
  constructor
  · -- A kernel class lifts to one stage; its homology zero relation holds at a later stage.
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨i, b, rfl⟩ := compactSupportCohomology_exists_openExtension_of_directedCover
      ℚ (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hdir hcover p a
    have hb : singularHomologyMap ℚ (f i) q (compactPoincareDuality (O' i) p q h b) = 0 :=
      (hnat i b).symm.trans ha
    obtain ⟨j, hij, hj⟩ := singularHomologyMap_directedUnion_eventually_eq_zero
      ℚ (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hdir hcover i q
        (compactPoincareDuality (O' i) p q h b) hb
    let g := ContinuousMap.inclusion hij
    have hg : IsOpenEmbedding g :=
      IsOpenEmbedding.inclusion hij ((U i).isOpen.preimage continuous_subtype_val)
    have hz : compactSupportCohomologyOpenExtension ℚ g hg p b = 0 := by
      apply (hU j).1
      rw [map_zero]
      exact (compactPoincareDuality_openExtension (O' i) (O' j) g hg
        (isOrientationPreservingOpenEmbedding_openInclusion O (U i) (U j) hij)
        p q h b).trans hj
    -- Extension is functorial for these same inclusions, so the original ambient class is zero.
    have hcomp := congrArg (fun F ↦ F b)
      (compactSupportCohomologyOpenExtension_comp ℚ g hg (f j) (hf j) p)
    change compactSupportCohomologyOpenExtension ℚ (f i) (hf i) p b = 0
    exact hcomp.trans ((congrArg (compactSupportCohomologyOpenExtension ℚ (f j) (hf j) p)
      hz).trans (map_zero _))
  · -- A homology representative lifts to one stage and is capped there before extension.
    intro c
    obtain ⟨i, d, hd⟩ := singularHomologyMap_directedUnion_jointly_surjective
      ℚ (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hdir hcover q c
    obtain ⟨a, ha⟩ := (hU i).2 d
    exact ⟨compactSupportCohomologyOpenExtension ℚ (f i) (hf i) p a,
      (hnat i a).trans ((congrArg (singularHomologyMap ℚ (f i) q) ha).trans hd)⟩

end DirectedUnion

end AtiyahSinger
