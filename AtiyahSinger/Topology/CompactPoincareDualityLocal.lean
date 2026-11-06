/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactDualityNaturality
public import AtiyahSinger.Topology.EuclideanPoincareDuality
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Local models for compact Poincaré duality

Public module ID: M1646.

Homeomorphisms transport the original compact-support cap map, with the
specified orientation pulled back along the same map. This identifies the
duality map on bounded convex open sets with its Euclidean local model.

Source: the local-model step in Hatcher, *Algebraic Topology*, Theorem 3.35.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace Topology Opposite

universe u

section OpenExtension

variable (R : Type) [CommRing R] {X Y : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Extension along the identity is the identity on the original support colimit. -/
theorem compactSupportCohomologyOpenExtension_id (p : ℕ) :
    compactSupportCohomologyOpenExtension R (ContinuousMap.id X) IsOpenEmbedding.id p =
      𝟙 (compactSupportCohomology R X p) := by
  apply colimit.hom_ext
  intro K
  erw [colimit.ι_desc]
  rw [Category.comp_id]
  let L := openEmbeddingCompactImage (ContinuousMap.id X) K
  have hL : L = K := Compacts.map_id K
  let P := openEmbeddingCohomologySupportPullback R (ContinuousMap.id X)
    IsOpenEmbedding.id K p
  have : IsIso P := isIso_openEmbeddingCohomologySupportPullback R
    (ContinuousMap.id X) IsOpenEmbedding.id K p
  have hleg (L : Compacts X) (hL : L = K)
      (hp : Set.MapsTo (ContinuousMap.id X) (K : Set X)ᶜ (L : Set X)ᶜ)
      [IsIso (relativeSingularCohomologyPullback R (ContinuousMap.id X) hp p)] :
      (asIso (relativeSingularCohomologyPullback R (ContinuousMap.id X) hp p)).inv ≫
          compactSupportCohomologyClass R X L p = compactSupportCohomologyClass R X K p := by
    subst L
    have hid : relativeSingularCohomologyPullback R (ContinuousMap.id X) hp p = 𝟙 _ := by
      change (relativeSingularCohomologyFunctor R X p).map (𝟙 _) = _
      exact CategoryTheory.Functor.map_id _ _
    simp [hid]
  exact @hleg L hL _ (isIso_openEmbeddingCohomologySupportPullback R
    (ContinuousMap.id X) IsOpenEmbedding.id K p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A homeomorphism induces a bijective actual open-extension map. -/
theorem compactSupportCohomologyOpenExtension_bijective_of_homeomorph (e : X ≃ₜ Y)
    (p : ℕ) :
    Function.Bijective (compactSupportCohomologyOpenExtension R
      ⟨e, e.continuous⟩ e.isOpenEmbedding p) := by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  have hgf : g.comp f = ContinuousMap.id X := by ext x; exact e.symm_apply_apply x
  have hfg : f.comp g = ContinuousMap.id Y := by ext y; exact e.apply_symm_apply y
  let F := compactSupportCohomologyOpenExtension R f e.isOpenEmbedding p
  let G := compactSupportCohomologyOpenExtension R g e.symm.isOpenEmbedding p
  have hFG : F ≫ G = 𝟙 _ := by
    rw [← compactSupportCohomologyOpenExtension_comp]
    simpa only [hgf] using compactSupportCohomologyOpenExtension_id (X := X) R p
  have hGF : G ≫ F = 𝟙 _ := by
    rw [← compactSupportCohomologyOpenExtension_comp]
    simpa only [hfg] using compactSupportCohomologyOpenExtension_id (X := Y) R p
  exact ⟨Function.LeftInverse.injective (fun a ↦ congrArg (fun f ↦ f a) hFG),
    Function.RightInverse.surjective (fun b ↦ congrArg (fun f ↦ f b) hGF)⟩

end OpenExtension

section Manifolds

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
variable [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An orientation-preserving homeomorphism transports bijectivity of the same cap map. -/
theorem compactPoincareDuality_bijective_of_homeomorph
    (e : X ≃ₜ Y) (OX : HomologicalOrientation n X) (OY : HomologicalOrientation n Y)
    (ho : IsOrientationPreservingOpenEmbedding OX OY ⟨e, e.continuous⟩ e.isOpenEmbedding)
    (p q : ℕ) (h : p + q = n) (hX : Function.Bijective (compactPoincareDuality OX p q h)) :
    Function.Bijective (compactPoincareDuality OY p q h) := by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let F := compactSupportCohomologyOpenExtension ℚ f e.isOpenEmbedding p
  let G := singularHomologyMap ℚ f q
  have hF : Function.Bijective F :=
    compactSupportCohomologyOpenExtension_bijective_of_homeomorph ℚ e p
  have hG : Function.Bijective G := by
    let H := singularChainsFunctor ℚ ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.down ℕ) q
    let i := H.mapIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e)
    exact i.toLinearEquiv.bijective
  have hnat (a : compactSupportCohomology ℚ X p) :
      compactPoincareDuality OY p q h (F a) = G (compactPoincareDuality OX p q h a) :=
    compactPoincareDuality_openExtension OX OY f e.isOpenEmbedding ho p q h a
  -- The naturality square contains the prescribed cap maps and actual homeomorphism maps.
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := hF.2 a
    obtain ⟨b', rfl⟩ := hF.2 b
    exact congrArg F (hX.1 (hG.1 ((hnat a').symm.trans (hab.trans (hnat b')))))
  · intro b
    obtain ⟨b', hb'⟩ := hG.2 b
    obtain ⟨a, ha⟩ := hX.2 b'
    exact ⟨F a, (hnat a).trans ((congrArg G ha).trans hb')⟩

/-- The original duality map on an empty manifold is the unique map between zero groups. -/
theorem compactPoincareDuality_bijective_of_isEmpty [IsEmpty X]
    (O : HomologicalOrientation n X) (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  have : Subsingleton (singularHomology ℚ X q) :=
    subsingleton_singularHomology_of_isEmpty ℚ X q
  have hzero (a : compactSupportCohomology ℚ X p) : a = 0 := by
    obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative ℚ X p a
    have hK : (K : Set X)ᶜ = Set.univ := Set.eq_univ_of_forall fun x ↦ isEmptyElim x
    have : Subsingleton (relativeSingularHomology ℚ (K : Set X)ᶜ p) := by
      rw [hK]
      exact relativeSingularHomology_subsingleton_univ ℚ p
    have : Subsingleton (relativeSingularCohomology ℚ (K : Set X)ᶜ p) :=
      subsingleton_relativeSingularCohomology_of_subsingleton_homology ℚ (K : Set X)ᶜ p
    rw [Subsingleton.elim b 0, map_zero]
  exact ⟨fun a b _ ↦ (hzero a).trans (hzero b).symm,
    fun b ↦ ⟨0, Subsingleton.elim _ b⟩⟩

end Manifolds

section ConvexOpen

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) E] [SecondCountableTopology E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Bounded convex open Euclidean models satisfy compact Poincaré duality in every degree. -/
theorem compactPoincareDuality_bijective_of_bounded_convex
    (e : E ≃L[ℝ] (Fin n → ℝ)) (U : Opens E)
    (hconvex : Convex ℝ (U : Set E)) (hbounded : Bornology.IsBounded (U : Set E))
    (O : HomologicalOrientation n U) (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  by_cases hne : (U : Set E).Nonempty
  · -- Gauge rescaling identifies the bounded convex domain with the unit ball.
    obtain ⟨g, hg, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hconvex (by simpa only [U.isOpen.interior_eq] using hne) hbounded
    have hgU : g '' (U : Set E) = Metric.ball 0 1 := by
      simpa only [U.isOpen.interior_eq] using hg
    let toBall : U ≃ₜ Metric.ball (0 : E) 1 :=
      (g.image (U : Set E)).trans (Homeomorph.setCongr hgU)
    let f : E ≃ₜ U := Homeomorph.unitBall.trans toBall.symm
    let O' := homologicalOrientationOpenPullback O ⟨f, f.continuous⟩ f.isOpenEmbedding
    apply compactPoincareDuality_bijective_of_homeomorph f O' O
      (homologicalOrientationOpenPullback_orientationPreserving O
        ⟨f, f.continuous⟩ f.isOpenEmbedding) p q h
    exact compactPoincareDuality_bijective_of_continuousLinearEquiv e O' p q h
  · -- The empty open set has zero original homology and zero relative representatives.
    let : IsEmpty U := ⟨fun x ↦ hne ⟨x.val, x.property⟩⟩
    exact compactPoincareDuality_bijective_of_isEmpty O p q h

end ConvexOpen

end AtiyahSinger
