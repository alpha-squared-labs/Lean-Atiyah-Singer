/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyProperPullback
public import AtiyahSinger.Topology.CohomologyEuler
public import AtiyahSinger.Topology.RelativeSingularFunctoriality

/-!
# Naturality of the specified oriented Thom multiplication

Public module ID: M1630.

An actual map of total spaces covering a base map preserves the normalized Thom
class when its specified fiber equivalences preserve the original fiber
orientation classes. Uniqueness of the normalized extension proves this before
cup naturality proves the formula for the original Thom map. No properness is
needed for the relative statement and no target Thom identity is a hypothesis.

Source: Milnor--Stasheff, section 9, naturality of the oriented Thom class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

variable (R : Type) [CommRing R] (r : ℕ)
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (F : Y → Type u) [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℝ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) F)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) F]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) F]
  (oE : CohomologyOrientation R r E) (oF : CohomologyOrientation R r F)
  (f : C(X, Y))
  (g : C(TotalSpace (EuclideanSpace ℝ (Fin r)) E,
    TotalSpace (EuclideanSpace ℝ (Fin r)) F))
  (hN : Set.MapsTo g (bundleNonzero r E) (bundleNonzero r F))
  (e : ∀ x, E x ≃L[ℝ] F (f x))
  (hg : ∀ x, g.comp (bundleFiberInclusion r E x) =
    (bundleFiberInclusion r F (f x)).comp ⟨e x, (e x).continuous⟩)
  (ho : ∀ x, relativeSingularCohomologyPullback R
    (⟨e x, (e x).continuous⟩ : C(E x, F (f x)))
      (show Set.MapsTo (e x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) r
      (oF.fiberClass (f x)) = oE.fiberClass x)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hg ho in
/-- Preservation of the specified fiber orientations preserves the normalized Thom class. -/
theorem cohomologyThomClass_pullback :
    relativeSingularCohomologyPullback R g hN r (cohomologyThomClass R r F oF) =
      cohomologyThomClass R r E oE := by
  -- Compare the same class on every original fiber before applying global uniqueness.
  apply (existsUnique_cohomologyThomClass R r E oE).unique
  · intro x
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    simp only [hg x]
    rw [relativeSingularCohomologyPullback_comp R
      (⟨e x, (e x).continuous⟩ : C(E x, F (f x)))
      (bundleFiberInclusion r F (f x))
      (show Set.MapsTo (e x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm)))
      (fun _ hv ↦ hv) r, ModuleCat.comp_apply]
    have hrestriction : relativeSingularCohomologyPullback R
        (bundleFiberInclusion r F (f x)) (fun _ hv ↦ hv) r
        (cohomologyThomClass R r F oF) = oF.fiberClass (f x) :=
      (existsUnique_cohomologyThomClass R r F oF).exists.choose_spec (f x)
    exact (congrArg (fun a ↦ relativeSingularCohomologyPullback R
      (⟨e x, (e x).continuous⟩ : C(E x, F (f x)))
        (show Set.MapsTo (e x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
          fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) r a)
      hrestriction).trans (ho x)
  · exact (existsUnique_cohomologyThomClass R r E oE).exists.choose_spec

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hg ho in
/-- The original pullback and cup Thom map is natural under the same oriented bundle map. -/
theorem cohomologyThomMap_pullback (p : ℕ) (a : singularCohomology R Y p) :
    relativeSingularCohomologyPullback R g hN (p + r) (cohomologyThomMap R r F oF p a) =
      cohomologyThomMap R r E oE p (singularCohomologyPullback R f p a) := by
  -- The total-space square is the one determined by the same fiber equivalences.
  have hbase : (bundleProjection r F).comp g = f.comp (bundleProjection r E) := by
    apply ContinuousMap.ext
    rintro ⟨x, v⟩
    have hx := congrArg (fun h ↦ (h v).proj) (hg x)
    exact hx
  have hpull : singularCohomologyPullback R g p
      (singularCohomologyPullback R (bundleProjection r F) p a) =
      singularCohomologyPullback R (bundleProjection r E) p
        (singularCohomologyPullback R f p a) := by
    have hmap : singularCohomologyPullback R (bundleProjection r F) p ≫
        singularCohomologyPullback R g p =
      singularCohomologyPullback R f p ≫
        singularCohomologyPullback R (bundleProjection r E) p := by
      change (singularCohomologyFunctor R p).map _ ≫
          (singularCohomologyFunctor R p).map _ =
        (singularCohomologyFunctor R p).map _ ≫ (singularCohomologyFunctor R p).map _
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      exact congrArg (fun h : C(_, _) ↦ singularCohomologyPullback R h p) hbase
    exact congrArg (fun h ↦ h a) hmap
  -- Relative action naturality preserves the order: base factor first, Thom class second.
  change relativeSingularCohomologyPullback R g hN (p + r)
    (relativeSingularCohomologyAction R (bundleNonzero r F) p r
      (singularCohomologyPullback R (bundleProjection r F) p a)
      (cohomologyThomClass R r F oF)) = _
  rw [relativeSingularCohomologyPullback_action, hpull,
    cohomologyThomClass_pullback R r E F oE oF f g hN e hg ho]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hN hg ho in
/-- Proper oriented bundle maps preserve the original compact-support Thom pushforward. -/
theorem cohomologyZeroSectionPushforward_pullback [CompactSpace X] [CompactSpace Y]
    (hgProper : IsProperMap g) (p : ℕ) (a : singularCohomology R Y p) :
    compactSupportCohomologyProperPullback R g hgProper (p + r)
        (cohomologyZeroSectionPushforward R r F oF p a) =
      cohomologyZeroSectionPushforward R r E oE p
        (singularCohomologyPullback R f p a) := by
  -- Fiberwise injectivity identifies the literal inverse support with the original zero section.
  have hK : properCompactPreimage g hgProper (cohomologyZeroSectionSupport r F) =
      cohomologyZeroSectionSupport r E := by
    apply SetLike.coe_injective
    ext z
    rcases z with ⟨x, v⟩
    have hz : g ⟨x, v⟩ = ⟨f x, e x v⟩ := congrArg (fun t ↦ t v) (hg x)
    change (g ⟨x, v⟩).snd = 0 ↔ v = 0
    rw [hz]
    exact (e x).map_eq_zero_iff
  -- Pull back the same relative Thom representative and use the oriented naturality just proved.
  change compactSupportCohomologyProperPullback R g hgProper (p + r)
    (compactSupportCohomologyClass R _ (cohomologyZeroSectionSupport r F) (p + r)
      (cohomologyThomMap R r F oF p a)) = _
  rw [compactSupportCohomologyProperPullback_representative]
  have htransport (K L : TopologicalSpace.Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E))
      (hKL : K = L)
      (hKmap : Set.MapsTo g (K : Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ
        (bundleNonzero r F))
      (hLmap : Set.MapsTo g (L : Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ
        (bundleNonzero r F)) :
      compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) K (p + r)
        (relativeSingularCohomologyPullback R g hKmap (p + r)
          (cohomologyThomMap R r F oF p a)) =
      compactSupportCohomologyClass R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) L (p + r)
        (relativeSingularCohomologyPullback R g hLmap (p + r)
          (cohomologyThomMap R r F oF p a)) := by
    subst L
    rfl
  refine (htransport _ _ hK _ hN).trans ?_
  change compactSupportCohomologyClass R _ (cohomologyZeroSectionSupport r E) (p + r)
    (relativeSingularCohomologyPullback R g hN (p + r)
      (cohomologyThomMap R r F oF p a)) = _
  rw [cohomologyThomMap_pullback R r E F oE oF f g hN e hg ho]
  rfl

end AtiyahSinger
