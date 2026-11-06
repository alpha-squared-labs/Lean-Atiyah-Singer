/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainDescent
public import AtiyahSinger.Topology.SingularCechCochains

/-!
# Unique gluing in relative singular cohomology

Public module ID: M2130.

For an arbitrary open cover, lower-degree vanishing on finite intersections makes
relative cohomology in the specified degree the equalizer of actual Čech restrictions.
The augmented complex uses small relative chains. Its comparison with the original
relative complex is proved by the small-chain homotopy equivalence and the pair exact
sequence; singular cohomology itself is never assumed to be a sheaf.

The local datum is a class in the product complex on cover members, and compatibility
means that its alternating restriction class is zero on pairwise intersections.
No compactness, separation, connectedness, or nonempty-cover hypothesis is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Lower-degree overlap vanishing gives unique gluing on the original relative pair. -/
theorem existsUnique_relativeSingularCohomology_of_cech
    (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
    {ι : Type u} (U : ι → Set X) (A : Set X)
    (hOpen : ∀ i, IsOpen (U i)) (hCover : ⋃ i, U i = Set.univ)
    (n : ℕ) (hvan : ∀ m (a : Fin (m + 2) → ι), ∀ q, q < n →
      Subsingleton (relativeSingularCohomology R
        ((Subtype.val : singularCechIntersection U a → X) ⁻¹' A) q))
    (a : (singularCechCochains R U A 1).homology n)
    (ha : HomologicalComplex.homologyMap (singularCechDifferential R U A 1) n a = 0) :
    ∃! z : relativeSingularCohomology R A n,
      HomologicalComplex.homologyMap
        (smallRelativeSingularCochainsRestriction R (Set.range U) A ≫
          singularCechDifferential R U A 0) n z = a := by
  let C := singularCechCochains R U A
  let δ := singularCechDifferential R U A
  have hvan' (i : ℕ) (hi : 2 ≤ i) (q : ℕ) (hq : q < n) :
      Function.Exact ((C i).d (q - 1) q) ((C i).d q (q + 1)) := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    let F (t : Fin (m + 2) → ι) := relativeSingularCochains R
      ((Subtype.val : singularCechIntersection U t → X) ⁻¹' A)
    have hprod := (bijective_homologyMap_cochainFamilyProductProjection R F q).injective
    have (t : Fin (m + 2) → ι) : Subsingleton ((F t).homology q) := hvan m t q hq
    have : Subsingleton ((cochainFamilyProduct R F).homology q) := hprod.subsingleton
    have hex : (C (m + 2)).ExactAt q := by
      change (cochainFamilyProduct R F).ExactAt q
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    have hprev : (ComplexShape.up ℕ).prev q = q - 1 := by
      cases q <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ]
    have hs := (HomologicalComplex.exactAt_iff' (C (m + 2)) (q - 1) q (q + 1) hprev
      (CochainComplex.next ℕ q)).mp hex
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs
  -- Exact rows glue the same local cohomology class in the small relative model.
  obtain ⟨b, hb, huniq⟩ := existsUnique_cohomology_of_exact_rows R C δ
    (singularCechDifferential_comp R U A)
    (singularCechDifferential_exact R U A) (singularCechAugmentation_injective R U A)
    n hvan' a ha
  let F := smallRelativeSingularCochainsRestriction R (Set.range U) A
  have : IsIso (HomologicalComplex.homologyMap F n) :=
    isIso_homologyMap_smallRelativeSingularCochainsRestriction R (Set.range U) A
      (by rintro V ⟨i, rfl⟩; exact hOpen i) (by simpa using hCover) n
  have hbij := ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap F n)
  obtain ⟨z, hz⟩ := hbij.surjective b
  refine ⟨z, ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap (δ 0) n
      (HomologicalComplex.homologyMap F n z) = a
    rw [hz]
    exact hb
  · intro w hw
    apply hbij.injective
    rw [hz]
    apply huniq
    rw [HomologicalComplex.homologyMap_comp] at hw
    exact hw

end AtiyahSinger
