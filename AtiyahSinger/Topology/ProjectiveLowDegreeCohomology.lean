/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveBundleCohomology

/-!
# Low-degree cohomology of the original projective bundle

Public module ID: M2018.

When the unit is the only Leray--Hirsch generator in the degree under
consideration, the original projection pullback is bijective. In particular,
positive-rank complex projective bundles preserve degree-zero cohomology.
This supplies the coefficient comparison needed for detecting degree-two
classes on successive projective line bundles.

Source: the ordinary Leray--Hirsch theorem, Hatcher, Algebraic Topology,
Section 4.D. All comparisons use the existing singular cochain map and its
actual unit summand, with no connectedness assumption on the base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Below every nonunit Leray--Hirsch degree, the original pullback is bijective. -/
theorem singularCohomologyPullback_bijective_of_lerayHirsch_below_degrees
    (R : Type) [CommRing R] {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {ι : Type u} [Fintype ι]
    (p : C(Y, X)) (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (i₀ : ι) (hd : d i₀ = 0)
    (hc : singularCocycleClass R Y 0 (hd ▸ c i₀) = singularCohomologyOne R Y)
    (n : ℕ) (hn : ∀ i, i ≠ i₀ → n < d i)
    (h : Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R p d c) n)) :
    Function.Bijective (singularCohomologyPullback R p n) := by
  classical
  refine ⟨singularCohomologyPullback_injective_of_lerayHirsch
    R p d c i₀ hd hc n h.injective, ?_⟩
  let C (i : ι) : CochainComplex (ModuleCat.{u} R) ℕ := (singularCochains R X).extend
    (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))
  let P (a : (cochainFamilyProduct R C).homology n) (i : ι) : (C i).homology n :=
    homologyMap (cochainFamilyProductProjection R C i) n a
  let F (i : ι) : (C i).homology n ⟶ singularCohomology R Y n := homologyMap
    (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom p).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫
      singularCochainCupMap R Y (d i) (c i)) n
  -- Every positive shift is zero in this degree, so only the unit term survives.
  intro b
  obtain ⟨a, ha⟩ := h.surjective b
  have hsum : F i₀ (P a i₀) = b := by
    rw [homologyMap_singularCohomologyLerayHirschMap] at ha
    change (∑ i, F i (P a i)) = b at ha
    rw [Finset.sum_eq_single i₀] at ha
    · exact ha
    · intro i _ hi
      have hz : IsZero ((C i).homology n) := by
        apply (exactAt_iff_isZero_homology _ _).mp
        exact extend_exactAt _ _ n (by
          intro j hj
          change j + d i = n at hj
          have := hn i hi
          omega)
      let := ModuleCat.isZero_iff_subsingleton.mp hz
      rw [show P a i = 0 from Subsingleton.elim _ _, map_zero]
    · simp
  -- The remaining zero-shift cup map is exactly pullback followed by cup with one.
  have hunit (r : ℕ) (c₀ : singularCocycles R Y r) (hr : r = 0)
      (hclass : singularCocycleClass R Y 0 (hr ▸ c₀) = singularCohomologyOne R Y)
      (z : ((singularCochains R X).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) r)).homology n) :
      ∃ x : singularCohomology R X n,
        singularCohomologyPullback R p n x = homologyMap
          (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom p).op)
              (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
            singularCochainCupMap R Y r c₀) n z := by
    subst r
    let J := (singularCochains R X).extendHomologyIso
      (ComplexShape.embeddingUp'Add (1 : ℕ) 0) (j := n) rfl
    refine ⟨J.hom z, ?_⟩
    have heq := homologyMap_pullback_singularCochainCupMap R p 0 c₀ n (J.hom z)
    rw [hclass, singularCohomologyCup_one] at heq
    simpa only [J, Nat.add_zero, Iso.hom_inv_id_apply] using heq.symm
  obtain ⟨x, hx⟩ := hunit (d i₀) (c i₀) hd hc (P a i₀)
  exact ⟨x, hx.trans hsum⟩

namespace ComplexBundle

open Bundle

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A positive-rank projective bundle preserves the original degree-zero cohomology. -/
theorem hermitianProjectiveProjection_cohomologyZero_bijective (hr : 0 < r) :
    Function.Bijective (singularCohomologyPullback R (hermitianProjectiveProjection r E h) 0) := by
  classical
  let Q := HermitianProjectiveBundle r E h
  let t : singularCohomology R Q 2 :=
    singularCohomologyChangeCoefficients R Q 2 (hermitianProjectiveChernRoot r E h)
  have hrep (k : ℕ) (a : singularCohomology R Q k) :
      ∃ c : singularCocycles R Q k, singularCocycleClass R Q k c = a := by
    let C := singularCochains R Q
    obtain ⟨c, hc⟩ := (C.sc k).moduleCatToCycles.range.mkQ_surjective
      ((C.sc k).moduleCatHomologyIso.hom a)
    refine ⟨c, ?_⟩
    change (C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ c) = a
    rw [hc, Iso.hom_inv_id_apply]
  choose c hc using fun i : ULift.{u} (Fin r) ↦
    hrep (2 * i.down.val) (singularCohomologyDegreeTwoPow R Q t i.down.val)
  let i₀ : ULift.{u} (Fin r) := ⟨⟨0, hr⟩⟩
  have hunit : singularCocycleClass R Q 0 (c i₀) = singularCohomologyOne R Q := hc i₀
  -- All other actual tautological powers have strictly positive degree.
  apply singularCohomologyPullback_bijective_of_lerayHirsch_below_degrees R
    (hermitianProjectiveProjection r E h) (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val)
    c i₀ rfl hunit 0
  · intro i hi
    have hne : i.down.val ≠ 0 := by
      intro hz
      apply hi
      apply ULift.ext
      exact Fin.ext hz
    omega
  · exact homologyMap_hermitianProjectiveLerayHirsch_bijective R r E h c hc 0

end ComplexBundle

end AtiyahSinger
