/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyRing
public import AtiyahSinger.Topology.RelativeCupVanishing

/-!
# Finite open-cover cup vanishing

Public module ID: M1851.

Products of degree-two classes that vanish on the corresponding members of a
finite open cover are zero. The empty-cover case retains the actual empty space
and its zero cohomology. The relative union cup product supplies the induction,
without assuming that singular cohomology is a sheaf.

Source: Hatcher, Algebraic Topology, Section 3.2; Vector Bundles and K-Theory,
the relative cup-product argument in the proof of Theorem 3.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

attribute [local irreducible] singularCohomologyCup

/-- The actual singular cohomology of an empty space is zero over every coefficient ring. -/
theorem subsingleton_singularCohomology_of_isEmpty
    (X : Type u) [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    Subsingleton (singularCohomology R X n) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let : IsEmpty (S.obj (op ⦋n⦌)) :=
    ⟨fun σ ↦ isEmptyElim
      (((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) (Convexity.StdSimplex.single 0))⟩
  -- There are no singular simplices, so the original degree-n cochain module is zero.
  have hcochain : Subsingleton ((singularCochains R X).X n) :=
    (singularCochainEquiv R X n).injective.subsingleton
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply ((singularCochains R X).exactAt_iff_isZero_homology n).mp
  exact ShortComplex.exact_of_isZero_X₂ _ (ModuleCat.isZero_iff_subsingleton.mpr hcochain)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Degree-two classes vanishing on the respective members of a finite open cover
have zero product. -/
theorem singularEvenCohomologyOf_prod_eq_zero_of_openCover
    {X : Type u} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    (a : ι → singularCohomology R X 2)
    (ha : ∀ i, singularCohomologyPullback R (ContinuousMap.subtypeVal (U i)) 2 (a i) = 0) :
    ∏ i, singularEvenCohomologyOf R X 1 (a i) = 0 := by
  classical
  let Ufin (s : Finset ι) : Set X := ⋃ i ∈ s, U i
  have hopen (s : Finset ι) : IsOpen (Ufin s) :=
    isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hU i
  have htransport (A : Set X) (p q : ℕ) (hpq : p = q)
      (b : singularCohomology R X p) :
      singularCohomologyPullback R (ContinuousMap.subtypeVal A) q
          ((eqToIso (congrArg (fun n ↦ singularCohomology R X n) hpq)).hom b) =
        (eqToIso (congrArg (fun n ↦ singularCohomology R A n) hpq)).hom
          (singularCohomologyPullback R (ContinuousMap.subtypeVal A) p b) := by
    subst q
    rfl
  -- Each finite product has its original homogeneous representative, vanishing on the union.
  have hfinite (s : Finset ι) :
      ∃ b : singularCohomology R X (2 * s.card),
        singularEvenCohomologyOf R X s.card b =
            ∏ i ∈ s, singularEvenCohomologyOf R X 1 (a i) ∧
          singularCohomologyPullback R (ContinuousMap.subtypeVal (Ufin s)) (2 * s.card) b =
            0 := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨singularCohomologyOne R X, ?_, ?_⟩
      · simp only [Finset.card_empty, Finset.prod_empty, singularEvenCohomologyOf_one]
      · let : IsEmpty (Ufin ∅) := by simp [Ufin]
        exact @Subsingleton.elim _
          (subsingleton_singularCohomology_of_isEmpty R (Ufin ∅) _) _ _
    | @insert i s hi ih =>
      obtain ⟨b, hb, hvan⟩ := ih
      have hcard : (insert i s).card = 1 + s.card := by
        rw [Finset.card_insert_of_notMem hi, Nat.add_comm]
      have hunion : Ufin (insert i s) = U i ∪ Ufin s := by
        ext x
        simp [Ufin]
      rw [hcard, hunion]
      refine ⟨singularCohomologyEvenCup R X 1 s.card (a i) b, ?_, ?_⟩
      · rw [singularEvenCohomologyOf_cup, hb, Finset.prod_insert hi]
      · -- Relative union cup gives the ordinary vanishing before canonical even regrading.
        have hv := singularCohomologyCup_restrict_union_eq_zero R (U i) (Ufin s)
          (hU i) (hopen s) 2 (2 * s.card) (a i) b (ha i) hvan
        have ht := htransport (U i ∪ Ufin s) (2 + 2 * s.card) (2 * (1 + s.card))
          (by omega) (singularCohomologyCup R X 2 (2 * s.card) (a i) b)
        change singularCohomologyPullback R (ContinuousMap.subtypeVal (U i ∪ Ufin s))
          (2 * (1 + s.card)) (singularCohomologyEvenCup R X 1 s.card (a i) b) = _ at ht
        rw [hv, map_zero] at ht
        exact ht
  obtain ⟨b, hb, hvan⟩ := hfinite Finset.univ
  have huniv : Ufin Finset.univ = Set.univ := by simpa [Ufin] using hcover
  rw [huniv] at hvan
  -- Restriction to the whole original space is injective, including when that space is empty.
  let j : C(X, (Set.univ : Set X)) :=
    ⟨fun x ↦ ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
  have hinv : singularCohomologyPullback R (ContinuousMap.subtypeVal Set.univ)
        (2 * (Finset.univ : Finset ι).card) ≫
          singularCohomologyPullback R j (2 * (Finset.univ : Finset ι).card) =
      𝟙 (singularCohomology R X (2 * (Finset.univ : Finset ι).card)) := by
    let H := singularCohomologyFunctor R (2 * (Finset.univ : Finset ι).card)
    change H.map (TopCat.ofHom (ContinuousMap.subtypeVal Set.univ)).op ≫
      H.map (TopCat.ofHom j).op = _
    rw [← H.map_comp, ← op_comp]
    exact H.map_id _
  have hvalue := congrArg (fun f ↦ f b) hinv
  change singularCohomologyPullback R j (2 * (Finset.univ : Finset ι).card)
      (singularCohomologyPullback R (ContinuousMap.subtypeVal Set.univ)
        (2 * (Finset.univ : Finset ι).card) b) = b at hvalue
  rw [hvan, map_zero] at hvalue
  rw [← hb, ← hvalue, map_zero]

end AtiyahSinger
