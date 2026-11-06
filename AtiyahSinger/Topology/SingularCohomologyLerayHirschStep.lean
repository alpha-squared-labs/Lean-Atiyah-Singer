/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch
public import AtiyahSinger.Topology.SingularCohomologySplitBasis

/-!
# Extending a Leray--Hirsch family through a relative class

Public module ID: M2134.

Separate one specified summand of the finite cochain comparison. If the
other summands parametrize the subspace cohomology in every degree, and
the specified summand is the ordinary image of a relative isomorphism,
then the full Leray--Hirsch comparison is an isomorphism in that degree.

The proof uses the actual product projections and the original pair
sequence. It retains all low degrees of the shifted cochain complexes,
including zero summands below their shift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] {ι : Type u} [Fintype ι]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open scoped Classical in
/-- A relative top summand extends a subspace Leray--Hirsch basis to the ambient space. -/
theorem homologyMap_singularCohomologyLerayHirschMap_bijective_of_relative
    (π : C(Y, X)) (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (A : Set Y) (i₀ : ι) (n : ℕ) :
    let C (i : ι) : CochainComplex (ModuleCat.{u} R) ℕ := (singularCochains R X).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))
    let I₀ := {i : ι // i ≠ i₀}
    let old := singularCohomologyLerayHirschMap R π
      (fun i : I₀ ↦ d i.val) (fun i ↦ c i.val)
    (∀ k : ℕ, Function.Bijective (fun a : (cochainFamilyProduct R
        (fun i : I₀ ↦ C i.val)).homology k ↦
      singularCohomologyPullback R (ContinuousMap.subtypeVal A) k (homologyMap old k a))) →
    ∀ g : (C i₀).homology n ⟶ relativeSingularCohomology R A n,
      Function.Bijective g →
      (∀ a : (C i₀).homology n,
        homologyMap
          (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
              (ComplexShape.embeddingUp'Add (1 : ℕ) (d i₀)) ≫
            singularCochainCupMap R Y (d i₀) (c i₀)) n a =
          relativeSingularCohomologyToOrdinary R A n (g a)) →
      Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R π d c) n) := by
  classical
  intro C I₀ old hOld g hg htop
  let fOld (k : ℕ) : (cochainFamilyProduct R (fun i : I₀ ↦ C i.val)).homology k ⟶
      singularCohomology R Y k := homologyMap old k
  let P (a : (cochainFamilyProduct R C).homology n) : ∀ i, (C i).homology n :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R C i) n a
  let Q (a : (cochainFamilyProduct R (fun i : I₀ ↦ C i.val)).homology n) :
      ∀ i : I₀, (C i.val).homology n :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R (fun i : I₀ ↦ C i.val) i) n a
  have hP : Function.Bijective P := bijective_homologyMap_cochainFamilyProductProjection R C n
  have hQ : Function.Bijective Q :=
    bijective_homologyMap_cochainFamilyProductProjection R (fun i : I₀ ↦ C i.val) n
  let q (a : (cochainFamilyProduct R C).homology n) :=
    (hQ.surjective (fun i : I₀ ↦ P a i.val)).choose
  have hq (a : (cochainFamilyProduct R C).homology n) (i : I₀) : Q (q a) i = P a i.val :=
    congrFun (hQ.surjective (fun i : I₀ ↦ P a i.val)).choose_spec i
  let split (a : (cochainFamilyProduct R C).homology n) := (q a, P a i₀)
  -- Products commute with homology, including the empty complementary family.
  have hsplit : Function.Bijective split := by
    constructor
    · intro a b hab
      apply hP.injective
      funext i
      by_cases hi : i = i₀
      · subst i
        exact congrArg Prod.snd hab
      · have hqeq : q a = q b := congrArg Prod.fst hab
        exact (hq a ⟨i, hi⟩).symm.trans
          ((congrArg (fun z ↦ Q z ⟨i, hi⟩) hqeq).trans (hq b ⟨i, hi⟩))
    · rintro ⟨b, t⟩
      let v (i : ι) : (C i).homology n := by
        by_cases hi : i = i₀
        · subst i
          exact t
        · exact Q b ⟨i, hi⟩
      obtain ⟨a, ha⟩ := hP.surjective v
      refine ⟨a, Prod.ext ?_ ?_⟩
      · apply hQ.injective
        funext i
        rw [hq, congrFun ha i.val]
        exact dite_eq_right i.property
      · change P a i₀ = t
        rw [congrFun ha i₀]
        exact dite_eq_left rfl
  let F (i : ι) : (C i).homology n ⟶ singularCohomology R Y n := homologyMap
    (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫
      singularCochainCupMap R Y (d i) (c i)) n
  have hsum (a : (cochainFamilyProduct R C).homology n) :
      homologyMap (singularCohomologyLerayHirschMap R π d c) n a =
        fOld n (q a) + F i₀ (P a i₀) := by
    have hfull := homologyMap_singularCohomologyLerayHirschMap R π d c n a
    change homologyMap (singularCohomologyLerayHirschMap R π d c) n a =
      ∑ i, F i (P a i) at hfull
    have hold := homologyMap_singularCohomologyLerayHirschMap R π
      (fun i : I₀ ↦ d i.val) (fun i ↦ c i.val) n (q a)
    change fOld n (q a) = ∑ i : I₀, F i.val (Q (q a) i) at hold
    simp only [hq] at hold
    have hsub : (∑ i ∈ Finset.univ.erase i₀, F i (P a i)) =
        ∑ i : I₀, F i.val (P a i.val) :=
      Finset.sum_subtype (Finset.univ.erase i₀) (by intro i; simp) (fun i ↦ F i (P a i))
    have herase := Finset.sum_erase_add Finset.univ (fun i ↦ F i (P a i))
      (Finset.mem_univ i₀)
    exact hfull.trans (herase.symm.trans
      (congrArg (fun z ↦ z + F i₀ (P a i₀)) (hsub.trans hold.symm)))
  -- Apply the split pair sequence with the original lower comparison as its chosen lift.
  have hb := singularCohomology_split_bijective R A
    (fun k ↦ (cochainFamilyProduct R (fun i : I₀ ↦ C i.val)).homology k)
    fOld hOld n
  have hprod : Function.Bijective
      (fun a : (cochainFamilyProduct R (fun i : I₀ ↦ C i.val)).homology n ×
        (C i₀).homology n ↦ (a.1, g a.2)) := Function.bijective_id.prodMap hg
  have hcomp := hb.comp (hprod.comp hsplit)
  have hformula (a : (cochainFamilyProduct R C).homology n) :
      homologyMap (singularCohomologyLerayHirschMap R π d c) n a =
        fOld n (q a) + relativeSingularCohomologyToOrdinary R A n (g (P a i₀)) := by
    have htop' : F i₀ (P a i₀) = relativeSingularCohomologyToOrdinary R A n (g (P a i₀)) :=
      htop (P a i₀)
    exact (hsum a).trans (congrArg (fun z ↦ fOld n (q a) + z) htop')
  exact (congrArg Function.Bijective (funext hformula)).mpr hcomp

end AtiyahSinger
