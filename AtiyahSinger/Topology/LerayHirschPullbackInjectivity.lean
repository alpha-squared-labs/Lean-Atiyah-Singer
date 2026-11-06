/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch

/-!
# Pullback injectivity from the unit summand of Leray--Hirsch

Public module ID: M1930.

An injective finite Leray--Hirsch comparison makes its actual unit summand
injective. The degree-zero shift identifies that summand with pullback on
the original cohomology. A specified index of degree zero is necessary;
the assertion does not apply to an empty family.
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
/-- An actual unit class among an injective Leray--Hirsch family makes pullback injective. -/
theorem singularCohomologyPullback_injective_of_lerayHirsch
    (p : C(Y, X)) (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (i₀ : ι) (hd : d i₀ = 0)
    (hc : singularCocycleClass R Y 0 (hd ▸ c i₀) = singularCohomologyOne R Y)
    (n : ℕ)
    (h : Function.Injective (homologyMap (singularCohomologyLerayHirschMap R p d c) n)) :
    Function.Injective (singularCohomologyPullback R p n) := by
  classical
  let C (i : ι) : CochainComplex (ModuleCat.{u} R) ℕ := (singularCochains R X).extend
    (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))
  let P (a : (cochainFamilyProduct R C).homology n) : ∀ i, (C i).homology n :=
    fun i ↦ homologyMap (cochainFamilyProductProjection R C i) n a
  let F (i : ι) : (C i).homology n ⟶ singularCohomology R Y n := homologyMap
    (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom p).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫
      singularCochainCupMap R Y (d i) (c i)) n
  have hP : Function.Bijective P := bijective_homologyMap_cochainFamilyProductProjection R C n
  -- Embed one original component in the actual product cohomology, with every other class zero.
  let v (a : (C i₀).homology n) (i : ι) : (C i).homology n :=
    if hi : i = i₀ then hi ▸ a else 0
  let lift (a : (C i₀).homology n) : (cochainFamilyProduct R C).homology n :=
    (hP.surjective (v a)).choose
  have hlift (a : (C i₀).homology n) (i : ι) : P (lift a) i = v a i :=
    congrFun (hP.surjective (v a)).choose_spec i
  have hsum (a : (C i₀).homology n) :
      homologyMap (singularCohomologyLerayHirschMap R p d c) n (lift a) = F i₀ a := by
    rw [homologyMap_singularCohomologyLerayHirschMap]
    change (∑ i, F i (P (lift a) i)) = F i₀ a
    rw [Finset.sum_eq_single i₀]
    · rw [hlift]
      simp [v]
    · intro i _ hi
      rw [hlift]
      simp only [v, dite_eq_right hi, map_zero]
    · simp
  have hF : Function.Injective (F i₀) := by
    intro a b hab
    have heq : lift a = lift b := h ((hsum a).trans (hab.trans (hsum b).symm))
    have hcomponent := congrArg (fun z ↦ P z i₀) heq
    rw [hlift, hlift] at hcomponent
    simpa [v] using hcomponent
  -- The chosen degree-zero summand is the original pullback followed by cup with one.
  have hunit (r : ℕ) (c₀ : singularCocycles R Y r) (hr : r = 0)
      (hclass : singularCocycleClass R Y 0 (hr ▸ c₀) = singularCohomologyOne R Y)
      (hinj : Function.Injective (homologyMap
        (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom p).op)
            (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
          singularCochainCupMap R Y r c₀) n)) :
      Function.Injective (singularCohomologyPullback R p n) := by
    subst r
    let J := (singularCochains R X).extendHomologyIso
      (ComplexShape.embeddingUp'Add (1 : ℕ) 0) (j := n) rfl
    intro a b hab
    have ha := homologyMap_pullback_singularCochainCupMap R p 0 c₀ n a
    have hb := homologyMap_pullback_singularCochainCupMap R p 0 c₀ n b
    rw [hclass, singularCohomologyCup_one] at ha hb
    have heq : J.inv a = J.inv b := hinj (ha.trans (hab.trans hb.symm))
    exact (ConcreteCategory.bijective_of_isIso J.inv).injective heq
  exact hunit (d i₀) (c i₀) hd hc hF

end AtiyahSinger
