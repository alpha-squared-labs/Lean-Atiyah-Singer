/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch
public import AtiyahSinger.Topology.SingularCohomologyPowerCombination

/-!
# Degreewise coefficients from the cochain Leray--Hirsch comparison

Public module ID: M2137.

When all specified powers occur in the requested even degree, the shifted
cochain source has precisely the usual tuple of homogeneous coefficient
groups. The actual product projections and shift isomorphisms identify its
homology with that tuple. The original pullback-cup formula then identifies
the cochain comparison with the ordinary homogeneous power combination.

The finite index is explicitly universe-lifted only inside the cochain
product. The coefficient tuple uses the ordinary type `Fin r`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

set_option maxHeartbeats 600000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual cochain comparison gives unique ordinary homogeneous power coefficients. -/
theorem singularCohomologyPowerCombination_bijective_of_lerayHirsch
    (π : C(Y, X)) (t : singularCohomology R Y 2)
    (r n : ℕ) (hn : ∀ i : Fin r, i.val ≤ n)
    (c : ∀ i : ULift.{u} (Fin r), singularCocycles R Y (2 * i.down.val))
    (hc : ∀ i : ULift.{u} (Fin r), singularCocycleClass R Y (2 * i.down.val) (c i) =
      singularCohomologyDegreeTwoPow R Y t i.down.val)
    (hLH : Function.Bijective (homologyMap
      (singularCohomologyLerayHirschMap R π (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) c)
        (2 * n))) :
    Function.Bijective (singularCohomologyPowerCombination R π t r n hn) := by
  classical
  let I := ULift.{u} (Fin r)
  let C (i : I) : CochainComplex (ModuleCat.{u} R) ℕ :=
    (singularCochains R X).extend (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * i.down.val))
  have hdeg (i : Fin r) : 2 * (n - i.val) + 2 * i.val = 2 * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (hn i)]
  let J (i : Fin r) : (C (ULift.up i)).homology (2 * n) ≅
      singularCohomology R X (2 * (n - i.val)) :=
    (singularCochains R X).extendHomologyIso
      (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * i.val)) (hdeg i)
  let P (a : (cochainFamilyProduct R C).homology (2 * n)) (i : Fin r) :=
    (J i).hom (homologyMap (cochainFamilyProductProjection R C (ULift.up i)) (2 * n) a)
  have hprod := bijective_homologyMap_cochainFamilyProductProjection R C (2 * n)
  -- The shift isomorphisms give exactly the prescribed homogeneous coefficient groups.
  have hP : Function.Bijective P := by
    constructor
    · intro a b hab
      apply hprod.injective
      funext i
      apply (ConcreteCategory.bijective_of_isIso (J i.down).hom).injective
      exact congrFun hab i.down
    · intro b
      obtain ⟨a, ha⟩ := hprod.surjective (fun i : I ↦ (J i.down).inv (b i.down))
      refine ⟨a, ?_⟩
      funext i
      change (J i).hom
        (homologyMap (cochainFamilyProductProjection R C (ULift.up i)) (2 * n) a) = b i
      have hai : homologyMap (cochainFamilyProductProjection R C (ULift.up i)) (2 * n) a =
          (J i).inv (b i) := congrFun ha (ULift.up i)
      exact (congrArg (J i).hom hai).trans (Iso.inv_hom_id_apply (J i) (b i))
  have hsupported (p q k : ℕ) (hk : p + q = k) (z : singularCocycles R Y q)
      (a : ((singularCochains R X).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) q)).homology k) :
      homologyMap
        (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
            (ComplexShape.embeddingUp'Add (1 : ℕ) q) ≫ singularCochainCupMap R Y q z) k a =
        (eqToIso (congrArg (fun j ↦ singularCohomology R Y j) hk)).hom
          (singularCohomologyCup R Y p q
            (singularCohomologyPullback R π p
              (((singularCochains R X).extendHomologyIso
                (ComplexShape.embeddingUp'Add (1 : ℕ) q) hk).hom a))
            (singularCocycleClass R Y q z)) := by
    subst k
    let H := (singularCochains R X).extendHomologyIso
      (ComplexShape.embeddingUp'Add (1 : ℕ) q) (j := p) rfl
    have h := homologyMap_pullback_singularCochainCupMap R π q z p (H.hom a)
    rw [Iso.hom_inv_id_apply] at h
    exact h
  have hcast (p q k : ℕ) (hk : p + q = k)
      (x : singularCohomology R Y (2 * p)) (y : singularCohomology R Y (2 * q)) :
      (eqToIso (congrArg (fun j ↦ singularCohomology R Y j)
        ((Nat.mul_add 2 p q).symm.trans (congrArg (2 * ·) hk)))).hom
          (singularCohomologyCup R Y (2 * p) (2 * q) x y) =
        (eqToIso (congrArg (fun j ↦ singularCohomology R Y (2 * j)) hk)).hom
          (singularCohomologyEvenCup R Y p q x y) := by
    subst k
    rfl
  let F := singularCohomologyLerayHirschMap R π (fun i : I ↦ 2 * i.down.val) c
  have hformula (a : (cochainFamilyProduct R C).homology (2 * n)) :
      homologyMap F (2 * n) a = singularCohomologyPowerCombination R π t r n hn (P a) := by
    have hfull := homologyMap_singularCohomologyLerayHirschMap R π
      (fun i : I ↦ 2 * i.down.val) c (2 * n) a
    rw [singularCohomologyPowerCombination_apply]
    apply hfull.trans
    apply Fintype.sum_equiv (Equiv.ulift : I ≃ Fin r)
    rintro ⟨i⟩
    have h := hsupported (2 * (n - i.val)) (2 * i.val) (2 * n)
      (hdeg i) (c (ULift.up i))
      (homologyMap (cochainFamilyProductProjection R C (ULift.up i)) (2 * n) a)
    rw [hc (ULift.up i)] at h
    have he := hcast (n - i.val) i.val n (Nat.sub_add_cancel (hn i))
      (singularCohomologyPullback R π (2 * (n - i.val)) (P a i))
      (singularCohomologyDegreeTwoPow R Y t i.val)
    dsimp only [P, J] at he
    have hf := h.trans he
    convert hf using 1
    dsimp only [Equiv.ulift, P, J]
    rfl
  constructor
  · -- Injectivity of the same cochain comparison makes the coefficients unique.
    intro a b hab
    obtain ⟨x, rfl⟩ := hP.surjective a
    obtain ⟨y, rfl⟩ := hP.surjective b
    exact congrArg P (hLH.injective ((hformula x).trans (hab.trans (hformula y).symm)))
  · intro b
    obtain ⟨a, ha⟩ := hLH.surjective b
    exact ⟨P a, (hformula a).symm.trans ha⟩

end AtiyahSinger
