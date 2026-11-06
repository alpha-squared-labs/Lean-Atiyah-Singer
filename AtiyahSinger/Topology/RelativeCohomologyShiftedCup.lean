/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyCup
public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch

/-!
# Relative cup isomorphisms on the full shifted source

Public module ID: M2071.

A relative class giving the original pullback-cup isomorphism in every
supported degree identifies the full shifted source with relative cohomology,
provided the relative groups vanish below the shift. The shifted source also
vanishes there. Its ordinary image is the same specified Leray--Hirsch summand,
with the original cocycle and relative-to-ordinary map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- With lower-degree vanishing, relative cup isomorphisms supply
the same full shifted Leray--Hirsch summand. -/
theorem exists_relativeSingularCohomologyShiftedCupEquiv
    (π : C(Y, X)) (A : Set Y) (r : ℕ) (c : singularCocycles R Y r)
    (τ : relativeSingularCohomology R A r)
    (hτ : relativeSingularCohomologyToOrdinary R A r τ = singularCocycleClass R Y r c)
    (hbij : ∀ p : ℕ, Function.Bijective (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R A p r (singularCohomologyPullback R π p a) τ))
    (hvan : ∀ k : ℕ, k < r → Subsingleton (relativeSingularCohomology R A k)) (n : ℕ) :
    ∃ g : ((singularCochains R X).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) r)).homology n ⟶
          relativeSingularCohomology R A n,
      Function.Bijective g ∧
      ∀ a, homologyMap
          (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
              (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ singularCochainCupMap R Y r c) n a =
        relativeSingularCohomologyToOrdinary R A n (g a) := by
  let C := singularCochains R X
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    let J := C.extendHomologyIso e (j := p) rfl
    let f : singularCohomology R X p →ₗ[R] relativeSingularCohomology R A (p + r) :=
      ((relativeSingularCohomologyAction R A p r).flip τ).comp
        (singularCohomologyPullback R π p).hom
    let g := J.hom ≫ ModuleCat.ofHom f
    have hg : Function.Bijective g := (hbij p).comp (ConcreteCategory.bijective_of_isIso J.hom)
    refine ⟨g, hg, ?_⟩
    intro a
    -- The supported-degree cochain formula and relative cup have the same two factors.
    have h := homologyMap_pullback_singularCochainCupMap R π r c p (J.hom a)
    rw [Iso.hom_inv_id_apply] at h
    have hrel := relativeSingularCohomologyToOrdinary_action R A p r
      (singularCohomologyPullback R π p (J.hom a)) τ
    rw [hτ] at hrel
    exact h.trans hrel.symm
  · -- The full source and relative target vanish below the shift; no truncation is introduced.
    have hsource : Subsingleton ((C.extend e).homology n) := by
      apply ModuleCat.isZero_iff_subsingleton.mp
      apply ((C.extend e).exactAt_iff_isZero_homology n).mp
      apply C.extend_exactAt e n
      intro p hp
      change p + r = n at hp
      omega
    let := hsource
    let := hvan n (Nat.lt_of_not_ge hn)
    let g : (C.extend e).homology n ⟶ relativeSingularCohomology R A n := 0
    refine ⟨g, ⟨fun a b _ ↦ Subsingleton.elim a b, fun b ↦ ⟨0, Subsingleton.elim _ _⟩⟩, ?_⟩
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero, map_zero, map_zero]

end AtiyahSinger
