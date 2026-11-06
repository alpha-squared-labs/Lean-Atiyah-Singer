/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyLerayHirsch

/-!
# Reindexing and representative independence of the Leray--Hirsch comparison

Public module ID: M2133.

The finite comparison depends on the ordered family of cohomology classes,
up to reindexing of its source factors. This allows a lower projective basis
to be used as the complementary summands in the pair exact sequence, without
requiring unrelated choices of cocycle representatives to coincide.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] {ι κ : Type u} [Fintype ι] [Fintype κ]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Reindexing the same finite family preserves the original Leray--Hirsch bijection. -/
theorem homologyMap_singularCohomologyLerayHirschMap_bijective_reindex
    (π : C(Y, X)) (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (e : κ ≃ ι) (n : ℕ)
    (h : Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R π d c) n)) :
    Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R π
      (fun j ↦ d (e j)) (fun j ↦ c (e j))) n) := by
  classical
  let C (i : ι) : CochainComplex (ModuleCat.{u} R) ℕ := (singularCochains R X).extend
    (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))
  let P := cochainFamilyProductMap R (C := C) (D := fun j ↦ C (e j)) e (fun _ ↦ 𝟙 _)
  -- Each degree map is the literal reindexing equivalence of dependent tuples.
  have hP (q : ℕ) : IsIso (P.f q) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact (LinearEquiv.piCongrLeft R (fun i ↦ (C i).X q) e).symm.bijective
  let : ∀ q, IsIso (P.f q) := hP
  let : IsIso P := HomologicalComplex.Hom.isIso_of_components P
  have hproj (j : κ) : P ≫ cochainFamilyProductProjection R (fun j ↦ C (e j)) j =
      cochainFamilyProductProjection R C (e j) := by
    ext q a
    rfl
  have hmap : P ≫ singularCohomologyLerayHirschMap R π
      (fun j ↦ d (e j)) (fun j ↦ c (e j)) =
      singularCohomologyLerayHirschMap R π d c := by
    let F (i : ι) : C i ⟶ singularCochains R Y :=
      extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫ singularCochainCupMap R Y (d i) (c i)
    change P ≫ (∑ j, cochainFamilyProductProjection R (fun j ↦ C (e j)) j ≫ F (e j)) =
      ∑ i, cochainFamilyProductProjection R C i ≫ F i
    rw [Preadditive.comp_sum]
    simp_rw [← Category.assoc, hproj]
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  have hhom := congrArg (fun f ↦ homologyMap f n) hmap
  rw [homologyMap_comp] at hhom
  -- The actual source isomorphism is cancelled only after its homology map is identified.
  apply (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso
    (homologyMap P n))).mp
  change Function.Bijective (homologyMap P n ≫ homologyMap
    (singularCohomologyLerayHirschMap R π (fun j ↦ d (e j)) (fun j ↦ c (e j))) n)
  rw [hhom]
  exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original finite comparison on homology depends only on its specified cocycle classes. -/
theorem homologyMap_singularCohomologyLerayHirschMap_congr
    (π : C(Y, X)) (d : ι → ℕ) (c c' : ∀ i, singularCocycles R Y (d i))
    (hc : ∀ i, singularCocycleClass R Y (d i) (c i) =
      singularCocycleClass R Y (d i) (c' i)) (n : ℕ) :
    homologyMap (singularCohomologyLerayHirschMap R π d c) n =
      homologyMap (singularCohomologyLerayHirschMap R π d c') n := by
  classical
  have hsummand (i : ι) :
      homologyMap (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
          (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫
            singularCochainCupMap R Y (d i) (c i)) n =
        homologyMap (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom π).op)
          (ComplexShape.embeddingUp'Add (1 : ℕ) (d i)) ≫
            singularCochainCupMap R Y (d i) (c' i)) n := by
    let e := ComplexShape.embeddingUp'Add (1 : ℕ) (d i)
    by_cases hn : d i ≤ n
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + d i := ⟨n - d i, (Nat.sub_add_cancel hn).symm⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      let J := (singularCochains R X).extendHomologyIso e (j := p) rfl
      -- In the supported degree each summand is cup with precisely its cohomology class.
      have h₁ := homologyMap_pullback_singularCochainCupMap R π (d i) (c i) p (J.hom a)
      have h₂ := homologyMap_pullback_singularCochainCupMap R π (d i) (c' i) p (J.hom a)
      rw [Iso.hom_inv_id_apply] at h₁ h₂
      exact h₁.trans ((congrArg _ (hc i)).trans h₂.symm)
    · -- Below its shift the entire source homology is zero, independently of representatives.
      have hz : IsZero (((singularCochains R X).extend e).homology n) := by
        apply (exactAt_iff_isZero_homology _ _).mp
        exact extend_exactAt _ e n (by
          intro p hp
          change p + d i = n at hp
          omega)
      exact hz.eq_of_src _ _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rw [homologyMap_singularCohomologyLerayHirschMap,
    homologyMap_singularCohomologyLerayHirschMap]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsummand i]

end AtiyahSinger
