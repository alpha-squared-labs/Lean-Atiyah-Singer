/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Coefficients of the original relative singular chains

Public module ID: M2086.

The original degreewise cokernel is free on exactly those singular simplices
whose images are not contained in the relative subspace. The coordinate
equivalence below keeps each such simplex and its coefficient unchanged.
It supplies the chain-level comparison with locally finite coefficient
functions over a compact exhaustion, without changing the singular model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The actual relative chains in a fixed degree have their standard free simplex coordinates. -/
def relativeSingularChainCoordinates (A : Set X) (n : ℕ) :
    (relativeSingularChains R A).X n ≃ₗ[R]
      ({σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) //
        ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ A} →₀ R) := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  let P (σ : S.obj (op ⦋n⦌)) :=
    ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ A
  let α := {σ : S.obj (op ⦋n⦌) // P σ}
  let π := (relativeSingularChainsProjection R A).f n
  let gen (σ : S.obj (op ⦋n⦌)) : R →ₗ[R] (relativeSingularChains R A).X n :=
    π.hom.comp ((S.ιChainComplex (R := singularCoefficient R) σ).hom.comp
      (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toLinearMap)
  let encode : (singularChains R X).X n ⟶ ModuleCat.of R (α →₀ R) :=
    Sigma.desc fun σ ↦ if h : P σ then
      ModuleCat.ofHom ((Finsupp.lsingle ⟨σ, h⟩).comp
        (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap) else 0
  have hto (σ : S.obj (op ⦋n⦌)) (a : R) :
      encode (S.ιChainComplex (R := singularCoefficient R) σ (ULift.up a)) =
        if h : P σ then Finsupp.single ⟨σ, h⟩ a else 0 := by
    change (S.ιChainComplex σ ≫ encode) (ULift.up a) = _
    simp only [SSet.ιChainComplex, encode, Sigma.ι_comp_desc]
    split_ifs <;> rfl
  have hzero : (singularSubspaceChains R A).f n ≫ encode = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    let inc := TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
    have hcontained : ¬ P (inc.app (op ⦋n⦌) σ) := by
      intro h
      apply h
      rintro _ ⟨t, rfl⟩
      exact (((TopCat.of A).toSSetObjEquiv (op ⦋n⦌) σ) t).property
    change _ ≫ (SSet.chainComplexMap inc (singularCoefficient R)).f n ≫ encode = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    simp only [SSet.ιChainComplex, Sigma.ι_comp_desc, dite_eq_right hcontained]
    exact comp_zero.symm
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    (singularSubspaceChains R A)
  let desc := CokernelCofork.IsColimit.desc' Q encode hzero
  let forward : (relativeSingularChains R A).X n ⟶ ModuleCat.of R (α →₀ R) := desc.val
  have hforward : π ≫ forward = encode := desc.property
  let backward : (α →₀ R) →ₗ[R] (relativeSingularChains R A).X n :=
    Finsupp.lsum R (fun σ ↦ gen σ.val)
  have hvan (σ : S.obj (op ⦋n⦌)) (hσ : ¬ P σ) (a : R) : gen σ a = 0 := by
    -- A simplex lying in A lifts to the original subspace and is killed by its cokernel.
    have hcontained : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ A :=
      not_not.mp hσ
    let τ := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm
      (⟨fun t ↦ ⟨((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) t,
        hcontained ⟨t, rfl⟩⟩,
        (((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ).continuous).subtype_mk _⟩ :
          C(_, A))
    let inc := TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
    have hτ : inc.app (op ⦋n⦌) τ = σ := rfl
    have h := congrArg (fun F ↦ F.f n
      ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
        (R := singularCoefficient R) τ (ULift.up a)))
      (cokernel.condition (singularSubspaceChains R A))
    change π ((SSet.chainComplexMap inc (singularCoefficient R)).f n
      ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
        (R := singularCoefficient R) τ (ULift.up a))) = 0 at h
    change (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
      (R := singularCoefficient R) τ ≫
        (SSet.chainComplexMap inc (singularCoefficient R)).f n) ≫ π) (ULift.up a) = 0 at h
    rw [SSet.ι_chainComplexMap_f, hτ] at h
    exact h
  have hleft : forward ≫ ModuleCat.ofHom backward = 𝟙 _ := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hforward, Category.comp_id]
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change backward (encode
      (S.ιChainComplex (R := singularCoefficient R) σ (ULift.up a.down))) = gen σ a.down
    rw [hto]
    split_ifs with hσ
    · simp [backward]
    · rw [map_zero, hvan σ hσ]
  have hright : (ModuleCat.ofHom backward) ≫ forward = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro σ a
    change forward (backward (Finsupp.single σ a)) = Finsupp.single σ a
    simp only [backward, Finsupp.lsum_single]
    change (π ≫ forward) (S.ιChainComplex (R := singularCoefficient R) σ.val (ULift.up a)) = _
    rw [hforward, hto]
    simp only [σ.property, ↓reduceDIte]
    exact congrArg (fun τ : α ↦ Finsupp.single τ a) (Subtype.ext rfl)
  exact
    { toFun := forward
      invFun := backward
      left_inv x := congrArg (fun F ↦ F x) hleft
      right_inv x := congrArg (fun F ↦ F x) hright
      map_add' := forward.hom.map_add
      map_smul' := forward.hom.map_smul }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
/-- Coordinates of a projected original simplex retain its coefficient exactly when it survives. -/
theorem relativeSingularChainCoordinates_apply_generator (A : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : R) :
    relativeSingularChainCoordinates R A n
      ((relativeSingularChainsProjection R A).f n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) σ (ULift.up a))) =
      if h : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ A then
        Finsupp.single ⟨σ, h⟩ a else 0 := by
  classical
  let C := ModuleCat.of R
    ({τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) //
      ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) ⊆ A} →₀ R)
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    (singularSubspaceChains R A)
  change (show (relativeSingularChains R A).X n ⟶ C from
    (CokernelCofork.IsColimit.desc' Q _ _).val)
    ((relativeSingularChainsProjection R A).f n
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) σ (ULift.up a))) = _
  erw [← ModuleCat.comp_apply, (CokernelCofork.IsColimit.desc' Q _ _).property]
  change ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := singularCoefficient R) σ ≫ _) (ULift.up a) = _
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  split_ifs <;> rfl

/-- A singleton coordinate reconstructs the same original relative simplex. -/
theorem relativeSingularChainCoordinates_symm_single (A : Set X) (n : ℕ)
    (σ : {σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) //
      ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ A}) (a : R) :
    (relativeSingularChainCoordinates R A n).symm (Finsupp.single σ a) =
      (relativeSingularChainsProjection R A).f n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) σ.val (ULift.up a)) := by
  apply (relativeSingularChainCoordinates R A n).injective
  rw [LinearEquiv.apply_symm_apply, relativeSingularChainCoordinates_apply_generator]
  simp only [σ.property]
  rfl

/-- Enlarging the relative subspace simply discards the corresponding simplex coordinates. -/
theorem relativeSingularChainCoordinates_inclusion_apply
    (A B : Set X) (hAB : A ⊆ B) (n : ℕ)
    (c : (relativeSingularChains R A).X n)
    (σ : {σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) //
      ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ B}) :
    relativeSingularChainCoordinates R B n
      ((relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ hAB hx)).f n c) σ =
      relativeSingularChainCoordinates R A n c
        ⟨σ.val, fun h ↦ σ.property (h.trans hAB)⟩ := by
  classical
  let f := relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ hAB hx)
  have hp : relativeSingularChainsProjection R A ≫ f =
      relativeSingularChainsProjection R B := by
    simp [f, relativeSingularChainsMap, relativeSingularChainsProjection]
  obtain ⟨v, rfl⟩ := (relativeSingularChainCoordinates R A n).symm.surjective c
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hv hw
  | single τ a =>
    rw [relativeSingularChainCoordinates_symm_single]
    have hgen := congrArg (fun g ↦ g.f n
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) τ.val (ULift.up a))) hp
    change f.f n ((relativeSingularChainsProjection R A).f n
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) τ.val (ULift.up a))) = _ at hgen
    rw [hgen, relativeSingularChainCoordinates_apply_generator,
      relativeSingularChainCoordinates_apply_generator]
    by_cases hτ : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ.val) ⊆ B
    · simp [hτ, τ.property, Finsupp.single_apply, Subtype.ext_iff]
    · have hne : τ.val ≠ σ.val := by
        intro h
        exact hτ (h ▸ σ.property)
      simp [hτ, τ.property, Subtype.ext_iff, hne]

end AtiyahSinger
