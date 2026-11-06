/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Reduced cohomology and the original relative group at a specified point

Public module ID: M1990.

Reduced singular cohomology of a pointed space is the kernel of restriction along the actual
map from a point. The canonical map from H^n(X,{x₀};R) is the original map
forgetting the relative condition, with its codomain restricted to this
kernel. The split point inclusion makes precisely this map bijective.

Sources: Hatcher, Algebraic Topology, Section 3.1, the cohomology sequence of
a pair and reduced cohomology. The split point-pair formulation below is
the immediate standard consequence of that sequence. It uses neither a
cofibration hypothesis on {x₀} nor a comparison with a quotient space.
In degree zero the kernel removes the constant summand; no connectedness
or positive-degree hypothesis is imposed. No one-point compactification
comparison is supplied by this module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- Reduced cohomology is the kernel of restriction along the specified point inclusion. -/
def reducedSingularCohomology (x₀ : X) (n : ℕ) :
    Submodule R (singularCohomology R X n) :=
  (singularCohomologyPullback R (ContinuousMap.const PUnit.{u + 1} x₀) n).hom.ker

/-- The original relative-to-ordinary map has zero restriction to its specified base point. -/
theorem pointRelativeCohomologyToOrdinary_mem_reduced (x₀ : X) (n : ℕ)
    (a : relativeSingularCohomology R ({x₀} : Set X) n) :
    relativeSingularCohomologyToOrdinary R ({x₀} : Set X) n a ∈
      reducedSingularCohomology R x₀ n := by
  /- Stage 1: factor the constant map from PUnit through the actual singleton
  subspace {x₀}. The composite of its chain inclusion with the relative
  quotient projection is zero by the defining cokernel relation.
  Stage 2: dualize this same zero composite and take degree-n cohomology.
  The resulting identity says exactly that the displayed ordinary class
  pulls back to zero along the specified PUnit point inclusion. This is
  membership in the actual kernel above, without computing point cohomology. -/
  have : (singularCochainDualFunctor.{u} R).Additive := by
    change (((((linearYoneda R (ModuleCat.{u} R)).obj
      (singularCoefficient R)).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).op) ⋙
        HomologicalComplex.unopFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)).Additive
    infer_instance
  let F := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  let p : C(PUnit.{u + 1}, ({x₀} : Set X)) :=
    ContinuousMap.const _ ⟨x₀, Set.mem_singleton x₀⟩
  -- The specified point inclusion factors through the actual singleton chain inclusion.
  have hpoint : (singularChainsFunctor R).map
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)) =
      (singularChainsFunctor R).map (TopCat.ofHom p) ≫
        singularSubspaceChains R ({x₀} : Set X) := by
    rw [singularSubspaceChains, ← CategoryTheory.Functor.map_comp]
    rfl
  have hzero : (singularChainsFunctor R).map
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)) ≫
      relativeSingularChainsProjection R ({x₀} : Set X) = 0 := by
    rw [hpoint, Category.assoc, cokernel.condition, comp_zero]
  -- Dualization and homology carry that same zero composite to point evaluation.
  have hcohom : relativeSingularCohomologyToOrdinary R ({x₀} : Set X) n ≫
      singularCohomologyPullback R (ContinuousMap.const PUnit.{u + 1} x₀) n = 0 := by
    change F.map (relativeSingularChainsProjection R ({x₀} : Set X)).op ≫
      F.map ((singularChainsFunctor R).map
        (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀))).op = 0
    rw [← F.map_comp, ← op_comp, hzero, op_zero, F.map_zero]
  exact congrArg (fun f ↦ f a) hcohom

/-- The canonical point-relative comparison, obtained by restricting the original map's range. -/
def pointRelativeCohomologyToReduced (x₀ : X) (n : ℕ) :
    relativeSingularCohomology R ({x₀} : Set X) n →ₗ[R]
      reducedSingularCohomology R x₀ n :=
  (relativeSingularCohomologyToOrdinary R ({x₀} : Set X) n).hom.codRestrict
    (reducedSingularCohomology R x₀ n)
    (pointRelativeCohomologyToOrdinary_mem_reduced R x₀ n)

/-- The split point inclusion identifies its relative cohomology with this actual kernel. -/
theorem pointRelativeCohomologyToReduced_bijective (x₀ : X) (n : ℕ) :
    Function.Bijective (pointRelativeCohomologyToReduced R x₀ n) := by
  /- Stage 1: the inclusion of the actual singleton subspace into X admits
  the continuous constant retraction. Its restriction on cohomology is
  therefore split surjective in every degree. Identifying the singleton
  with PUnit gives precisely the point-evaluation map used above.
  Stage 2: split the actual chain cokernel sequence using this retraction.
  Taking its opposite and applying additive dualization and degree-n
  homology preserves the splitting, without a general long exact sequence.
  Stage 3: the resulting split injection is the original relative-to-
  ordinary map. The splitting identity explicitly supplies every class
  in the point-evaluation kernel as its image. This includes degree zero,
  so no reduced negative-degree group is used. This argument
  applies over every commutative R, including the zero ring, and requires
  no separation, local contractibility, cofibration or compactness of X. -/
  have : (singularCochainDualFunctor.{u} R).Additive := by
    change (((((linearYoneda R (ModuleCat.{u} R)).obj
      (singularCoefficient R)).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).op) ⋙
        HomologicalComplex.unopFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)).Additive
    infer_instance
  let F := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  let i := singularSubspaceChains R ({x₀} : Set X)
  let r := (singularChainsFunctor R).map
    (TopCat.ofHom (ContinuousMap.const X (⟨x₀, Set.mem_singleton x₀⟩ : ({x₀} : Set X))))
  -- Constant retraction splits the original singleton inclusion already on chains.
  have hir : i ≫ r = 𝟙 _ := by
    change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ = _
    rw [← Functor.map_comp]
    have htop : TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(({x₀} : Set X), X)) ≫
        TopCat.ofHom (ContinuousMap.const X
          (⟨x₀, Set.mem_singleton x₀⟩ : ({x₀} : Set X))) =
        𝟙 (TopCat.of ({x₀} : Set X)) := by
      ext a
      exact (Set.mem_singleton_iff.mp a.property).symm
    rw [htop, CategoryTheory.Functor.map_id]
  let S := ShortComplex.cokernelSequence i
  let splitting := ShortComplex.Splitting.ofExactOfRetraction S
    (ShortComplex.cokernelSequence_exact i) r hir inferInstance
  -- Any additive functor preserves a splitting, including dualization followed by homology.
  let T := S.op.map F
  let splitting' : T.Splitting := splitting.op.map F
  have hmono : Function.Injective T.f :=
    (ModuleCat.mono_iff_injective T.f).mp splitting'.mono_f
  constructor
  · intro a b hab
    apply hmono
    exact congrArg Subtype.val hab
  · intro b
    -- The singleton inclusion factors back through precisely the PUnit point used in the kernel.
    let c : C(({x₀} : Set X), PUnit.{u + 1}) := ContinuousMap.const _ PUnit.unit
    have hfactor : i = (singularChainsFunctor R).map (TopCat.ofHom c) ≫
        (singularChainsFunctor R).map
          (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)) := by
      rw [← Functor.map_comp]
      apply congrArg ((singularChainsFunctor R).map)
      ext a
      exact Set.mem_singleton_iff.mp a.property
    have hrestrict : T.g b.val = 0 := by
      have hp : singularCohomologyPullback R
          (ContinuousMap.const PUnit.{u + 1} x₀) n b.val = 0 := b.property
      change F.map i.op b.val = 0
      rw [hfactor, op_comp, F.map_comp]
      change F.map ((singularChainsFunctor R).map (TopCat.ofHom c)).op
        (singularCohomologyPullback R (ContinuousMap.const PUnit.{u + 1} x₀) n b.val) = 0
      rw [hp, map_zero]
    -- The splitting identity gives an explicit preimage under the original forgetful map.
    refine ⟨splitting'.r b.val, ?_⟩
    apply Subtype.ext
    have hid := congrArg (fun f ↦ f b.val) splitting'.id
    change T.f (splitting'.r b.val) + splitting'.s (T.g b.val) = b.val at hid
    rw [hrestrict, map_zero, add_zero] at hid
    exact hid

/-- The equivalence whose forward map is the original point-relative comparison. -/
def pointRelativeCohomologyEquivReduced (x₀ : X) (n : ℕ) :
    relativeSingularCohomology R ({x₀} : Set X) n ≃ₗ[R]
      reducedSingularCohomology R x₀ n :=
  LinearEquiv.ofBijective (pointRelativeCohomologyToReduced R x₀ n)
    (pointRelativeCohomologyToReduced_bijective R x₀ n)

end AtiyahSinger
