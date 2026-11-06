/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import AtiyahSinger.Topology.SingularHomology

/-!
# Functoriality of the specified relative singular maps

Public module ID: M2091.

Composition and restriction commute for the actual quotient chain maps and
their cohomological pullbacks. These identities are used both in open extension
and in the comparison with one-point compactification. They do not assert
excision or replace a specified map by an abstract equivalence.

The proofs are the universal property of the original chain cokernel, followed
by the contravariant cochain functor and homology. This is the usual functoriality
of singular cohomology of pairs (Hatcher, section 3.1).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type) [CommRing R] {X Y Z : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Composition of the actual continuous pair maps induces composition on their quotients. -/
theorem relativeSingularChainsMap_comp (f : C(X, Y)) (g : C(Y, Z))
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativeSingularChainsMap R (g.comp f) (hg.comp hf) =
      relativeSingularChainsMap R f hf ≫ relativeSingularChainsMap R g hg := by
  -- The two maps agree after projection of every original singular chain.
  apply (cancel_epi (relativeSingularChainsProjection R A)).mp
  simp [relativeSingularChainsMap, relativeSingularChainsProjection,
    cokernel.map, Category.assoc, Functor.map_comp]

/-- The original relative cohomology pullback reverses composition of pair maps. -/
theorem relativeSingularCohomologyPullback_comp (f : C(X, Y)) (g : C(Y, Z))
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    relativeSingularCohomologyPullback R (g.comp f) (hg.comp hf) n =
      relativeSingularCohomologyPullback R g hg n ≫
        relativeSingularCohomologyPullback R f hf n := by
  let H := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  change H.map (relativeSingularChainsMap R (g.comp f) (hg.comp hf)).op =
    H.map (relativeSingularChainsMap R g hg).op ≫
      H.map (relativeSingularChainsMap R f hf).op
  rw [relativeSingularChainsMap_comp, op_comp, H.map_comp]

/-- Pullback commutes with restriction of the relative subspaces of a fixed map. -/
theorem relativeSingularCohomologyPullback_restriction (f : C(X, Y))
    {A A' : Set X} {B B' : Set Y} (hA : A ⊆ A') (hB : B ⊆ B')
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') (n : ℕ) :
    relativeSingularCohomologyRestriction R B B' hB n ≫
        relativeSingularCohomologyPullback R f hf n =
      relativeSingularCohomologyPullback R f hf' n ≫
        relativeSingularCohomologyRestriction R A A' hA n := by
  -- The square of the specified chain quotients commutes before taking duals.
  let p := relativeSingularChainsMap R f hf
  let p' := relativeSingularChainsMap R f hf'
  let iA := (relativeSingularChainsFunctor R X).map (homOfLE hA)
  let iB := (relativeSingularChainsFunctor R Y).map (homOfLE hB)
  have hsquare : p ≫ iB = iA ≫ p' := by
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    simp [p, p', iA, iB, relativeSingularChainsFunctor, relativeSingularChainsMap,
      relativeSingularChainsProjection, cokernel.map, Category.assoc]
  let H := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  change H.map iB.op ≫ H.map p.op = H.map p'.op ≫ H.map iA.op
  rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp, hsquare]

/-- Forgetting the relative condition is natural for the original pair pullback. -/
theorem relativeSingularCohomologyPullback_toOrdinary (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ) :
    relativeSingularCohomologyPullback R f hf n ≫
        relativeSingularCohomologyToOrdinary R A n =
      relativeSingularCohomologyToOrdinary R B n ≫ singularCohomologyPullback R f n := by
  -- Dualize the defining square between ordinary chains and their original quotients.
  have hsquare : relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
      (singularChainsFunctor R).map (TopCat.ofHom f) ≫
        relativeSingularChainsProjection R B := by
    simp [relativeSingularChainsMap, relativeSingularChainsProjection]
  let H := singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
  change H.map (relativeSingularChainsMap R f hf).op ≫
      H.map (relativeSingularChainsProjection R A).op =
    H.map (relativeSingularChainsProjection R B).op ≫
      H.map ((singularChainsFunctor R).map (TopCat.ofHom f)).op
  rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp, hsquare]

/-- Inclusion of the relative subspaces is natural for the original covariant homology maps. -/
theorem relativeSingularHomologyMap_inclusion (f : C(X, Y))
    {A A' : Set X} {B B' : Set Y} (hA : A ⊆ A') (hB : B ⊆ B')
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') (n : ℕ) :
    relativeSingularHomologyInclusion R A A' hA n ≫
        relativeSingularHomologyMap R f hf' n =
      relativeSingularHomologyMap R f hf n ≫
        relativeSingularHomologyInclusion R B B' hB n := by
  let p := relativeSingularChainsMap R f hf
  let p' := relativeSingularChainsMap R f hf'
  let iA := (relativeSingularChainsFunctor R X).map (homOfLE hA)
  let iB := (relativeSingularChainsFunctor R Y).map (homOfLE hB)
  -- Both routes are the same map on the original chain quotient projections.
  have hsquare : iA ≫ p' = p ≫ iB := by
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    simp [p, p', iA, iB, relativeSingularChainsFunctor, relativeSingularChainsMap,
      relativeSingularChainsProjection, cokernel.map, Category.assoc]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  change H.map iA ≫ H.map p' = H.map p ≫ H.map iB
  rw [← H.map_comp, ← H.map_comp, hsquare]

end AtiyahSinger
