/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomology
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Small singular chains for an open cover

Public module ID: M2153.

The small simplicial subset consists of the original singular simplices whose
entire image lies in one member of the given family. Its chain complex is
mathlib's original free singular-simplex complex restricted to this subset.
The inclusion below therefore keeps the original generators and boundary.

This is the small-chain construction used in singular excision, as in
Hatcher, Algebraic Topology, Section 2.1. The open-cover homotopy
equivalence is established in SingularSmallChainsHomotopy.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The original singular simplices lying in one member of the specified family. -/
def smallSingularSet (𝒰 : Set (Set X)) : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex where
  obj n := {σ | ∃ U ∈ 𝒰, Set.range ((TopCat.of X).toSSetObjEquiv n σ) ⊆ U}
  map {m n} f := by
    rintro σ ⟨U, hU, hσ⟩
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨t, rfl⟩
    apply hσ
    exact ⟨t.map f.unop.toOrderHom, rfl⟩

/-- Small chains use the actual simplicial chain functor and the original coefficient module. -/
abbrev smallSingularChains (R : Type) [CommRing R] (𝒰 : Set (Set X)) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (smallSingularSet 𝒰).toSSet.chainComplex (singularCoefficient R)

/-- The actual inclusion of the small singular-simplex generators. -/
def smallSingularChainsInclusion (R : Type) [CommRing R] (𝒰 : Set (Set X)) :
    smallSingularChains R 𝒰 ⟶ singularChains R X :=
  SSet.chainComplexMap (smallSingularSet 𝒰).ι (singularCoefficient R)

/-- Small-chain inclusion is split in each degree by retaining exactly the small generators. -/
theorem isSplitMono_smallSingularChainsInclusion
    (R : Type) [CommRing R] (𝒰 : Set (Set X)) (n : ℕ) :
    IsSplitMono ((smallSingularChainsInclusion R 𝒰).f n) := by
  classical
  let r : (singularChains R X).X n ⟶ (smallSingularChains R 𝒰).X n :=
    Sigma.desc fun σ ↦
      if h : σ ∈ (smallSingularSet 𝒰).obj (op ⦋n⦌) then
        (smallSingularSet 𝒰).toSSet.ιChainComplex ⟨σ, h⟩ else 0
  refine ⟨⟨r, ?_⟩⟩
  -- The inclusion takes each small generator to that identical original simplex.
  apply SSet.chainComplex_hom_ext
  intro σ
  change (smallSingularSet 𝒰).toSSet.ιChainComplex σ ≫
      (SSet.chainComplexMap (smallSingularSet 𝒰).ι (singularCoefficient R)).f n ≫ r = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp [SSet.ιChainComplex, σ.property]

/-- An injective continuous map embeds the original simplex generators and therefore induces
split injections on singular chains in each degree. -/
theorem isSplitMono_singularChainsMap_of_injective
    (R : Type) [CommRing R] {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Function.Injective f) (n : ℕ) :
    IsSplitMono (((singularChainsFunctor R).map (TopCat.ofHom f)).f n) := by
  classical
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  have hg : Function.Injective (g.app (op ⦋n⦌)) := by
    intro σ τ h
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro t
    apply hf
    exact congrArg (fun η ↦ TopCat.toSSetObjEquiv (TopCat.of Y) (op ⦋n⦌) η t) h
  let r : (singularChains R Y).X n ⟶ (singularChains R X).X n :=
    Sigma.desc fun τ ↦
      if h : τ ∈ Set.range (g.app (op ⦋n⦌)) then
        (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex h.choose else 0
  refine ⟨⟨r, ?_⟩⟩
  apply SSet.chainComplex_hom_ext
  intro σ
  change (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
      (SSet.chainComplexMap g (singularCoefficient R)).f n ≫ r = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  have hmem : g.app (op ⦋n⦌) σ ∈ Set.range (g.app (op ⦋n⦌)) := ⟨σ, rfl⟩
  have hchoose : hmem.choose = σ := hg hmem.choose_spec
  simp only [SSet.ιChainComplex, colimit.ι_desc, Cofan.mk_pt,
    Cofan.mk_ι_app, hmem, ↓reduceDIte, hchoose]
  exact (Category.comp_id _).symm

end AtiyahSinger
