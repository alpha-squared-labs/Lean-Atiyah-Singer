/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Relative singular cohomology on the actual quotient chain complex

Public module ID: M2087.

Relative singular cohomology as used in SG III.11–12 and in the
standard singular cochain construction (Hatcher, Algebraic Topology,
§3.1). For any subset A of X, the chain complex is the cokernel of
C_*(A;R) → C_*(X;R), using the actual subspace inclusion and the original
singular chain functor. Its algebraic dual gives relative cochains;
taking homology gives H^n(X,A;R). This is equivalently the usual
cochains that vanish on all singular chains lying in A, with their
original coboundary. No closedness or geometric condition on A is needed.

A continuous map f : X → Y carrying A into B induces the actual map
of chain quotients, and therefore the contravariant cohomology map.
For subsets of a fixed X, inclusion is carried by the very same
map-of-pairs construction with f = id. The subset functor supplies
identity and composition laws.

The canonical natural transformation to ordinary cohomology is the
dual of the original quotient projection. Its empty-subspace component
is the isomorphism used in the compact-space comparison downstream.
No pair long exact sequence, cup product or excision theorem is asserted
by merely defining these objects. The PR13 integral model is a source
of comparison only.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type) [CommRing R]

/-- The chain map induced by the actual inclusion of the subspace A into X. -/
def singularSubspaceChains {X : Type u} [TopologicalSpace X] (A : Set X) :
    singularChains R A ⟶ singularChains R X :=
  (singularChainsFunctor R).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

/-- The relative singular chains C_*(X,A;R), the cokernel of the subspace-chain inclusion. -/
abbrev relativeSingularChains {X : Type u} [TopologicalSpace X] (A : Set X) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  cokernel (singularSubspaceChains R A)

/-- The canonical projection from ordinary chains to relative chains. -/
abbrev relativeSingularChainsProjection {X : Type u} [TopologicalSpace X] (A : Set X) :
    singularChains R X ⟶ relativeSingularChains R A :=
  cokernel.π (singularSubspaceChains R A)

/-- The actual relative chain map induced by a specified continuous map of pairs. -/
def relativeSingularChainsMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    relativeSingularChains R A ⟶ relativeSingularChains R B :=
  cokernel.map (singularSubspaceChains R A) (singularSubspaceChains R B)
    ((singularChainsFunctor R).map (TopCat.ofHom
      ⟨fun a : A ↦ ⟨f a, hf a.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩))
    ((singularChainsFunctor R).map (TopCat.ofHom f)) (by
      simp only [singularSubspaceChains, ← Functor.map_comp]
      rfl)

/-- The relative chain functor for subsets of the same ambient space, ordered by inclusion. -/
abbrev relativeSingularChainsFunctor (X : Type u) [TopologicalSpace X] :
    Set X ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj A := relativeSingularChains R A
  map {A B} h := relativeSingularChainsMap R (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) A B from fun _ hx ↦ (leOfHom h) hx)
  map_id A := by
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    simp [relativeSingularChainsMap, relativeSingularChainsProjection]
  map_comp {A B D} h k := by
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    simp [relativeSingularChainsMap, relativeSingularChainsProjection, ← Category.assoc]

/-- Relative singular cochains, the algebraic dual of the actual relative chain quotient. -/
abbrev relativeSingularCochains {X : Type u} [TopologicalSpace X] (A : Set X) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (singularCochainDualFunctor R).obj (op (relativeSingularChains R A))

/-- Relative singular cohomology H^n(X,A;R), with no closedness condition on A. -/
abbrev relativeSingularCohomology {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    ModuleCat.{u} R :=
  (relativeSingularCochains R A).homology n

/-- The contravariant relative cohomology functor on subsets of a fixed ambient space. -/
abbrev relativeSingularCohomologyFunctor (X : Type u) [TopologicalSpace X] (n : ℕ) :
    (Set X)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (relativeSingularChainsFunctor R X).op ⋙ singularCochainDualFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

/-- If A is contained in B, restriction of the relative condition gives H^n(X,B) → H^n(X,A). -/
def relativeSingularCohomologyRestriction {X : Type u} [TopologicalSpace X]
    (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    relativeSingularCohomology R B n ⟶ relativeSingularCohomology R A n :=
  (relativeSingularCohomologyFunctor R X n).map (homOfLE h).op

/-- Pullback on relative cohomology along the specified continuous map of pairs. -/
def relativeSingularCohomologyPullback {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ) :
    relativeSingularCohomology R B n ⟶ relativeSingularCohomology R A n :=
  HomologicalComplex.homologyMap
    ((singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op) n

/-- The canonical map from relative to ordinary cohomology, natural in the subspace. -/
def relativeSingularCohomologyToOrdinaryNatTrans (X : Type u)
    [TopologicalSpace X] (n : ℕ) : relativeSingularCohomologyFunctor R X n ⟶
    (Functor.const (Set X)ᵒᵖ).obj (singularCohomology R X n) where
  app A := HomologicalComplex.homologyMap
    ((singularCochainDualFunctor R).map (relativeSingularChainsProjection R A.unop).op) n
  naturality {A B} f := by
    -- Dualize the natural quotient projection and then pass to cohomology.
    let F := singularCochainDualFunctor R ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
    have hProjection : relativeSingularChainsProjection R B.unop ≫
        (relativeSingularChainsFunctor R X).map f.unop =
      relativeSingularChainsProjection R A.unop := by
      simp [relativeSingularChainsFunctor, relativeSingularChainsMap,
        relativeSingularChainsProjection]
    -- Contravariance reverses the same projection identity.
    change F.map ((relativeSingularChainsFunctor R X).map f.unop).op ≫
        F.map (relativeSingularChainsProjection R B.unop).op =
      F.map (relativeSingularChainsProjection R A.unop).op ≫ 𝟙 _
    rw [Category.comp_id, ← F.map_comp, ← op_comp, hProjection]

/-- The ordinary cohomology class obtained by forgetting the relative vanishing condition. -/
def relativeSingularCohomologyToOrdinary {X : Type u} [TopologicalSpace X]
    (A : Set X) (n : ℕ) : relativeSingularCohomology R A n ⟶ singularCohomology R X n :=
  (relativeSingularCohomologyToOrdinaryNatTrans R X n).app (op A)

/-- The canonical map H^n(X,∅;R) → H^n(X;R) is an isomorphism. -/
theorem isIso_relativeSingularCohomologyToOrdinary_empty
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    IsIso (relativeSingularCohomologyToOrdinary R (∅ : Set X) n) := by
  /- Stage 1: the empty subspace has no singular simplices, so each
  degree of its actual singular chain complex is zero. Its chain
  inclusion is therefore the zero map from a zero object.
  Stage 2: the cokernel projection to C_*(X,∅;R) is an isomorphism of
  the actual complexes; this compares the canonical projection itself,
  rather than an independently selected model of relative chains.
  Stage 3: the dual-complex functor and the degree-n homology functor
  preserve this isomorphism. Their map is exactly the component of
  relativeSingularCohomologyToOrdinaryNatTrans displayed in the goal. -/
  -- The empty subspace has no singular vertices, hence no singular simplices.
  let S := TopCat.toSSet.obj (TopCat.of (∅ : Set X))
  have hEmpty : ¬ S.Nonempty := by
    rintro ⟨vertex⟩
    let f := (TopCat.toSSetObjEquiv (TopCat.of (∅ : Set X)) _) vertex
    exact (f (Classical.arbitrary _)).property
  let : S.HasDimensionLT 0 := (S.notNonempty_iff_hasDimensionLT_zero).mp hEmpty
  have hzero : IsZero (singularChains R (∅ : Set X)) :=
    S.isZero_chainComplex (singularCoefficient R)
  -- The original quotient projection is a cokernel of the zero inclusion.
  have hmap : singularSubspaceChains R (∅ : Set X) = 0 := hzero.eq_of_src _ _
  have : IsIso (relativeSingularChainsProjection R (∅ : Set X)) := by
    dsimp only [relativeSingularChainsProjection]
    exact CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ _ (cokernel.condition _))
      (cokernelIsCokernel (singularSubspaceChains R (∅ : Set X))) hmap
  -- Dualization and homology preserve that same projection isomorphism.
  change IsIso (HomologicalComplex.homologyMap
    ((singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R (∅ : Set X)).op) n)
  infer_instance

end AtiyahSinger
