/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.CategoryTheory.Abelian.Ext

/-!
# Ordinary singular cohomology on the original singular chain complex

Public module ID: M2126.

D11: the ordinary cohomology foundation used in SG III.11 and III.12.1.
For any small commutative coefficient ring R and any topological space X,
the chains are mathlib's actual free R-modules on continuous singular
simplices, with their alternating-face boundary. Cochains are the algebraic
linear dual complex Hom_R(C_*(X;R),R), with differential φ ↦ φ ∘ ∂.
Its degree-n homology is unreduced singular cohomology H^n(X;R).

The coefficient object's ULift changes only its universe. No compactness,
separation, local contractibility, manifold or dimension hypothesis is
imposed on X. Integer, rational and real coefficient rings can all be used;
maps changing the coefficient ring are not supplied by this file.

The contravariant functors below use the original singular chain maps.
The dual-complex functor is also exposed for the actual relative chain
cokernels used for relative singular cohomology.

The construction uses mathlib's additive linear-Yoneda dualization, with
a variable coefficient ring. The homotopy theorem applies this same
dualization to the singular chain homotopy of the given continuous maps.
Cup products, characteristic classes and locally finite fundamental-class
pairings are provided in their respective modules.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R]

/-- The regular coefficient module, lifted to the same universe as the topological space. -/
abbrev singularCoefficient : ModuleCat.{u} R :=
  ModuleCat.of R (ULift.{u} R)

/-- The original mathlib singular chain functor with coefficients in the regular R-module. -/
abbrev singularChainsFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (singularCoefficient R)

/-- The ordinary singular chains, with finite sums of actual continuous singular simplices. -/
abbrev singularChains (X : Type u) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (singularChainsFunctor R).obj (TopCat.of X)

/-- Algebraic dualization of actual R-module chain complexes, with differential φ ↦ φ ∘ ∂. -/
def singularCochainDualFunctor : (ChainComplex (ModuleCat.{u} R) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((((linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)).op) ⋙
      HomologicalComplex.unopFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- The contravariant ordinary singular cochain functor, obtained from the actual chain maps. -/
abbrev singularCochainsFunctor : TopCat.{u}ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (singularChainsFunctor R).op ⋙ singularCochainDualFunctor R

/-- The algebraic singular cochain complex Hom_R(C_*(X;R),R). -/
abbrev singularCochains (X : Type u) [TopologicalSpace X] :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (singularCochainsFunctor R).obj (op (TopCat.of X))

/-- The degree-n unreduced singular cohomology functor, with its actual contravariant maps. -/
abbrev singularCohomologyFunctor (n : ℕ) : TopCat.{u}ᵒᵖ ⥤ ModuleCat.{u} R :=
  singularCochainsFunctor R ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

/-- Ordinary singular cohomology H^n(X;R), the cochain cocycles modulo coboundaries. -/
abbrev singularCohomology (X : Type u) [TopologicalSpace X] (n : ℕ) : ModuleCat.{u} R :=
  (singularCohomologyFunctor R n).obj (op (TopCat.of X))

/-- Pullback in ordinary singular cohomology along the specified continuous map. -/
def singularCohomologyPullback {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : singularCohomology R Y n ⟶ singularCohomology R X n :=
  (singularCohomologyFunctor R n).map (TopCat.ofHom f).op

/-- Homotopic continuous maps induce the same pullback in every degree and coefficient ring. -/
theorem singularCohomologyPullback_homotopic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    singularCohomologyPullback R f n = singularCohomologyPullback R g n := by
  /- Stage 1: regard the given homotopy as a TopCat.Homotopy between
  the same maps f and g. The original singular prism construction in
  TopCat.Homotopy.singularChainComplexFunctorObjMap supplies a chain
  homotopy between their actual singular chain maps with coefficient R.
  Stage 2: apply the additive linear-Yoneda functor to that chain
  homotopy and unop it. This gives a cochain homotopy for precisely
  the two maps used by singularCochainsFunctor, including its signs.
  Stage 3: Homotopy.homologyMap_eq identifies their induced homology
  maps, which are the displayed cohomology pullbacks. All stages use
  the given X, Y and coefficient module; no additional geometric or
  finiteness assumption is needed. -/
  -- The given topological homotopy supplies a homotopy of the original singular chains.
  let Htop : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  let hchains := Htop.singularChainComplexFunctorObjMap (singularCoefficient R)
  -- Apply the same additive dual functor, then reverse the complex direction.
  let dual := ((linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)).rightOp
  let hcochains := (dual.mapHomotopy hchains).unop
  -- Homotopic cochain maps agree on their actual homology objects.
  exact hcochains.homologyMap_eq n

end AtiyahSinger
