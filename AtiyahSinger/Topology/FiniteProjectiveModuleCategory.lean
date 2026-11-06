/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# The category of finite projective modules

Public module ID: M1854.

This is the standard full subcategory of `ModuleCat R` on finitely generated
projective modules. Its objects and linear maps retain the original carriers
and scalar actions. The ring and module universes are independent.

Source: Karoubi, K-Theory, I.6.16--6.18. Mathlib uses left modules; the source's
right-module convention is represented by choosing the scalar ring to be the
opposite ring. For continuous complex functions the section functor uses the
existing evaluation action over the commutative ring C(X,ℂ).
-/

@[expose] public section

namespace AtiyahSinger

open CategoryTheory

universe v u

/-- Finite projective modules with all linear maps, as a full subcategory of modules. -/
abbrev FiniteProjectiveModuleCat (R : Type u) [Ring R] : Type (max u (v + 1)) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{v} R ↦ Module.Finite R M ∧ Module.Projective R M)

namespace FiniteProjectiveModuleCat

variable {R : Type u} [Ring R]

/-- The underlying module of an object has its recorded finite-generation certificate. -/
instance finite (P : FiniteProjectiveModuleCat.{v} R) : Module.Finite R P.obj :=
  P.property.1

/-- The underlying module of an object has its recorded projectivity certificate. -/
instance projective (P : FiniteProjectiveModuleCat.{v} R) : Module.Projective R P.obj :=
  P.property.2

/-- Package an existing finite projective module without changing its carrier or action. -/
abbrev of (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] : FiniteProjectiveModuleCat.{v} R :=
  ⟨ModuleCat.of R P, ⟨inferInstance, inferInstance⟩⟩

end FiniteProjectiveModuleCat

end AtiyahSinger
