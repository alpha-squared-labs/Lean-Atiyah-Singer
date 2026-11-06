/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyChangeCoefficients

/-!
# Integral coefficient change is the original identity

Public module ID: M1619.

The actual integer-to-integer coefficient map leaves every original singular
simplex evaluation unchanged. Passing through the original cocycle quotient
and its scalar-restriction comparison therefore fixes every cohomology class.
This identifies integral specializations with the original normalized Chern
roots, without replacing them by separately chosen classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified integer-to-integer coefficient map fixes every original cohomology class. -/
theorem singularCohomologyChangeCoefficients_int_self (X : Type u) [TopologicalSpace X]
    (n : ℕ) (a : singularCohomology ℤ X n) :
    singularCohomologyChangeCoefficients ℤ X n a = a := by
  let C := singularCochains ℤ X
  -- Represent the actual class in the original cocycle quotient.
  obtain ⟨α, hα⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
    ((C.sc n).moduleCatHomologyIso.hom a)
  have hclass : singularCocycleClass ℤ X n α = a := by
    change (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ α) = a
    rw [hα]
    exact congrArg (fun f ↦ f a) (C.sc n).moduleCatHomologyIso.hom_inv_id
  rw [← hclass, singularCohomologyChangeCoefficients_cocycleClass]
  apply congrArg (singularCocycleClass ℤ X n)
  apply Subtype.ext
  -- The coefficient map preserves this same cocycle, since each integer value is unchanged.
  apply (singularCochainEquiv ℤ X n).injective
  funext σ
  have heval := (existsUnique_singularCochainsChangeCoefficients ℤ X).exists.choose_spec
    n α.val σ
  change singularCochainEquiv ℤ X n ((singularCochainsChangeCoefficients ℤ X).f n α.val) σ =
    ULift.up ((singularCochainEquiv ℤ X n α.val σ).down : ℤ) at heval
  apply ULift.ext
  exact congrArg ULift.down heval

end AtiyahSinger
