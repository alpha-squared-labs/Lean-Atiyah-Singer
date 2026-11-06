/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Homotopy of idempotents in Banach algebras

Public module ID: M0037.

KR02 and a local calculation used in Karoubi III.1. The precise conclusion is conjugacy
by a unit, which induces an isomorphism of image modules. No finite-dimensionality or
self-adjointness is needed. Completeness is required for the Neumann-series inverse.

The explicit local intertwiner makes the conjugacy class locally constant along the
path. Connectedness of the interval gives endpoint conjugacy, replacing the equivalent
finite-subdivision bookkeeping while retaining the original Banach-algebra calculation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The usual intertwiner for two idempotents, equal to one when they coincide. -/
def idempotentIntertwiner (p q : A) : A := 1 - p - q + 2 * p * q

set_option linter.unusedSectionVars false in
/-- KR02: the displayed polynomial intertwines the two idempotents. -/
theorem idempotentIntertwiner_mul (p q : A) (hp : p * p = p) (hq : q * q = q) :
    idempotentIntertwiner p q * q = p * idempotentIntertwiner p q := by
  -- Distribute without commuting p and q, then use the two idempotent identities.
  have hppq : p * (p * q) = p * q := by
    rw [← mul_assoc, hp]
  unfold idempotentIntertwiner
  noncomm_ring [hp, hq, hppq]

set_option linter.unusedSectionVars false in
/-- KR02: the explicit intertwiner is a unit when its distance from one is less than one. -/
theorem isUnit_idempotentIntertwiner_of_norm_lt (p q : A)
    (h : ‖idempotentIntertwiner p q - 1‖ < 1) :
    IsUnit (idempotentIntertwiner p q) := by
  -- The Neumann series in a complete normed ring supplies a two-sided inverse.
  have hsmall : ‖1 - idempotentIntertwiner p q‖ < 1 := by
    simpa only [norm_sub_rev] using h
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hsmall

/-- KR02: a norm-continuous path of idempotents has conjugate endpoints. -/
theorem exists_unit_conjugating_idempotent_path (p : C(I, A))
    (hp : ∀ t : I, p t * p t = p t) :
    ∃ u : Aˣ, p 1 = (u : A) * p 0 * (↑(u⁻¹) : A) := by
  -- At each point the explicit intertwiner equals one. Continuity therefore makes
  -- neighboring intertwiners units, so the conjugacy class is locally constant.
  have hloc : IsLocallyConstant (fun t : I ↦ ConjClasses.mk (p t)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro t
    have hdiag : idempotentIntertwiner (p t) (p t) = 1 := by
      unfold idempotentIntertwiner
      noncomm_ring [hp t]
    have hcont : Continuous (fun s : I ↦ ‖idempotentIntertwiner (p s) (p t) - 1‖) := by
      unfold idempotentIntertwiner
      fun_prop
    have hsmall : ∀ᶠ s in 𝓝 t, ‖idempotentIntertwiner (p s) (p t) - 1‖ < 1 := by
      apply hcont.continuousAt.eventually_lt continuousAt_const
      simp only [hdiag, sub_self, norm_zero, zero_lt_one]
    filter_upwards [hsmall] with s hs
    obtain ⟨u, hu⟩ := isUnit_idempotentIntertwiner_of_norm_lt (p s) (p t) hs
    have hconj : IsConj (p t) (p s) := by
      refine ⟨u, ?_⟩
      change (u : A) * p t = p s * (u : A)
      rw [hu]
      exact idempotentIntertwiner_mul (p s) (p t) (hp s) (hp t)
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hconj.symm
  -- A locally constant map on the connected interval has equal endpoint values.
  have hends : IsConj (p 0) (p 1) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (hloc.apply_eq_of_preconnectedSpace 0 1)
  -- Turn the unit intertwining equation into the requested conjugation formula.
  obtain ⟨u, hu⟩ := hends
  refine ⟨u, ?_⟩
  have heq := congrArg (fun a : A ↦ a * (↑(u⁻¹) : A)) hu
  simpa only [mul_assoc, Units.mul_inv, mul_one] using heq.symm

end AtiyahSinger
