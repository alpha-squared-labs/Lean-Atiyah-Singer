/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleCutoff
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Global bundle-map realizations of compactly supported triples

Public module ID: M2198.

P01: multiply the given exterior isomorphism and its actual inverse by one
continuous cutoff that vanishes near the original compact control. These are
the existing explicit cutoffHom maps on the original bundles. Outside a larger
compact control they retain the original forward and inverse actions, and the
same enlarged support triple has exactly the original compact-support K class.

This is the standard map realization of the support-triple model of SG I.9.26,
used across the zero section in III.13.3. The continuous cutoff assembly is an
explicit project supplement. It asserts neither global homogeneity after the
cutoff nor global invertibility across the control, and needs no bundle metric.
The proof retains the existing formulas and the same cutoff throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- The explicit global cutoff maps realize the original support class outside one compact set. -/
theorem CompactSupportTriple.exists_cutoff_realization (a : CompactSupportTriple E F) :
    ∃ (U : Set X) (hU : IsOpen U) (hcontrol : a.control ⊆ U),
      ∃ (L : Set X) (hL : IsCompact L) (hUL : U ⊆ L),
        ∃ (ρ : C(X, I)) (hzero : ∀ x ∈ U, ρ x = 0),
          (∀ x ∉ L, ρ x = 1) ∧
          (∀ x : (Lᶜ : Set X),
            (a.cutoffHom ρ U hU hcontrol hzero).linearMap x =
              ((a.enlarge L hL (hcontrol.trans hUL)).boundary.linearEquiv x).toLinearMap ∧
            (a.inverse.cutoffHom ρ U hU hcontrol hzero).linearMap x =
              ((a.enlarge L hL (hcontrol.trans hUL)).boundary.linearEquiv x).symm.toLinearMap) ∧
          (a.enlarge L hL (hcontrol.trans hUL)).compactSupportClass = a.compactSupportClass := by
  /- Stage 1: choose U,L and rho by exists_time_cutoff on the original
  locally compact Hausdorff base space X. The prescribed original compact
  control lies inside the open zero plateau; no norm bound on its exterior
  isomorphism near the control is needed.
  Stage 2: use the already defined cutoffHom for a and a.inverse with
  this same rho. Its zero extension is a continuous Hom on each of the
  original bundles. At every point outside L, rho=1 recovers the original
  boundary and its actual inverse. Enlargement restricts exactly this map,
  so both displayed identities concern the same exterior vector.
  Stage 3: compactSupportClass_enlarge identifies the class of that very
  enlarged triple with the original class. -/
  -- Choose one zero plateau, compact control, and cutoff for the original triple.
  obtain ⟨U, hU, hcontrol, L, hL, hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff a.control a.isCompact_control
  refine ⟨U, hU, hcontrol, L, hL, hUL, ρ, hzero, hone, ?_,
    a.compactSupportClass_enlarge L hL (hcontrol.trans hUL)⟩
  -- Outside the same L, the given boundary and its specified inverse are unchanged.
  intro x
  let y : (a.controlᶜ : Set X) :=
    ⟨x, fun hx ↦ x.property (hUL (hcontrol hx))⟩
  have hboundary := a.cutoffHom_boundary ρ U hU hcontrol hzero y (hone x x.property)
  constructor
  · refine hboundary.1.trans ?_
    apply LinearMap.ext
    intro v
    exact (a.enlarge_apply L hL (hcontrol.trans hUL) x v).symm
  · refine hboundary.2.trans ?_
    apply LinearMap.ext
    intro v
    exact (Iso.restrictTo_apply a.boundary.symm
      (Set.compl_subset_compl.mpr (hcontrol.trans hUL)) x v).symm

end AtiyahSinger.ComplexBundle
