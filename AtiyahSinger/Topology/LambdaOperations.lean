/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacterKZero
public import AtiyahSinger.Topology.ThomDirectSum
public import AtiyahSinger.Topology.ThomZeroSection

import all AtiyahSinger.Topology.ThomNaturality

/-!
# Isomorphism invariance and the zero-bundle exterior unit

Public module ID: M1927.

The original alternating exterior class is invariant under actual bundle
isomorphisms. The existing exterior-functor parity isomorphisms supply this
comparison without introducing new exterior bundles. For zero fibers, the
already proved zero-rank Thom transport and the original zero-section formula
identify this same alternating class with the K-theory unit.

Source: SG III.12 and KA IV.1, the alternating exterior class and its unit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  t2Space_totalSpace locallyCompactSpace_totalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- The original alternating exterior class is invariant under actual bundle isomorphisms. -/
theorem lambdaMinusOne_eq_of_iso
    (F : X → Type w) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F] (e : Iso E F) :
    lambdaMinusOne E = lambdaMinusOne F := by
  obtain ⟨e₀, _⟩ := exists_exteriorParity_iso e 0
  obtain ⟨e₁, _⟩ := exists_exteriorParity_iso e 1
  unfold lambdaMinusOne
  rw [kZeroClass_eq_of_iso e₀, kZeroClass_eq_of_iso e₁]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For zero fibers, the actual alternating exterior class is the K-theory unit. -/
theorem lambdaMinusOne_eq_one_of_subsingleton [∀ x, Subsingleton (E x)] :
    lambdaMinusOne E = (1 : ComplexKZero X) := by
  let h := (nonempty_continuousHermitianMetric E).some
  let a := (compactSupportKZeroCompactEquiv X).symm (1 : ComplexKZero X)
  let e := zeroSectionHomeomorph (E := E)
  -- The actual zero section and its inverse compose to identity in compact-support K-theory.
  have hback := DFunLike.congr_fun (compactSupportKZeroHomeomorph_symm e) a
  have hz := zeroSectionPullback_supportedThomHom E h a
  rw [ContinuousHermitianMetric.supportedThomHom_zeroRank] at hz
  change compactSupportKZeroCompactEquiv X
    (compactSupportKZeroHomeomorph e.symm (compactSupportKZeroHomeomorph e a)) =
      kZeroMul C(X, ℂ) (lambdaMinusOne E) (compactSupportKZeroCompactEquiv X a) at hz
  change compactSupportKZeroHomeomorph e.symm (compactSupportKZeroHomeomorph e a) = a at hback
  rw [hback] at hz
  have ha : compactSupportKZeroCompactEquiv X a = (1 : ComplexKZero X) :=
    (compactSupportKZeroCompactEquiv X).apply_symm_apply 1
  rw [ha] at hz
  change 1 = lambdaMinusOne E * 1 at hz
  simpa only [mul_one] using hz.symm

end AtiyahSinger.ComplexBundle
