/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric

/-!
# Restricting a continuous Hermitian metric along a bundle injection

Public module ID: M1887.

An actual fiberwise injective bundle map pulls the given Hermitian form back
to a positive form on its source. Joint continuity is checked in the original
double-bundle total topologies. No fiber norms or bundle topologies change.
This gives the inherited metrics on the actual flag range lines.

Source: the induced Hermitian metric on a complex vector subbundle,
Husemoller, Fibre Bundles, Chapter III.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

attribute [local instance] sumTopology

variable {X : Type*} [TopologicalSpace X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- The original Hermitian form restricted along the specified fiberwise injection. -/
def comap [IsFiniteRank E] (h : ContinuousHermitianMetric F) (a : Hom E F)
    (ha : ∀ x, Function.Injective (a.linearMap x)) : ContinuousHermitianMetric E where
  toCore x :=
    { inner := fun v w ↦ (h.toCore x).inner (a.linearMap x v) (a.linearMap x w)
      conj_inner_symm v w := (h.toCore x).conj_inner_symm _ _
      re_inner_nonneg v := (h.toCore x).re_inner_nonneg _
      add_left v w z := by rw [map_add, (h.toCore x).add_left]
      smul_left v w c := by rw [map_smul, (h.toCore x).smul_left]
      definite v hv := ha x ((h.toCore x).definite _ hv |>.trans (map_zero _).symm) }
  continuous_pairing := h.continuous_pairing.comp (a.sum a).continuous_total
  isFiniteRank := inferInstance

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
