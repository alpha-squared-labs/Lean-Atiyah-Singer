/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.SupportedCohomologyThomVanishing

/-!
# Compact-support cohomology below the real rank of a complex bundle

Public module ID: M1695.

The supplied Hermitian metric gives a native real model with its canonical
complex orientation. The oriented compact-support Thom vanishing theorem
therefore applies in every degree below twice the fixed complex rank.
Pullback through the identity-on-vectors total-space homeomorphism transfers
this conclusion to the original Unit-model compact-support cohomology.
The base is Hausdorff and need not be compact.

This standard consequence of Thom vanishing is used by the complex Thom
character and the supported normal Thom character. Sources: Hatcher,
Algebraic Topology, Sections 3.2 and 4.D; Milnor--Stasheff, Sections 9, 10
and 14, for the canonical orientation of a complex bundle. The transfer
between the project's two total-space models is an explicit adapter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X] [hHausdorff : T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hFinite : IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

include h hHausdorff hFinite in
/-- Rational compact-support cohomology of the original complex total space vanishes
below twice the fixed complex rank, over any Hausdorff base. -/
theorem compactSupportCohomology_subsingleton_below_complex_rank
    (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (k : ℕ) (hk : k < 2 * r) :
    Subsingleton (compactSupportCohomology ℚ (TotalSpace Unit E) k) := by
  -- Use the native real model from the same metric and the same rank witness.
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let : Subsingleton (compactSupportCohomology ℚ
      (TotalSpace (EuclideanSpace ℝ (Fin (2 * r))) E) k) :=
    compactSupportCohomology_subsingleton_below_rank_of_orientation ℚ (2 * r) E
      (h.complexCohomologyOrientation r hr).rationalization k hk
  -- Pullback along this actual homeomorphism is injective into the zero group.
  exact (compactSupportCohomologyHomeomorphPullback_bijective ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) k).injective.subsingleton

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
