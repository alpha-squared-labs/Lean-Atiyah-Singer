/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleCohomologyThom
public import AtiyahSinger.Topology.ComplexBundleCohomologyVanishing
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.ComplexBundleCompactSupportCharacter

/-!
# The original complex Thom characteristic defect

Public module ID: M1720.

This definition layer retains the original exterior K-Thom unit and the inverse
of the canonically complex-oriented cohomological Thom map. Keeping the definition
below naturality and the characteristic formula avoids a circular module import.

Source: SG III.12, the characteristic defect of the exterior Thom symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r)

/-- SG's characteristic Thom defect, defined using the original K unit and specified integral. -/
def complexThomDefectComponent (j : ℕ) : singularCohomology ℚ X (2 * j) :=
  h.complexCohomologyFiberIntegral r hr (2 * j)
    ((eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ (TotalSpace Unit E) (2 * (r + j)) ≅
          compactSupportCohomology ℚ (TotalSpace Unit E) (2 * j + 2 * r)).hom
      (h.compactSupportChernCharacterComponent r hr (r + j)
        (h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm
          (AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1))))))

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
