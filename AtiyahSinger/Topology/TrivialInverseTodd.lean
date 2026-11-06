/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacterNormalization
public import AtiyahSinger.Topology.InverseToddOperations

/-!
# The original inverse Todd class of a trivial bundle

Public module ID: M2264.

The original trivial bundle is the actual pullback of its fiber over a point.
Naturality and its specified pullback Iso imply that positive components
vanish. The existing zero-component normalization supplies the unit, including
for the empty bundle and an arbitrary original base.

Source: SG III.11, normalization of multiplicative characteristic classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X]

attribute [local instance] trivialTopology isFiniteRank_trivial isFiniteRank_pullback

/-- Every actual trivial complex bundle has unit inverse Todd class. -/
theorem inverseToddClassComponent_trivial (n : ℕ)
    (h : ContinuousHermitianMetric (Bundle.Trivial X (Fin n → ℂ))) (k : ℕ) :
    inverseToddClassComponent (Bundle.Trivial X (Fin n → ℂ)) h k =
      singularCohomologyDegreeTwoPow ℚ X (0 : singularCohomology ℚ X 2) k := by
  cases k with
  | zero => exact inverseToddClassComponent_zero _ h
  | succ k =>
    -- The same trivial fiber is pulled from the point, whose positive cohomology vanishes.
    let P := PUnit.{u + 1}
    let E := Bundle.Trivial P (Fin n → ℂ)
    let hP := (nonempty_continuousHermitianMetric E).some
    let f : C(X, P) := ContinuousMap.const _ PUnit.unit
    have hn : 0 < 2 * (k + 1) := by omega
    let := subsingleton_singularHomology_of_subsingleton ℚ P (2 * (k + 1)) hn
    let : Subsingleton (singularCohomology ℚ P (2 * (k + 1))) :=
      subsingleton_singularCochainDualHomology_of_subsingleton ℚ
        (singularChains ℚ P) (2 * (k + 1))
    have hpoint : inverseToddClassComponent E hP (k + 1) = 0 := Subsingleton.elim _ _
    rw [inverseToddClassComponent_eq_of_iso (Bundle.Trivial X (Fin n → ℂ)) h
      ((f : X → P) *ᵖ E) (hP.pullback f) (pullbackTrivialIso f n).symm,
      ← inverseToddClassComponent_pullback E hP f, hpoint, map_zero]
    simp [singularCohomologyDegreeTwoPow]

end AtiyahSinger.ComplexBundle
