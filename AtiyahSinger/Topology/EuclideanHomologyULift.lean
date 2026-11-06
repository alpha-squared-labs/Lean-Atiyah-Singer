/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanRelativeHomology

/-!
# Euclidean local homology in an arbitrary universe

Public module ID: M1821.

The native singular-chain maps use one universe for source and target. A chart
from a manifold in a higher universe therefore uses the explicit ULift of its
Euclidean target. The universe-polymorphic coordinate calculation is supplied by
`EuclideanRelativeHomology`; these adapters retain the original coefficient module. No comparison
between homology objects in unequal universes is silently assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable (R : Type) [CommRing R]

/-- The punctured lifted Euclidean model vanishes in and above its dimension. -/
theorem subsingleton_singularHomology_punctured_ulift_euclidean (n k : ℕ)
    (x : ULift.{u} (EuclideanSpace ℝ (Fin n))) (hk : n ≤ k) :
    Subsingleton (singularHomology R {y : ULift.{u} (EuclideanSpace ℝ (Fin n)) | y ≠ x} k) := by
  let := subsingleton_singularHomology_punctured_pi_ulift.{u} R n k hk
  -- Lift the coordinate values as well as the chart target, keeping one universe
  -- throughout the induced singular-chain maps.
  let e : ULift.{u} (EuclideanSpace ℝ (Fin n)) ≃ₜ (Fin n → ULift.{u} ℝ) :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.ulift.trans
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.trans
        (Homeomorph.piCongrRight (fun _ : Fin n ↦ Homeomorph.ulift.symm))))
  have hex : e x = 0 := by
    ext i
    simp [e]
    rfl
  let ep : {y : ULift.{u} (EuclideanSpace ℝ (Fin n)) | y ≠ x} ≃ₜ
      {z : Fin n → ULift.{u} ℝ | z ≠ 0} :=
    e.subtype (fun y ↦ by rw [← hex]; exact e.injective.ne_iff.symm)
  exact subsingleton_singularHomology_of_homotopy_retract R
    ep.toHomotopyEquiv.toFun ep.toHomotopyEquiv.invFun ep.toHomotopyEquiv.left_inv k

/-- Local relative homology of the lifted Euclidean chart vanishes above its dimension. -/
theorem subsingleton_relativeSingularHomology_ulift_euclidean (n k : ℕ)
    (x : ULift.{u} (EuclideanSpace ℝ (Fin n))) (hk : n < k) :
    Subsingleton (relativeSingularHomology R ({x}ᶜ : Set (ULift.{u}
      (EuclideanSpace ℝ (Fin n)))) k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let := subsingleton_singularHomology_of_contractible R
    (ULift.{u} (EuclideanSpace ℝ (Fin n))) (j + 1) (by omega)
  have hset : ({x}ᶜ : Set (ULift.{u} (EuclideanSpace ℝ (Fin n)))) =
      {y : ULift.{u} (EuclideanSpace ℝ (Fin n)) | y ≠ x} := by
    ext y
    simp
  let : Subsingleton (singularHomology R
      ({x}ᶜ : Set (ULift.{u} (EuclideanSpace ℝ (Fin n)))) j) := by
    rw [hset]
    exact subsingleton_singularHomology_punctured_ulift_euclidean R n j x (by omega)
  exact relativeSingularHomology_subsingleton_of_absolute R _ j

end AtiyahSinger
