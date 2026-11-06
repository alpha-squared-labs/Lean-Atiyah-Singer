/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenCotangent
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The derivative of an inherited open-submanifold inclusion

Public module ID: M1320.

The inherited charts make the actual inclusion derivative the identity.
This native-coordinate fact is used for the two pole cotangent lifts and
for their product comparison; it does not change the manifold model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- An inherited open inclusion has identity derivative in the original native model. -/
theorem mfderiv_openSubtype_val (U : Opens M) (y : U) :
    mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hι : MDifferentiableAt (𝓡 n) (𝓡 n) (Subtype.val : U → M) y :=
    (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
  have hrep : writtenInExtChartAt (𝓡 n) (𝓡 n) y (Subtype.val : U → M) =ᶠ[
      𝓝 ((extChartAt (𝓡 n) y) y)]
      writtenInExtChartAt (𝓡 n) (𝓡 n) (y : M) (id : M → M) := by
    change (fun v ↦ (chartAt (EuclideanSpace ℝ (Fin n)) (y : M))
        (((chartAt (EuclideanSpace ℝ (Fin n)) y).symm v : U) : M)) =ᶠ[
          𝓝 (chartAt (EuclideanSpace ℝ (Fin n)) (y : M) y)]
      (fun v ↦ (chartAt (EuclideanSpace ℝ (Fin n)) (y : M))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).symm v))
    exact
      (U.chartAt_subtype_val_symm_eventuallyEq (x := y)).symm.fun_comp
        (chartAt (EuclideanSpace ℝ (Fin n)) (y : M))
  have hD := hrep.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := Set.range (𝓡 n))
  have hid := mfderiv_id (I := 𝓡 n) (x := (y : M))
  rw [mfderiv, ite_eq_left hι]
  change fderivWithin ℝ (writtenInExtChartAt (𝓡 n) (𝓡 n) y
    (Subtype.val : U → M)) (Set.range (𝓡 n)) ((extChartAt (𝓡 n) y) y) = _
  rw [hD]
  simp only [mfderiv, mdifferentiableAt_id, ↓reduceIte] at hid
  change fderivWithin ℝ (writtenInExtChartAt (𝓡 n) (𝓡 n) (y : M)
    (id : M → M)) (Set.range (𝓡 n)) ((extChartAt (𝓡 n) (y : M)) y) = _ at hid
  exact hid

end AtiyahSinger
