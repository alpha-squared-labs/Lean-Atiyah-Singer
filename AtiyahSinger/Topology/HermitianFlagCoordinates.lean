/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagSplitting

/-!
# The original full-flag coordinate maps

Public module ID: M1883.

Each coordinate of the original flag splitting is its specified projection
onto the corresponding actual range line. These continuous bundle maps
jointly detect vectors. The same maps can therefore be used as line
coordinates when comparing projective constructions for different metrics.
They do not require the comparison metric to make those lines orthogonal.

This is an implementation interface for the original splitting, with no
new splitting witness or replacement bundle topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianFlagTopology hermitianFlagLineTopology
  hermitianFlagSumTopology

/-- The specified flag projection, viewed as a continuous map into its own range line. -/
def hermitianFlagCoordinateHom (i : Fin r) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    Hom ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → X) *ᵖ E)
      (HermitianFlagLine r E h i) := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  refine
    { linearMap := fun p ↦ (p.2.val i).toLinearMap.rangeRestrict
      continuous_total := ?_ }
  -- Extract the same component from the already verified inverse splitting map.
  have hc : Continuous (fun z : TotalSpace Unit (HermitianFlagSum r E h) ↦
      (z.proj, fun j : Fin r ↦
        (⟨z.proj, z.snd j⟩ : TotalSpace Unit (HermitianFlagLine r E h j)))) :=
    continuous_induced_dom
  exact ((continuous_apply i).comp hc.snd).comp
    (hermitianFlagSplitting_properties r E h).2.2.2

/-- The original flag coordinates jointly distinguish vectors in each original fiber. -/
theorem hermitianFlagCoordinates_injective (p : HermitianFlagBundle r E h) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    Function.Injective (fun v : E p.1 ↦ fun i : Fin r ↦
      (hermitianFlagCoordinateHom r E h i).linearMap p v) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro v w hvw
  -- The same sum-of-projections identity reconstructs both vectors, also at rank zero.
  have hcoordinates : ∀ i : Fin r, p.2.val i v = p.2.val i w :=
    fun i ↦ congrArg Subtype.val (congrFun hvw i)
  calc
    v = ∑ i, p.2.val i v := ((hermitianFlagSplitting_properties r E h).2.1 p v).symm
    _ = ∑ i, p.2.val i w := Finset.sum_congr rfl (fun i _ ↦ hcoordinates i)
    _ = w := (hermitianFlagSplitting_properties r E h).2.1 p w

end AtiyahSinger.ComplexBundle
