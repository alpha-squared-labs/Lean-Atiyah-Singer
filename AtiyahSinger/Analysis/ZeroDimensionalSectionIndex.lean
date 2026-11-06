/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothAtlasSections
public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Smooth sections and the index on a finite zero-dimensional base

Public module ID: M1055.

The original smooth-atlas section space is the full product of its original
fibers: a zero-dimensional charted space is discrete, so every coordinate
function is smooth. On a finite base, finite-dimensional rank-nullity then
computes the index of any linear map between these same section spaces.
The fiber dimensions may vary among the points.

This is the elementary zero-dimensional supplement to the section and index
conventions in Spin Geometry, III.1 and III.5. It makes no use of an index
theorem, an elliptic representative, or a replacement bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  {E F : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := 0) E) (B : SmoothComplexBundleAtlas (n := 0) F)

/-- Evaluation identifies the original smooth sections with all original fiberwise values. -/
def sectionsEquivPiOfZeroDimensional : A.smoothSections ≃ₗ[ℂ] (∀ x : M, E x) := by
  let : DiscreteTopology M := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) M
  -- Every coordinate map is smooth on this discrete manifold, in the specified atlas.
  have hs (s : ∀ x : M, E x) : A.IsSmoothSection s := by
    intro i
    exact contMDiff_of_discreteTopology.contMDiffOn
  exact
    { toFun := Subtype.val
      invFun := fun s ↦ ⟨s, hs s⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Finite-dimensional rank-nullity computes the index on the same finite collection of fibers. -/
theorem index_eq_sum_finrank_of_zeroDimensional [Fintype M]
    (T : A.smoothSections →ₗ[ℂ] B.smoothSections) :
    T.index = (∑ x : M, (Module.finrank ℂ (E x) : ℤ)) -
      ∑ x : M, (Module.finrank ℂ (F x) : ℤ) := by
  let : ComplexBundle.IsFiniteRank E := A.isFiniteRank
  let : ComplexBundle.IsFiniteRank F := B.isFiniteRank
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ ComplexBundle.finite_fiber x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦ ComplexBundle.finite_fiber x
  -- The same evaluation equivalences give finite-dimensionality of the section spaces.
  let : FiniteDimensional ℂ A.smoothSections :=
    A.sectionsEquivPiOfZeroDimensional.symm.finiteDimensional
  let : FiniteDimensional ℂ B.smoothSections :=
    B.sectionsEquivPiOfZeroDimensional.symm.finiteDimensional
  -- Rank-nullity cancels the actual range dimension; no property of T is assumed.
  rw [LinearMap.index_eq_of_finiteDimensional,
    A.sectionsEquivPiOfZeroDimensional.finrank_eq,
    B.sectionsEquivPiOfZeroDimensional.finrank_eq,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype,
    Nat.cast_sum, Nat.cast_sum]

end AtiyahSinger.SmoothComplexBundleAtlas
