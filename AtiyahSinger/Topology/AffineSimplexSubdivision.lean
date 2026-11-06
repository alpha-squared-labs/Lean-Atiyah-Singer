/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AffineSimplexChains
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Abel

/-!
# Barycentric subdivision of affine vertex chains

Public module ID: M1524.

Subdivision cones the already subdivided boundary to the centroid of the same
ordered simplex. The empty augmented simplex is fixed. The cone identity shows
that this recursive finite expression commutes with boundary. Affine naturality
allows these universal expressions to define subdivision of actual singular
simplices. This is the barycentric construction in Hatcher, section 2.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Convexity

open scoped BigOperators

universe u v w

variable (R : Type u) [CommRing R] (E : Type v) [ConvexSpace ℝ E]

/-- Barycentric subdivision as a finite cone of the recursively subdivided boundary. -/
def vertexChainSubdivision : (k : ℕ) → SimplexVertexChain R E k →ₗ[R] SimplexVertexChain R E k
  | 0 => LinearMap.id
  | k + 1 => Finsupp.linearCombination R (fun v : Fin (k + 1) → E ↦
      vertexChainCone R E ((StdSimplex.barycenter (K := ℝ)).iConvexComb v) k
        (vertexChainSubdivision k (vertexChainBoundary R E k (Finsupp.single v 1))))

/-- On a generator, subdivision uses precisely its own centroid and boundary. -/
theorem vertexChainSubdivision_single (k : ℕ) (v : Fin (k + 1) → E) (a : R) :
    vertexChainSubdivision R E (k + 1) (Finsupp.single v a) =
      a • vertexChainCone R E ((StdSimplex.barycenter (K := ℝ)).iConvexComb v) k
        (vertexChainSubdivision R E k
          (vertexChainBoundary R E k (Finsupp.single v 1))) := by
  exact Finsupp.linearCombination_single _ _ _

/-- Subdivision commutes with the original alternating boundary, including augmentation. -/
theorem vertexChainSubdivision_boundary (k : ℕ) (c : SimplexVertexChain R E (k + 1)) :
    vertexChainBoundary R E k (vertexChainSubdivision R E (k + 1) c) =
      vertexChainSubdivision R E k (vertexChainBoundary R E k c) := by
  classical
  induction k with
  | zero =>
    suffices h : (vertexChainBoundary R E 0).comp (vertexChainSubdivision R E 1) =
        (vertexChainSubdivision R E 0).comp (vertexChainBoundary R E 0) from
      congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    simp only [LinearMap.comp_apply, vertexChainSubdivision_single, map_smul,
      vertexChainBoundary_cone_zero]
    simp [vertexChainSubdivision, vertexChainBoundary_single]
  | succ k hk =>
    suffices h : (vertexChainBoundary R E (k + 1)).comp
        (vertexChainSubdivision R E (k + 2)) =
        (vertexChainSubdivision R E (k + 1)).comp (vertexChainBoundary R E (k + 1)) from
      congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    -- The coned boundary is a cycle, by the previous dimension and boundary squared zero.
    simp only [LinearMap.comp_apply, vertexChainSubdivision_single, map_smul,
      vertexChainBoundary_cone, hk, vertexChainBoundary_boundary, map_zero, sub_zero]
    simp only [vertexChainBoundary_single, one_smul, map_smul]

variable {E}

/-- Affine maps commute with subdivision of the original ordered vertex chains. -/
theorem vertexChainMap_subdivision {F : Type w} [ConvexSpace ℝ F]
    (f : ConvexSpace.AffineMap ℝ E F) (k : ℕ) (c : SimplexVertexChain R E k) :
    vertexChainMap R E f k (vertexChainSubdivision R E k c) =
      vertexChainSubdivision R F k (vertexChainMap R E f k c) := by
  classical
  induction k with
  | zero => rfl
  | succ k hk =>
    suffices h : (vertexChainMap R E f (k + 1)).comp (vertexChainSubdivision R E (k + 1)) =
        (vertexChainSubdivision R F (k + 1)).comp (vertexChainMap R E f (k + 1)) from
      congrArg (fun g ↦ g c) h
    apply Finsupp.lhom_ext
    intro v a
    have hcentroid : f ((StdSimplex.barycenter (K := ℝ)).iConvexComb v) =
        (StdSimplex.barycenter (K := ℝ)).iConvexComb (f ∘ v) := by
      exact f.isAffineMap.map_iConvexComb _ v
    -- The original centroid, cone vertex, and all faces are transported together.
    simp only [LinearMap.comp_apply, vertexChainSubdivision_single, map_smul,
      vertexChainMap_cone, hcentroid, hk, vertexChainMap_boundary]
    simp [vertexChainMap, vertexChainSubdivision_single]

variable (E)

/-- The standard cone homotopy from subdivision to the identity on augmented vertex chains. -/
def vertexChainSubdivisionHomotopy :
    (k : ℕ) → SimplexVertexChain R E k →ₗ[R] SimplexVertexChain R E (k + 1)
  | 0 => 0
  | k + 1 => Finsupp.linearCombination R (fun v : Fin (k + 1) → E ↦
      vertexChainCone R E (v 0) (k + 1)
        (Finsupp.single v 1 - vertexChainSubdivision R E (k + 1) (Finsupp.single v 1) -
          vertexChainSubdivisionHomotopy k
            (vertexChainBoundary R E k (Finsupp.single v 1))))

/-- The homotopy cones the same simplex discrepancy at its original first vertex. -/
theorem vertexChainSubdivisionHomotopy_single (k : ℕ) (v : Fin (k + 1) → E) (a : R) :
    vertexChainSubdivisionHomotopy R E (k + 1) (Finsupp.single v a) =
      a • vertexChainCone R E (v 0) (k + 1)
        (Finsupp.single v 1 - vertexChainSubdivision R E (k + 1) (Finsupp.single v 1) -
          vertexChainSubdivisionHomotopy R E k
            (vertexChainBoundary R E k (Finsupp.single v 1))) := by
  exact Finsupp.linearCombination_single _ _ _

/-- The finite cone construction satisfies the actual augmented chain homotopy equation. -/
theorem vertexChainSubdivisionHomotopy_boundary (k : ℕ)
    (c : SimplexVertexChain R E (k + 1)) :
    vertexChainBoundary R E (k + 1) (vertexChainSubdivisionHomotopy R E (k + 1) c) =
      c - vertexChainSubdivision R E (k + 1) c -
        vertexChainSubdivisionHomotopy R E k (vertexChainBoundary R E k c) := by
  classical
  induction k with
  | zero =>
    suffices h : (vertexChainBoundary R E 1).comp (vertexChainSubdivisionHomotopy R E 1) =
        LinearMap.id - vertexChainSubdivision R E 1 -
          (vertexChainSubdivisionHomotopy R E 0).comp (vertexChainBoundary R E 0) from
      congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    -- In the first degree the augmentation of the discrepancy is zero.
    simp only [LinearMap.comp_apply, vertexChainSubdivisionHomotopy_single, map_smul,
      vertexChainBoundary_cone, map_sub, vertexChainSubdivision_boundary,
      LinearMap.sub_apply, LinearMap.id_apply]
    simp only [vertexChainSubdivisionHomotopy, vertexChainSubdivision, LinearMap.zero_apply,
      LinearMap.id_apply, map_zero, sub_zero, sub_self]
    rw [← Finsupp.smul_single_one v a, map_smul, smul_sub]
    simp only [smul_sub]
    abel
  | succ k hk =>
    suffices h : (vertexChainBoundary R E (k + 2)).comp
        (vertexChainSubdivisionHomotopy R E (k + 2)) =
        LinearMap.id - vertexChainSubdivision R E (k + 2) -
          (vertexChainSubdivisionHomotopy R E (k + 1)).comp
            (vertexChainBoundary R E (k + 1)) from congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    let b : SimplexVertexChain R E (k + 2) := Finsupp.single v 1
    -- The induction equation and boundary-square identity make this discrepancy a cycle.
    have hcycle : vertexChainBoundary R E (k + 1)
        (b - vertexChainSubdivision R E (k + 2) b -
          vertexChainSubdivisionHomotopy R E (k + 1) (vertexChainBoundary R E (k + 1) b)) =
        0 := by
      rw [map_sub, map_sub, vertexChainSubdivision_boundary, hk,
        vertexChainBoundary_boundary, map_zero, sub_zero, sub_self]
    simp only [LinearMap.comp_apply, vertexChainSubdivisionHomotopy_single, map_smul,
      vertexChainBoundary_cone, LinearMap.sub_apply, LinearMap.id_apply]
    change a • (b - vertexChainSubdivision R E (k + 2) b -
      vertexChainSubdivisionHomotopy R E (k + 1) (vertexChainBoundary R E (k + 1) b) -
      vertexChainCone R E (v 0) (k + 1) _) = _
    rw [hcycle, map_zero, sub_zero]
    rw [← Finsupp.smul_single_one v a]
    simp only [map_smul, smul_sub]
    rfl

variable {E}

/-- The same cone homotopy is natural for affine maps of its vertices. -/
theorem vertexChainMap_subdivisionHomotopy {F : Type w} [ConvexSpace ℝ F]
    (f : ConvexSpace.AffineMap ℝ E F) (k : ℕ) (c : SimplexVertexChain R E k) :
    vertexChainMap R E f (k + 1) (vertexChainSubdivisionHomotopy R E k c) =
      vertexChainSubdivisionHomotopy R F k (vertexChainMap R E f k c) := by
  classical
  induction k with
  | zero => simp [vertexChainSubdivisionHomotopy]
  | succ k hk =>
    suffices h : (vertexChainMap R E f (k + 2)).comp
        (vertexChainSubdivisionHomotopy R E (k + 1)) =
        (vertexChainSubdivisionHomotopy R F (k + 1)).comp
          (vertexChainMap R E f (k + 1)) from congrArg (fun g ↦ g c) h
    apply Finsupp.lhom_ext
    intro v a
    simp only [LinearMap.comp_apply, vertexChainSubdivisionHomotopy_single, map_smul,
      vertexChainMap_cone, map_sub, vertexChainMap_subdivision, hk,
      vertexChainMap_boundary]
    simp [vertexChainMap, vertexChainSubdivisionHomotopy_single]

end AtiyahSinger
