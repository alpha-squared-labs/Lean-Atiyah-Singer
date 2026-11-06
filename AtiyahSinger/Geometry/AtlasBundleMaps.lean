/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame

/-!
# Smooth maps between the original atlas bundles

Public module ID: M1086.

The standard local-matrix criterion is stated for an actual fiberwise linear
map over a specified smooth base map. The same-base version is its special
case over the identity. Coordinates use the given original frame inverses;
zero extension is only a total-function convention outside the tested overlap.
This also compares a pullback atlas with the original atlas without choosing
new fibers, norms or an arbitrary smooth structure on that pullback.

Source: SG III.1, p.167, smooth complex bundle maps. The explicit atlas and
base-map formulation is the standard transition-coordinate description.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  {E : M → Type*} {F : N → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]

open Classical in
/-- Smoothness of an original complex-linear bundle map over its specified base map. -/
def IsSmoothAtlasBundleMapOver (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := m) F) (f : M → N)
    (a : ∀ x : M, E x →ₗ[ℂ] F (f x)) : Prop :=
  ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f ∧
    ∀ (i : A.Index) (j : B.Index) (k : Fin (A.rank i)),
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
        (fun x : M ↦ if hx : x ∈ (A.chart i).baseSet then
          (B.chart j ⟨f x, a x ((A.frameLinearEquiv i x hx).symm (Pi.single k 1))⟩).2
          else 0) ((A.chart i).baseSet ∩ f ⁻¹' (B.chart j).baseSet)

variable {F' : M → Type*} [∀ x, AddCommGroup (F' x)] [∀ x, Module ℂ (F' x)]
  [TopologicalSpace (TotalSpace Unit F')]

/-- Smoothness of the specified complex-linear map between two atlases on the same base. -/
def IsSmoothAtlasBundleMap (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F') (a : ∀ x : M, E x →ₗ[ℂ] F' x) : Prop :=
  IsSmoothAtlasBundleMapOver A B id a

end AtiyahSinger
