/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereProductChart
public import AtiyahSinger.Geometry.AtlasChartLocalization

/-!
# Base support of extension through the original associated product chart

Public module ID: M0081.

The base projection of the full coordinate Schwartz support controls extension,
even when the output cutoff is a larger plateau. The proof reads the actual
principal trivialization and the original coordinate concatenation. This is
used when summing local vertical pieces over a native base partition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle

/-- Extension vanishes away from the actual base projection of the full Schwartz support. -/
theorem associatedSphereChart_extendedFunction_eq_zero_of_notMem_base
    (b : B) (c : OpenPartialHomeomorph B X)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let CP := associatedSphereProductChart S b c d
    ∀ (E : Z → Type*) [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
      [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n + r) E)
      (D : AtlasChartCutoff A CP)
      (v : 𝓢(XY, EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) (K : Set X),
      (∀ x ∈ tsupport v, (EuclideanSpace.finAddEquivProd x).1 ∈ K) →
      ∀ z : Z, πS z ∉ c.symm '' K → D.extendedFunction v z = 0 := by
  classical
  let := associatedSphereChartedSpace S
  let ef := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace ef.symm Z
  let CP : OpenPartialHomeomorph Z XY := associatedSphereProductChart S b c d
  dsimp only
  intro E _ _ _ A D v K hv z hz
  let t := associatedSphereTrivialization S b
  by_cases hvalid : z ∈ CP.source ∩ (A.chart D.frameIndex).baseSet
  · -- The principal chart recovers the very same original base point.
    have hzt : z ∈ t.source := hvalid.1.1.1
    have hxc : (t z).1 ∈ c.source := hvalid.1.1.2.1
    have hprojection : (t z).1 = πS z := t.proj_toFun z hzt
    have hcoordinates : ef (CP z) = (c (t z).1, d (t z).2) :=
      ef.apply_symm_apply _
    have hnot : CP z ∉ tsupport v := by
      intro h
      apply hz
      refine ⟨c (t z).1, ?_, ?_⟩
      · have hbase := hv (CP z) h
        rwa [hcoordinates] at hbase
      · exact (c.left_inv hxc).trans hprojection
    -- Vanishing of the coordinate Schwartz output is independent of the plateau width.
    have hzero : v (CP z) = 0 := image_eq_zero_of_notMem_tsupport hnot
    dsimp only [CP] at hvalid hzero
    simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hvalid, hzero,
      map_zero, smul_zero]
  · dsimp only [CP] at hvalid
    simp only [AtlasChartCutoff.extendedFunction, dite_eq_right hvalid]

end AtiyahSinger
