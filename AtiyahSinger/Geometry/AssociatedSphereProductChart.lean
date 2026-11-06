/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.ManifoldModelChange
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual product coordinates for the selected associated sphere atlas

Public module ID: M1078.

Compose the original principal trivialization with supplied base and sphere
charts and the original base-first Euclidean sum equivalence. This chart is
smoothly compatible with the unchanged chosen associated sphere atlas. The
existence certificate for that atlas provides smooth trivializations in both
directions; it does not assert that these product charts belong to its raw atlas.

The maximal-atlas conclusion is the legitimate coordinate input for local
Sobolev and pseudodifferential transfer. It does not change the raw charted
space or assume an unavailable membership property of its chosen witness.
Sources: SG III.13.6 and the smooth associated-bundle coordinate construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

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

/-- The original principal product coordinates, flattened in the specified base-first order. -/
def associatedSphereProductChart (b : B) (c : OpenPartialHomeomorph B X)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y) :
    OpenPartialHomeomorph Z (EuclideanSpace ℝ (Fin (n + r))) := by
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  exact ((associatedSphereTrivialization S b).toOpenPartialHomeomorph.trans (c.prod d)).trans
    l.toHomeomorph.toOpenPartialHomeomorph

/-- These actual product coordinates are compatible with the same chosen associated atlas. -/
theorem associatedSphereProductChart_mem_maximalAtlas (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : d ∈ atlas Y (OrthogonalSphere r)) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    associatedSphereProductChart S b c d ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z := by
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let J := (𝓡 n).prod (𝓡 r)
  let I := 𝓘(ℝ, X × Y)
  have hJI : J = I := modelWithCornersSelf_prod.symm
  let : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace _ _ _ _
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let e := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let := isManifold_linearModelChartedSpace l Z
  let t := (associatedSphereTrivialization S b).toOpenPartialHomeomorph
  let p := c.prod d
  have hp : p ∈ IsManifold.maximalAtlas J ∞ (B × OrthogonalSphere r) :=
    IsManifold.mem_maximalAtlas_prod
      (IsManifold.subset_maximalAtlas hc) (IsManifold.subset_maximalAtlas hd)
  rw [hJI] at hp
  -- The public certificate supplies the same trivialization, in both original directions.
  have ht := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
  have hforward : ContMDiffOn (𝓡 (n + r)) J ∞ t t.source :=
    ht.1.comp e.symm.contMDiff.contMDiffOn (fun _ hz ↦ hz)
  have hinverse : ContMDiffOn J (𝓡 (n + r)) ∞ t.symm t.target :=
    e.contMDiff.comp_contMDiffOn ht.2
  rw [hJI] at hforward hinverse
  -- Compose the actual product chart and exact linear model change, preserving both domains.
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have h : ContMDiffOn (𝓡 (n + r)) I ∞ (p ∘ t)
        (associatedSphereProductChart S b c d).source :=
      (contMDiffOn_of_mem_maximalAtlas hp).comp
        (hforward.mono (fun _ hz ↦ hz.1.1)) (fun _ hz ↦ hz.1.2)
    exact l.contDiff.contMDiff.comp_contMDiffOn h
  · have hlinear : ContMDiffOn (𝓡 (n + r)) I ∞ l.symm
        (associatedSphereProductChart S b c d).target := l.symm.contDiff.contMDiff.contMDiffOn
    have hprod : ContMDiffOn (𝓡 (n + r)) I ∞ (p.symm ∘ l.symm)
        (associatedSphereProductChart S b c d).target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hp).comp hlinear (fun _ hz ↦ hz.2.1)
    exact hinverse.comp hprod (fun _ hz ↦ hz.2.2)

end AtiyahSinger
