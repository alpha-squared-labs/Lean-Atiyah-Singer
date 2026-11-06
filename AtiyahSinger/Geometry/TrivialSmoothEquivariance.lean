/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth equivariance for the one-element group

Public module ID: M1503.

The original one-element group has its zero-dimensional vector-space chart.
Every action of this group on an original smooth bundle is smooth: its only
fiber map is the identity, so its matrix columns are the original transition
columns. These adapters allow ordinary constructions to use the equivariant
stabilization and direct-sum theorems without changing the underlying objects.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The one-element group, with its existing self chart, is a compact Lie group. -/
instance punitLieGroup : LieGroup 𝓘(ℝ, PUnit.{1}) ∞ PUnit.{1} where
  contMDiff_mul := by
    simpa using (contMDiff_const (c := (1 : PUnit.{1})) :
      ContMDiff (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, PUnit.{1})) 𝓘(ℝ, PUnit.{1}) ∞ (fun _ ↦ (1 : PUnit.{1})))
  contMDiff_inv := by
    simpa using (contMDiff_const (c := (1 : PUnit.{1})) :
      ContMDiff 𝓘(ℝ, PUnit.{1}) 𝓘(ℝ, PUnit.{1}) ∞ (fun _ ↦ (1 : PUnit.{1})))

/-- The standard one-element-group action is the smooth second projection. -/
theorem punitContMDiffSMul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ContMDiffSMul 𝓘(ℝ, PUnit.{1}) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ PUnit.{1} M := by
  constructor
  convert (contMDiff_snd : ContMDiff
    (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : PUnit.{1} × M ↦ p.2)) using 1

namespace ComplexBundle

/-- Every equivariant structure for the one-element group preserves the original smooth atlas. -/
theorem EquivariantStructure.isSmooth_of_subsingleton
    {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
    [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
    [Group G] [Subsingleton G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ChartedSpace HG G]
    {n r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MulAction G M] [ContinuousSMul G M]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
    {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) : σ.IsSmooth (n := n) (r := r) IG := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro e f he hf j
  -- The only group element acts by the identity on the same total space.
  have hid (g : G) (x : M) (v : E x) :
      (⟨g • x, σ.linearMap g x v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    rw [Subsingleton.elim g 1]
    exact σ.one_map x v
  have hcoord := ((ContinuousLinearMap.apply ℂ
    (EuclideanSpace ℂ (Fin r)) (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn
        (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E) e f)
  let U : Set (G × M) := {p | p.2 ∈ e.baseSet ∧ p.1 • p.2 ∈ f.baseSet}
  have hmap : Set.MapsTo Prod.snd U (e.baseSet ∩ f.baseSet) := by
    intro p hp
    exact ⟨hp.1, by simpa only [Subsingleton.elim p.1 (1 : G), one_smul] using hp.2⟩
  have hs := hcoord.comp
    (contMDiffOn_snd (I := IG) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) hmap
  apply hs.congr
  intro p hp
  have ht := congrArg (fun z : TotalSpace Unit E ↦
    (f (⟨z.proj, z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)).2)
    (hid p.1 p.2 (e.symmL ℂ p.2 (EuclideanSpace.single j 1)))
  rw [ht]
  change (f ⟨p.2, e.symmL ℂ p.2 (EuclideanSpace.single j 1)⟩).2 =
    (e.coordChangeL ℂ f p.2) (EuclideanSpace.single j 1)
  simpa only [e.symmL_apply hp.1] using
    (e.coordChangeL_apply f (hmap hp) (EuclideanSpace.single j (1 : ℂ))).symm

end ComplexBundle

end AtiyahSinger
