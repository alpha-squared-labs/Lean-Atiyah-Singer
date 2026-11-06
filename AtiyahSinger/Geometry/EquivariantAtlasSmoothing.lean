/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.EquivariantRankSmoothing
public import AtiyahSinger.Geometry.EquivariantSmoothImageModel
public import AtiyahSinger.Geometry.NativeSmoothAtlas
public import AtiyahSinger.Geometry.SmoothAtlasTransport

/-!
# Smooth original equivariant bundles with locally varying rank

Public module ID: M1172.

Joint smoothness is the moving-frame matrix condition in an original
SmoothComplexBundleAtlas whose chart ranks may vary. It retains the
specified jointly smooth base action and the original continuous linear
action on the original fibers and total-space topology. Smoothness
separately for each group element is not the condition used here.

The fixed-rank native formulation implies this formulation on its own atlas.
For a compact finite-dimensional Lie group, a continuous locally finite-rank
equivariant bundle over a compact smooth base admits a compatible smooth
atlas on its original fibers. Transport the smooth finite image atlas back
through its equivariant isomorphism and select a finite covering subatlas.
The original continuous frames are not assumed smooth, and the conclusion
retains the original fiber family, topology and action without a global rank.

Sources: SG III.1 and III.9, p.167 and pp.211--215, for smooth bundle charts
and smooth group actions; Karoubi II.1.26--1.29 for the locally constant
rank decomposition. The equivariant smoothing step is a project supplement
to those sources, as in EquivariantBundleSmoothing.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

section SmoothAction

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]

open Classical in
/-- Joint smoothness of the original action in the specified variable-rank smooth atlas. -/
def EquivariantStructure.IsSmoothAtlas
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
    {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    (σ : EquivariantStructure G E) (A : SmoothComplexBundleAtlas (n := n) E) : Prop :=
  ∀ (i j : A.Index) (k : Fin (A.rank i)),
    ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
      (fun p : G × M ↦ if hx : p.2 ∈ (A.chart i).baseSet then
        (A.chart j ⟨p.1 • p.2,
          σ.linearMap p.1 p.2 ((A.frameLinearEquiv i p.2 hx).symm (Pi.single k 1))⟩).2
        else 0)
      {p : G × M | p.2 ∈ (A.chart i).baseSet ∧ p.1 • p.2 ∈ (A.chart j).baseSet}

variable {r : ℕ} {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- The original native smooth action is smooth for its own converted atlas. -/
theorem EquivariantStructure.isSmoothAtlas_native
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (hσ : σ.IsSmooth (n := n) (r := r) IG) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    σ.IsSmoothAtlas IG (nativeSmoothComplexBundleAtlas (n := n) (r := r) E) := by
  /- Stage 1: every chart of nativeSmoothComplexBundleAtlas is an actual
  designated native chart followed by EuclideanSpace.equiv. Its inverse
  linear frame therefore takes Pi.single k 1 to the same original vector
  as the native inverse frame takes EuclideanSpace.single k 1. The phantom
  model change preserves the total topology and the original fiber maps.
  Stage 2: on the displayed moving overlap the source membership test is
  true. Thus each new column is EuclideanSpace.equiv applied to precisely
  the old column in hσ, for the same g, x and two native frames. Compose
  that joint smooth map with this fixed real-smooth linear equivalence.
  The original ContMDiffSMul instance remains an explicit prerequisite,
  including at rank zero when there are no columns to test. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  intro i j k
  let : MemTrivializationAtlas i.val := i.property
  let : MemTrivializationAtlas j.val := j.property
  let e₀ := EuclideanSpace.equiv (Fin r) ℂ
  -- Compose the same original joint column with the fixed finite-coordinate equivalence.
  have hcolumn := hσ i.val j.val k
  have hmodel := (e₀.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
  apply (hmodel.comp_contMDiffOn hcolumn).congr
  intro p hp
  have hi : p.2 ∈ (A.chart i).baseSet := hp.1
  -- Identify the two inverse-frame vectors by applying the actual converted frame.
  have hframe : (A.frameLinearEquiv i p.2 hi).symm (Pi.single k 1) =
      i.val.symmL ℂ p.2 (EuclideanSpace.single k 1) := by
    apply (A.frameLinearEquiv i p.2 hi).injective
    rw [LinearEquiv.apply_symm_apply]
    change Pi.single k 1 = e₀
      ((i.val ⟨p.2, i.val.symmL ℂ p.2 (EuclideanSpace.single k 1)⟩).2)
    rw [← i.val.continuousLinearMapAt_apply_of_mem ℂ hp.1,
      i.val.continuousLinearMapAt_symmL hp.1]
    rfl
  change (if hx : p.2 ∈ (A.chart i).baseSet then
    (A.chart j ⟨p.1 • p.2,
      σ.linearMap p.1 p.2 ((A.frameLinearEquiv i p.2 hx).symm (Pi.single k 1))⟩).2
    else 0) = _
  rw [dite_eq_left hi, hframe]
  rfl

end SmoothAction

section Smoothing

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

include hDim hLie hGC hGT hM hT hSC hC hAction hE

set_option linter.unusedSectionVars false in

/-- The original locally finite-rank equivariant bundle admits a compatible smooth atlas. -/
theorem EquivariantStructure.exists_smoothAtlas (σ : EquivariantStructure G E) :
    ∃ A : SmoothComplexBundleAtlas (n := n) E, σ.IsSmoothAtlas 𝓘(ℝ, VG) A := by
  classical
  obtain ⟨p, hp⟩ := σ.exists_smooth_image_model (VG := VG) (n := n)
  let := IdempotentMatrix.fiberTotalSpaceTopology p
  obtain ⟨τ, e, he, B, hB⟩ := hp
  -- Compactness gives a small finite subatlas without changing any chart.
  -- Its index can therefore be lifted to the original arbitrary index universe.
  let B₀ := B.finiteSubatlas
  have hB₀ : τ.IsSmoothAtlas 𝓘(ℝ, VG) B₀ := by
    intro i j k
    exact hB _ _ k
  let A := e.smoothAtlas B₀
  have hA : σ.IsSmoothAtlas 𝓘(ℝ, VG) A := by
    intro i j k
    apply (hB₀ i j k).congr
    intro z hz
    have hx : z.2 ∈ (A.chart i).baseSet := hz.1
    have hx' : z.2 ∈ (B₀.chart i).baseSet := hx
    -- The same equivariant isomorphism transports both the input frame and
    -- the output action vector, so the moving matrices agree pointwise.
    have hframe : e.linearEquiv z.2 ((A.frameLinearEquiv i z.2 hx).symm (Pi.single k 1)) =
        (B₀.frameLinearEquiv i z.2 hx').symm (Pi.single k 1) := by
      apply (B₀.frameLinearEquiv i z.2 hx').injective
      rw [LinearEquiv.apply_symm_apply]
      change A.frameLinearEquiv i z.2 hx ((A.frameLinearEquiv i z.2 hx).symm _) = _
      exact LinearEquiv.apply_symm_apply _ _
    simp only [dite_eq_left hx, dite_eq_left hx']
    change (B₀.chart j ⟨z.1 • z.2,
      e.linearEquiv (z.1 • z.2) (σ.linearMap z.1 z.2
        ((A.frameLinearEquiv i z.2 hx).symm (Pi.single k 1)))⟩).2 = _
    have he' : e.linearEquiv (z.1 • z.2) (σ.linearMap z.1 z.2
        ((A.frameLinearEquiv i z.2 hx).symm (Pi.single k 1))) =
        τ.linearMap z.1 z.2 (e.linearEquiv z.2
          ((A.frameLinearEquiv i z.2 hx).symm (Pi.single k 1))) := he _ _ _
    exact congrArg (fun v : p.fiber (z.1 • z.2) ↦ (B₀.chart j ⟨z.1 • z.2, v⟩).2)
      (he'.trans (congrArg (τ.linearMap z.1 z.2) hframe))
  refine ⟨{ Index := ULift A.Index
            rank := fun i ↦ A.rank i.down
            chart := fun i ↦ A.chart i.down
            covers := fun x ↦ by
              obtain ⟨i, hi⟩ := A.covers x
              exact ⟨⟨i⟩, hi⟩
            linear := fun i ↦ A.linear i.down
            contMDiffOn_coordChange := fun i j ↦ A.contMDiffOn_coordChange i.down j.down }, ?_⟩
  intro i j k
  exact hA i.down j.down k

end Smoothing

end AtiyahSinger.ComplexBundle
