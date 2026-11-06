/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.HermitianFlagManifold
public import AtiyahSinger.Geometry.SmoothAtlasPullback
public import AtiyahSinger.Geometry.SmoothAtlasRangeLine
public import AtiyahSinger.Topology.HermitianFlagSplitting

/-!
# Smooth splitting into the original tautological ranges

Public module ID: M1401.

C01, SG III.11.1, pp.225--226. The lines are the ranges of the same original
projection tuple; their sum and pullback retain their previously specified
Unit total-space topologies. The smooth atlases come from actual projected
local frames. The pullback projection is smooth over the original A-atlas,
the line inclusions are smooth, and the sum coordinates are smooth. These
compatibilities prevent the choice of unrelated smooth bundle structures.

The final smooth equivalence is precisely hermitianFlagSplitting: its forward
map adds original vectors, and its inverse applies the specified projections.
No alternative splitting witness or altered Hermitian metric is introduced.
Selections and certificates reuse that same existence witness. At rank zero
the line family is empty and the base is kept.
-/

@[expose] public noncomputable section

universe u v w

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable (r : ℕ) {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (E : M → Type v) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  (A : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    SmoothComplexBundleAtlas.{w} (n := n) E)
  (hh : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    A.IsSmoothHermitianMetric h)

attribute [local instance] hermitianFlagTopology hermitianFlagLineTopology
  hermitianFlagSumTopology

include hM hh

set_option maxHeartbeats 1600000 in
-- Elaborate the original flag projections and compatible line, sum and pullback atlases.
/-- Actual projected local frames give compatible smooth line, sum and pullback atlases. -/
theorem exists_hermitianFlag_smoothSplittingAtlases :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := hermitianFlagChartedSpace r E h A hh
    ∃ L : ∀ i : Fin r, SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
        (HermitianFlagLine r E h i),
      ∃ S : SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
          (HermitianFlagSum r E h),
        ∃ P : SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
            ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → M) *ᵖ E),
          IsSmoothAtlasBundleMapOver P A (hermitianFlagProjection r E h)
              (fun _ ↦ LinearMap.id) ∧
            (∀ i : Fin r, IsSmoothAtlasBundleMap (L i) P
              (fun p ↦ (LinearMap.range (p.2.val i).toLinearMap).subtype)) ∧
            (∀ i : Fin r, IsSmoothAtlasBundleMap S (L i) (fun _ ↦ LinearMap.proj i)) ∧
            IsSmoothAtlasBundleMap S P
              (fun p ↦ ((hermitianFlagSplitting r E h).linearEquiv p).toLinearMap) ∧
            IsSmoothAtlasBundleMap P S
              (fun p ↦ ((hermitianFlagSplitting r E h).linearEquiv p).symm.toLinearMap) :=
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := hermitianFlagChartedSpace r E h A hh
  let Q := HermitianFlagBundle r E h
  let f : C(Q, M) := hermitianFlagProjection r E h
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f :=
    (exists_hermitianFlag_atlas r E h A hh).choose_spec.2.1
  -- Pull back the same frames; lift only the index universe required by the original statement.
  let B : SmoothComplexBundleAtlas.{max u v w} (n := n) E :=
    { Index := ULift.{max u v w} A.Index
      rank := fun i ↦ A.rank i.down
      chart := fun i ↦ A.chart i.down
      covers := fun x ↦ by
        obtain ⟨i, hi⟩ := A.covers x
        exact ⟨⟨i⟩, hi⟩
      linear := fun i ↦ A.linear i.down
      contMDiffOn_coordChange := fun i j ↦ A.contMDiffOn_coordChange i.down j.down }
  let P := B.pullback f hf
  have hbase (i : P.Index) : (P.chart i).baseSet = f ⁻¹' (A.chart i.down).baseSet :=
    (B.exists_pullbackChart f i).choose_spec.1
  have hcoords (i : P.Index) (z : TotalSpace Unit ((f : Q → M) *ᵖ E)) :
      (P.chart i z).2 = (A.chart i.down ⟨f z.proj, z.snd⟩).2 :=
    (B.exists_pullbackChart f i).choose_spec.2 z
  have hframe (i : P.Index) (q : Q) (hq : q ∈ (P.chart i).baseSet)
      (v : Fin (P.rank i) → ℂ) :
      (P.frameLinearEquiv i q hq).symm v =
        (A.frameLinearEquiv i.down (f q) ((hbase i).subset hq)).symm v := by
    apply (A.frameLinearEquiv i.down (f q) ((hbase i).subset hq)).injective
    rw [LinearEquiv.apply_symm_apply]
    change (A.chart i.down ⟨f q, (P.frameLinearEquiv i q hq).symm v⟩).2 = v
    rw [← hcoords i ⟨q, (P.frameLinearEquiv i q hq).symm v⟩]
    exact (P.frameLinearEquiv i q hq).apply_symm_apply v
  have htoA : IsSmoothAtlasBundleMapOver P A f (fun _ ↦ LinearMap.id) := by
    refine ⟨hf, ?_⟩
    intro i j k
    exact (B.isSmoothAtlasBundleMapOver_pullback f hf).2 i ⟨j⟩ k
  -- The selected total atlas makes the actual diagonal projector columns smooth.
  -- On different frames, multiply by the original smooth transition matrix.
  have hprojector (j : Fin r) : IsSmoothAtlasBundleMap P P
      (fun q : Q ↦ (q.2.val j).toLinearMap) := by
    refine ⟨contMDiff_id, ?_⟩
    intro i l k
    let d (q : Q) : Fin (A.rank i.down) → ℂ :=
      if hq : q.1 ∈ (A.chart i.down).baseSet then
        A.frameLinearEquiv i.down q.1 hq
          (q.2.val j ((A.frameLinearEquiv i.down q.1 hq).symm (Pi.single k 1)))
      else 0
    let c (a : Fin (A.rank i.down)) (q : Q) : Fin (A.rank l.down) → ℂ :=
      (A.chart l.down ((A.chart i.down).toPartialEquiv.symm (q.1, Pi.single a 1))).2
    have hd : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
        𝓘(ℝ, Fin (A.rank i.down) → ℂ) ∞ d (f ⁻¹' (A.chart i.down).baseSet) :=
      (exists_hermitianFlag_atlas r E h A hh).choose_spec.2.2.2.2 i.down j k
    let U := (P.chart i).baseSet ∩ (P.chart l).baseSet
    have hc (a : Fin (A.rank i.down)) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
          𝓘(ℝ, Fin (A.rank l.down) → ℂ) ∞ (c a) U := by
      exact (A.contMDiffOn_coordChange i.down l.down a).comp hf.contMDiffOn
        (fun q hq ↦ ⟨(hbase i).subset hq.1, (hbase l).subset hq.2⟩)
    have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
        𝓘(ℝ, Fin (A.rank l.down) → ℂ) ∞ (fun q ↦ ∑ a, d q a • c a q) U := by
      apply contMDiffOn_finsetSum
      intro a _
      have hd' := ((contMDiffOn_pi_space.mp hd) a).mono
        (fun q (hq : q ∈ U) ↦ (hbase i).subset hq.1)
      have hmul : ContDiff ℝ ∞
          (fun z : ℂ × (Fin (A.rank l.down) → ℂ) ↦ z.1 • z.2) := contDiff_smul
      exact hmul.contMDiff.comp_contMDiffOn (hd'.prodMk_space (hc a))
    apply hs.congr
    intro q hq
    rw [dite_eq_left hq.1, hcoords, hframe i q hq.1]
    have hi : q.1 ∈ (A.chart i.down).baseSet := (hbase i).subset hq.1
    have hl : q.1 ∈ (A.chart l.down).baseSet := (hbase l).subset hq.2
    let v := q.2.val j ((A.frameLinearEquiv i.down q.1 hi).symm (Pi.single k 1))
    let w := A.frameLinearEquiv i.down q.1 hi v
    let T := (A.frameLinearEquiv l.down q.1 hl).toLinearMap.comp
      (A.frameLinearEquiv i.down q.1 hi).symm.toLinearMap
    have hcol (a : Fin (A.rank i.down)) : T (Pi.single a 1) = c a q := by
      exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart l.down z).2)
        (TotalSpace.mk_cast (F := Unit) (E := E)
          ((A.chart i.down).proj_symm_apply' (x := Pi.single a 1) hi) _)
    have hexpand := congrArg T ((Pi.basisFun ℂ (Fin (A.rank i.down))).sum_repr w)
    simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, hcol] at hexpand
    have hvalue : T w = A.frameLinearEquiv l.down q.1 hl v := by
      change A.frameLinearEquiv l.down q.1 hl
        ((A.frameLinearEquiv i.down q.1 hi).symm
          (A.frameLinearEquiv i.down q.1 hi v)) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [hvalue] at hexpand
    have hdq : d q = w := by
      simp only [d, dite_eq_left hi]
      rfl
    simp_rw [hdq]
    change A.frameLinearEquiv l.down q.1 hl v = ∑ a, w a • c a q
    exact hexpand.symm
  -- Each original range is a smooth line, with smooth inclusion and actual projector into it.
  have hrange (j : Fin r) :
      ∃ L : SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
          (HermitianFlagLine r E h j),
        IsSmoothAtlasBundleMap L P
            (fun q ↦ (LinearMap.range (q.2.val j).toLinearMap).subtype) ∧
          IsSmoothAtlasBundleMap P L (fun q ↦ (q.2.val j).toLinearMap.rangeRestrict) := by
    exact P.exists_rangeLine_smoothAtlas (fun q : Q ↦ (q.2.val j).toLinearMap)
      (hprojector j) (fun q ↦ q.2.property.2.1 j)
  choose L hL using hrange
  -- Transport the pullback atlas through the unchanged sum/projection isomorphism.
  let e := hermitianFlagSplitting r E h
  let S := e.smoothAtlas P
  have hforward := e.isSmoothAtlasBundleMap_smoothAtlas P
  have hbackward := e.isSmoothAtlasBundleMap_symm_smoothAtlas P
  refine ⟨L, S, P, htoA, fun j ↦ (hL j).1, ?_, hforward, hbackward⟩
  intro j
  have hcomp := (hL j).2.comp hforward
  have heq : (fun q : Q ↦ ((q.2.val j).toLinearMap.rangeRestrict).comp
      (e.toHom.linearMap q)) =
      (fun _ : Q ↦ LinearMap.proj j) := by
    funext q
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    exact (hermitianFlagSplitting_properties r E h).1 q s j
  exact (congrArg (fun a ↦ IsSmoothAtlasBundleMap S (L j) a) heq).mp hcomp

/-- The selected smooth atlas on each original range line. -/
@[reducible]
def hermitianFlagLineSmoothAtlas (i : Fin r) :
    letI := hermitianFlagChartedSpace r E h A hh
    SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1)) (HermitianFlagLine r E h i) :=
  (exists_hermitianFlag_smoothSplittingAtlases r E h A hh).choose i

/-- The selected smooth atlas on the original finite same-base sum. -/
@[reducible]
def hermitianFlagSumSmoothAtlas :
    letI := hermitianFlagChartedSpace r E h A hh
    SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1)) (HermitianFlagSum r E h) :=
  (exists_hermitianFlag_smoothSplittingAtlases r E h A hh).choose_spec.choose

/-- The selected pullback atlas, compatible with the specified original A-frames. -/
@[reducible]
def hermitianFlagPullbackSmoothAtlas :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := hermitianFlagChartedSpace r E h A hh
    SmoothComplexBundleAtlas.{max u v w} (n := n + r * (r - 1))
      ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → M) *ᵖ E) :=
  (exists_hermitianFlag_smoothSplittingAtlases r E h A hh).choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- Compatibility of the chosen atlases with the original projection, inclusions and components. -/
def hermitianFlagSmoothAtlases_compatibility :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := hermitianFlagChartedSpace r E h A hh
    IsSmoothAtlasBundleMapOver (hermitianFlagPullbackSmoothAtlas r E h A hh) A
        (hermitianFlagProjection r E h) (fun _ ↦ LinearMap.id) ∧
      (∀ i : Fin r, IsSmoothAtlasBundleMap (hermitianFlagLineSmoothAtlas r E h A hh i)
        (hermitianFlagPullbackSmoothAtlas r E h A hh)
        (fun p ↦ (LinearMap.range (p.2.val i).toLinearMap).subtype)) ∧
      ∀ i : Fin r, IsSmoothAtlasBundleMap (hermitianFlagSumSmoothAtlas r E h A hh)
        (hermitianFlagLineSmoothAtlas r E h A hh i) (fun _ ↦ LinearMap.proj i) := by
  -- All three structural maps use the same selected triple of original atlases.
  have hExists := exists_hermitianFlag_smoothSplittingAtlases r E h A hh
  have hcompat := hExists.choose_spec.choose_spec.choose_spec
  exact ⟨hcompat.1, hcompat.2.1, hcompat.2.2.1⟩

/-- The original finite-sum splitting map is smooth in the selected compatible atlases. -/
theorem isSmooth_hermitianFlagSplitting :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := hermitianFlagChartedSpace r E h A hh
    IsSmoothAtlasBundleMap (hermitianFlagSumSmoothAtlas r E h A hh)
      (hermitianFlagPullbackSmoothAtlas r E h A hh)
      (fun p ↦ ((hermitianFlagSplitting r E h).linearEquiv p).toLinearMap) := by
  /- The selected projected local frames make the actual inclusions smooth.
  In their product coordinates the original splitting adds their vectors.
  Its local matrix columns are the same smooth inclusions, as recorded in
  the single selected smooth-splitting atlas existence certificate. -/
  have hExists := exists_hermitianFlag_smoothSplittingAtlases r E h A hh
  have hspec := hExists.choose_spec.choose_spec.choose_spec
  exact hspec.2.2.2.1

/-- The inverse of that exact splitting is smooth and still applies the original projectors. -/
theorem isSmooth_hermitianFlagSplitting_symm :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := hermitianFlagChartedSpace r E h A hh
    IsSmoothAtlasBundleMap (hermitianFlagPullbackSmoothAtlas r E h A hh)
      (hermitianFlagSumSmoothAtlas r E h A hh)
      (fun p ↦ ((hermitianFlagSplitting r E h).linearEquiv p).symm.toLinearMap) := by
  /- The original inverse applies each smooth projector and then reads its
  range-line coordinate in the selected nonzero projected local frame.
  These columns are exactly the smooth inverse columns in the same selected
  existence certificate; neither the splitting nor its inverse is replaced. -/
  have hExists := exists_hermitianFlag_smoothSplittingAtlases r E h A hh
  have hspec := hExists.choose_spec.choose_spec.choose_spec
  exact hspec.2.2.2.2

end AtiyahSinger.ComplexBundle
