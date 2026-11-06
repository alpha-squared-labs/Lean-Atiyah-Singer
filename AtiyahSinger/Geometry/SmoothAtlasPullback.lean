/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Topology.HermitianMetricPullback
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Pullback of the original smooth complex bundle atlas

Public module ID: M1364.

Pullback along a specified smooth map retains the original chart indices,
coordinate ranks and fiber vectors. The topology is the actual pullback total
space topology. The canonical map back to the original bundle is smooth in
these same atlases, and the original smooth Hermitian form pulls back smoothly.

This is the standard smooth pullback construction (SG III.1). The local chart
certificates are implementation details of that construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n) E)
  {m : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  (f : C(N, M)) (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)

/-- Pull back a specified chart, preserving its original fiber coordinate function. -/
theorem exists_pullbackChart (i : A.Index) :
    ∃ e : Trivialization (Fin (A.rank i) → ℂ) (π Unit ((f : N → M) *ᵖ E)),
      e.baseSet = f ⁻¹' (A.chart i).baseSet ∧
        ∀ z : TotalSpace Unit ((f : N → M) *ᵖ E),
          (e z).2 = (A.chart i ⟨(f z.proj), z.snd⟩).2 := by
  /- Stage 1: use the inverse image of the original chart domain in the source. The
  forward map retains the original source base point and evaluates the same original fiber
  coordinate. Its inverse uses the original inverse chart vector at that point.
  Stage 2: the original chart identities give the two partial inverse laws.
  The pullback total topology makes both maps continuous on these domains.
  This includes empty intersections and zero-dimensional coordinate spaces;
  no choice of a fiber basis or of a new total topology is made. -/
  classical
  let e := A.chart i
  -- Keep the original total-space point when transporting the inverse fiber vector.
  let g : N × (Fin (A.rank i) → ℂ) → TotalSpace Unit ((f : N → M) *ᵖ E) :=
    fun y ↦ if hy : f y.1 ∈ e.baseSet then
      ⟨y.1, cast (congrArg E (e.proj_symm_apply' hy))
        (e.toPartialEquiv.symm (f y.1, y.2)).snd⟩
    else ⟨y.1, 0⟩
  have hgproj (y : N × (Fin (A.rank i) → ℂ)) : (g y).proj = y.1 := by
    dsimp [g]
    split_ifs <;> rfl
  have hglift (y : N × (Fin (A.rank i) → ℂ)) (hy : f y.1 ∈ e.baseSet) :
      Pullback.lift f (g y) = e.toPartialEquiv.symm (f y.1, y.2) := by
    dsimp only [g]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  -- Construct the usual pullback chart in the original Unit-model total topology.
  let t : Trivialization (Fin (A.rank i) → ℂ) (π Unit ((f : N → M) *ᵖ E)) :=
    { toFun := fun z ↦ (z.proj, (e (Pullback.lift f z)).2)
      invFun := g
      source := Pullback.lift f ⁻¹' e.source
      baseSet := f ⁻¹' e.baseSet
      target := (f ⁻¹' e.baseSet) ×ˢ Set.univ
      map_source' := by
        intro x hx
        simp only [e.source_eq, Set.mem_preimage, Pullback.lift_proj] at hx
        exact ⟨hx, Set.mem_univ _⟩
      map_target' := by
        intro y hy
        simp only [e.source_eq, Set.mem_preimage, Pullback.lift_proj, hgproj]
        exact hy.1
      left_inv' := by
        intro x hx
        have hbase : f x.proj ∈ e.baseSet := e.mem_source.mp hx
        apply TotalSpace.ext (hgproj _)
        have hpoint := (hglift (x.proj, (e (Pullback.lift f x)).2) hbase).trans
          (e.symm_apply_mk_proj hx)
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd) hpoint
      right_inv' := by
        intro y hy
        apply Prod.ext
        · exact hgproj y
        · change (e (Pullback.lift f (g y))).2 = y.2
          rw [hglift y hy.1]
          exact congrArg (fun p : M × (Fin (A.rank i) → ℂ) ↦ p.2)
            (e.apply_symm_apply' (x := y.2) hy.1)
      open_source := by
        rw [e.source_eq]
        exact e.open_baseSet.preimage
          (f.continuous.comp (Pullback.continuous_proj Unit E f))
      open_target := (e.open_baseSet.preimage f.continuous).prod isOpen_univ
      open_baseSet := e.open_baseSet.preimage f.continuous
      continuousOn_toFun :=
        (Pullback.continuous_proj Unit E f).continuousOn.prodMk
          (continuous_snd.comp_continuousOn
            (e.toOpenPartialHomeomorph.continuousOn.comp
              (Pullback.continuous_lift Unit E f).continuousOn Set.Subset.rfl))
      continuousOn_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuousOn_iff]
        refine (continuousOn_fst.prodMk
          (e.toOpenPartialHomeomorph.continuousOn_symm.comp
            (f.continuous.prodMap continuous_id).continuousOn
            (fun y hy ↦ e.mem_target.mpr hy.1))).congr ?_
        intro y hy
        exact Prod.ext (hgproj y) (hglift y hy.1)
      source_eq := by rw [e.source_eq]; rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  exact ⟨t, rfl, fun _ ↦ rfl⟩

/-- The chosen pullback chart, retaining the original fiber coordinate function. -/
def pullbackChart (i : A.Index) :
    Trivialization (Fin (A.rank i) → ℂ) (π Unit ((f : N → M) *ᵖ E)) :=
  (A.exists_pullbackChart f i).choose

include hf in
/-- The original covering, linearity and smooth transitions survive smooth pullback.
This grouped certificate supplies fields of the pullback atlas. -/
theorem pullbackChart_properties :
    (∀ x : N, ∃ i : A.Index, x ∈ (A.pullbackChart f i).baseSet) ∧
      (∀ (i : A.Index) (x : N), x ∈ (A.pullbackChart f i).baseSet →
        IsLinearMap ℂ (fun z : E (f x) ↦ (A.pullbackChart f i ⟨x, z⟩).2)) ∧
      ∀ (i j : A.Index) (a : Fin (A.rank i)),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
          (fun x : N ↦ (A.pullbackChart f j
            ((A.pullbackChart f i).toPartialEquiv.symm (x, Pi.single a 1))).2)
          ((A.pullbackChart f i).baseSet ∩ (A.pullbackChart f j).baseSet) := by
  /- Stage 1: the specified base-set identity pulls back the original cover.
  The specified fiber formula transfers A.linear on each pulled-back domain.
  Stage 2: on an overlap, the same inverse identities identify the pulled-back
  transition columns with the original columns composed with the specified base map.
  That map is smooth for the specified source and target atlases. Compose
  the original smooth transition certificates with it. No rank agreement is
  imposed on disjoint chart domains. -/
  classical
  have hbase (i : A.Index) : (A.pullbackChart f i).baseSet =
      f ⁻¹' (A.chart i).baseSet := (A.exists_pullbackChart f i).choose_spec.1
  have hcoords (i : A.Index) (z : TotalSpace Unit ((f : N → M) *ᵖ E)) :
      (A.pullbackChart f i z).2 = (A.chart i ⟨(f z.proj), z.snd⟩).2 :=
    (A.exists_pullbackChart f i).choose_spec.2 z
  -- The pullback inverse represents the same original fiber vector after applying f.
  have hinverse (i : A.Index) (x : N) (hx : x ∈ (A.pullbackChart f i).baseSet)
      (v : Fin (A.rank i) → ℂ) :
      (let z := (A.pullbackChart f i).toPartialEquiv.symm (x, v);
        (⟨(f z.proj), z.snd⟩ : TotalSpace Unit E)) =
        (A.chart i).toPartialEquiv.symm ((f x), v) := by
    let z := (A.pullbackChart f i).toPartialEquiv.symm (x, v)
    have hz : z.proj = x := (A.pullbackChart f i).proj_symm_apply' hx
    have hsource : (⟨(f z.proj), z.snd⟩ : TotalSpace Unit E) ∈ (A.chart i).source := by
      apply (A.chart i).mem_source.mpr
      change (f z.proj) ∈ (A.chart i).baseSet
      rw [hz]
      simpa only [hbase, Set.mem_preimage] using hx
    have hvalue : A.chart i ⟨(f z.proj), z.snd⟩ = ((f x), v) := by
      apply Prod.ext
      · exact ((A.chart i).proj_toFun _ hsource).trans (congrArg f hz)
      · rw [← hcoords i z]
        exact congrArg Prod.snd ((A.pullbackChart f i).apply_symm_apply' hx)
    rw [← hvalue]
    exact ((A.chart i).toPartialEquiv.left_inv hsource).symm
  constructor
  · intro x
    obtain ⟨i, hi⟩ := A.covers (f x)
    exact ⟨i, by simpa only [hbase, Set.mem_preimage] using hi⟩
  · constructor
    · intro i x hx
      have hi : (f x) ∈ (A.chart i).baseSet := by simpa only [hbase, Set.mem_preimage] using hx
      simpa only [hcoords] using A.linear i (f x) hi
    · intro i j a
      -- Smooth transition columns restrict by composition with the specified base map.
      have hs := (A.contMDiffOn_coordChange i j a).comp
        hf.contMDiffOn (fun x hx ↦ hx)
      rw [hbase i, hbase j]
      apply hs.congr
      intro x hx
      rw [hcoords]
      change (A.chart j
        (let z := (A.pullbackChart f i).toPartialEquiv.symm (x, Pi.single a 1);
          (⟨(f z.proj), z.snd⟩ : TotalSpace Unit E))).2 = _
      rw [hinverse i x (by simpa only [hbase, Set.mem_preimage] using hx.1)]
      rfl

/-- Smooth pullback with exactly the original index set, ranks and coordinates. -/
def pullback : SmoothComplexBundleAtlas (n := m) (M := N)
    ((f : N → M) *ᵖ E) where
  Index := A.Index
  rank := A.rank
  chart := A.pullbackChart f
  covers := (A.pullbackChart_properties f hf).1
  linear := (A.pullbackChart_properties f hf).2.1
  contMDiffOn_coordChange := (A.pullbackChart_properties f hf).2.2

/-- The canonical map from the actual smooth pullback is smooth in the original atlas. -/
theorem isSmoothAtlasBundleMapOver_pullback :
    IsSmoothAtlasBundleMapOver (A.pullback f hf) A f (fun _ ↦ LinearMap.id) := by
  classical
  refine ⟨hf, ?_⟩
  intro i j k
  have hbase : ((A.pullback f hf).chart i).baseSet = f ⁻¹' (A.chart i).baseSet :=
    (A.exists_pullbackChart f i).choose_spec.1
  have hs := (A.contMDiffOn_coordChange i j k).comp hf.contMDiffOn
    (s := ((A.pullback f hf).chart i).baseSet ∩ f ⁻¹' (A.chart j).baseSet)
    (fun x hx ↦ ⟨hbase.subset hx.1, hx.2⟩)
  apply hs.congr
  intro x hx
  rw [dite_eq_left hx.1]
  have hi : f x ∈ (A.chart i).baseSet := hbase.subset hx.1
  -- Equality of the original forward coordinates identifies the inverse frame vectors.
  have hframe : ((A.pullback f hf).frameLinearEquiv i x hx.1).symm (Pi.single k 1) =
      (A.frameLinearEquiv i (f x) hi).symm (Pi.single k 1) := by
    apply (A.frameLinearEquiv i (f x) hi).injective
    rw [LinearEquiv.apply_symm_apply]
    change (A.chart i ⟨f x,
      ((A.pullback f hf).frameLinearEquiv i x hx.1).symm (Pi.single k 1)⟩).2 = _
    rw [← (A.exists_pullbackChart f i).choose_spec.2
      ⟨x, ((A.pullback f hf).frameLinearEquiv i x hx.1).symm (Pi.single k 1)⟩]
    exact ((A.pullback f hf).frameLinearEquiv i x hx.1).apply_symm_apply _
  change (A.chart j ⟨f x,
    ((A.pullback f hf).frameLinearEquiv i x hx.1).symm (Pi.single k 1)⟩).2 = _
  rw [hframe]
  exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart j z).2)
    (TotalSpace.mk_cast (F := Unit) (E := E)
      ((A.chart i).proj_symm_apply' (x := Pi.single k 1) hi) _)

/-- The same original Hermitian form pulls back smoothly in the specified atlas. -/
theorem isSmoothHermitianMetric_pullback (h : ComplexBundle.ContinuousHermitianMetric E)
    (hh : A.IsSmoothHermitianMetric h) :
    (A.pullback f hf).IsSmoothHermitianMetric
      (h.pullback f) := by
  /- The selected restricted chart has the original forward fiber coordinates,
  hence its inverse frame vectors are the same original inverse frame vectors
  on the restricted domain. Each Gram entry is therefore the original Gram
  entry composed with the specified smooth map. Apply hh on that domain.
  The form and both vectors stay in E(f(x)); no auxiliary metric is selected. -/
  classical
  have hbase (i : A.Index) : (A.pullbackChart f i).baseSet =
      f ⁻¹' (A.chart i).baseSet := (A.exists_pullbackChart f i).choose_spec.1
  have hcoords (i : A.Index) (z : TotalSpace Unit ((f : N → M) *ᵖ E)) :
      (A.pullbackChart f i z).2 = (A.chart i ⟨(f z.proj), z.snd⟩).2 :=
    (A.exists_pullbackChart f i).choose_spec.2 z
  -- Equal original coordinate functions force the same inverse frame vectors.
  have hinverse (i : A.Index) (x : N)
      (hx : x ∈ ((A.pullback f hf).chart i).baseSet)
      (hx' : (f x) ∈ (A.chart i).baseSet) (v : Fin (A.rank i) → ℂ) :
      ((A.pullback f hf).frameLinearEquiv i x hx).symm v =
        (A.frameLinearEquiv i (f x) hx').symm v := by
    apply (A.frameLinearEquiv i (f x) hx').injective
    rw [LinearEquiv.apply_symm_apply]
    change (A.chart i ⟨(f x), ((A.pullback f hf).frameLinearEquiv i x hx).symm v⟩).2 = v
    rw [← hcoords i ⟨x, ((A.pullback f hf).frameLinearEquiv i x hx).symm v⟩]
    exact ((A.pullback f hf).frameLinearEquiv i x hx).apply_symm_apply v
  intro i a b
  have hs := (hh i a b).comp hf.contMDiffOn (fun x hx ↦ hx)
  have hdomain : ((A.pullback f hf).chart i).baseSet =
      (f : N → M) ⁻¹' (A.chart i).baseSet := hbase i
  apply (hs.mono hdomain.subset).congr
  intro x hxR
  have hx : (f x) ∈ (A.chart i).baseSet := hdomain.subset hxR
  -- The pulled-back form is evaluated on precisely these same two original vectors.
  dsimp only [ComplexBundle.ContinuousHermitianMetric.pullback, Function.comp_apply]
  simp only [dite_eq_left hx, dite_eq_left hxR]
  change (h.toCore (f x)).inner
      (((A.pullback f hf).frameLinearEquiv i x hxR).symm (Pi.single a 1))
      (((A.pullback f hf).frameLinearEquiv i x hxR).symm (Pi.single b 1)) =
    (h.toCore (f x)).inner
      ((A.frameLinearEquiv i (f x) hx).symm (Pi.single a 1))
      ((A.frameLinearEquiv i (f x) hx).symm (Pi.single b 1))
  exact congrArg₂ (h.toCore (f x)).inner
    (hinverse i x hxR hx (Pi.single a 1)) (hinverse i x hxR hx (Pi.single b 1))

end AtiyahSinger.SmoothComplexBundleAtlas
