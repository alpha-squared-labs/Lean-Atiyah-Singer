/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Topology.BundleRestriction
public import AtiyahSinger.Topology.HermitianMetricPullback
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Open restriction of the original smooth bundle atlas

Public module ID: M1366.

C01. Restriction keeps the original chart indices, coordinate ranks and fiber
coordinate functions. Only the base is restricted to an open submanifold. The
total topology is the existing pullback topology. In particular this operation
does not select a new smooth structure on a merely isomorphic bundle.

The chart certificates below are implementation components of ordinary smooth
bundle restriction, used for the actual clopen rank strata in the splitting
principle. Sources: SG III.1 and Hatcher VBKT Section 1.1. These sources do not
number the individual chart-conversion formulas as separate mathematical lemmas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n) E)
  (U : Opens M)

/-- Restrict a specified chart, preserving its original fiber coordinate function. -/
theorem exists_restrictOpenChart (i : A.Index) :
    ∃ e : Trivialization (Fin (A.rank i) → ℂ) (π Unit (ComplexBundle.Restrict E U)),
      e.baseSet = Subtype.val ⁻¹' (A.chart i).baseSet ∧
        ∀ z : TotalSpace Unit (ComplexBundle.Restrict E U),
          (e z).2 = (A.chart i ⟨z.proj.val, z.snd⟩).2 := by
  /- Stage 1: use the inverse image of the original chart domain in U. The
  forward map retains the U base point and evaluates the same original fiber
  coordinate. Its inverse uses the original inverse chart vector at that point.
  Stage 2: the original chart identities give the two partial inverse laws.
  The pullback total topology makes both maps continuous on these domains.
  This includes empty intersections and zero-dimensional coordinate spaces;
  no choice of a fiber basis or of a new total topology is made. -/
  classical
  let e := A.chart i
  let f : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Keep the original total-space point when transporting the inverse fiber vector.
  let g : U × (Fin (A.rank i) → ℂ) → TotalSpace Unit (ComplexBundle.Restrict E U) :=
    fun y ↦ if hy : f y.1 ∈ e.baseSet then
      ⟨y.1, cast (congrArg E (e.proj_symm_apply' hy))
        (e.toPartialEquiv.symm (f y.1, y.2)).snd⟩
    else ⟨y.1, 0⟩
  have hgproj (y : U × (Fin (A.rank i) → ℂ)) : (g y).proj = y.1 := by
    dsimp [g]
    split_ifs <;> rfl
  have hglift (y : U × (Fin (A.rank i) → ℂ)) (hy : f y.1 ∈ e.baseSet) :
      Pullback.lift f (g y) = e.toPartialEquiv.symm (f y.1, y.2) := by
    dsimp only [g]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  -- Construct the usual pullback chart in the original Unit-model total topology.
  let t : Trivialization (Fin (A.rank i) → ℂ) (π Unit (ComplexBundle.Restrict E U)) :=
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

/-- The specified original chart restricted to the actual open subspace. -/
def restrictOpenChart (i : A.Index) :
    Trivialization (Fin (A.rank i) → ℂ) (π Unit (ComplexBundle.Restrict E U)) :=
  (A.exists_restrictOpenChart U i).choose

/-- The original covering, linearity and smooth transitions survive open restriction.
This grouped certificate supplies fields of the restricted atlas. -/
theorem restrictOpenChart_properties :
    (∀ x : U, ∃ i : A.Index, x ∈ (A.restrictOpenChart U i).baseSet) ∧
      (∀ (i : A.Index) (x : U), x ∈ (A.restrictOpenChart U i).baseSet →
        IsLinearMap ℂ (fun z : E x.val ↦ (A.restrictOpenChart U i ⟨x, z⟩).2)) ∧
      ∀ (i j : A.Index) (a : Fin (A.rank i)),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
          (fun x : U ↦ (A.restrictOpenChart U j
            ((A.restrictOpenChart U i).toPartialEquiv.symm (x, Pi.single a 1))).2)
          ((A.restrictOpenChart U i).baseSet ∩ (A.restrictOpenChart U j).baseSet) := by
  /- Stage 1: the specified base-set identity pulls back the original cover.
  The specified fiber formula transfers A.linear on each pulled-back domain.
  Stage 2: on an overlap, the same inverse identities identify the restricted
  transition columns with the original columns composed with U's inclusion.
  That inclusion is smooth for the inherited open-submanifold atlas. Compose
  the original smooth transition certificates with it. No rank agreement is
  imposed on disjoint chart domains. -/
  classical
  have hbase (i : A.Index) : (A.restrictOpenChart U i).baseSet =
      Subtype.val ⁻¹' (A.chart i).baseSet := (A.exists_restrictOpenChart U i).choose_spec.1
  have hcoords (i : A.Index) (z : TotalSpace Unit (ComplexBundle.Restrict E U)) :
      (A.restrictOpenChart U i z).2 = (A.chart i ⟨z.proj.val, z.snd⟩).2 :=
    (A.exists_restrictOpenChart U i).choose_spec.2 z
  -- The selected restricted inverse is the same original total-space point after inclusion.
  have hinverse (i : A.Index) (x : U) (hx : x ∈ (A.restrictOpenChart U i).baseSet)
      (v : Fin (A.rank i) → ℂ) :
      (let z := (A.restrictOpenChart U i).toPartialEquiv.symm (x, v);
        (⟨z.proj.val, z.snd⟩ : TotalSpace Unit E)) =
        (A.chart i).toPartialEquiv.symm (x.val, v) := by
    let z := (A.restrictOpenChart U i).toPartialEquiv.symm (x, v)
    have hz : z.proj = x := (A.restrictOpenChart U i).proj_symm_apply' hx
    have hsource : (⟨z.proj.val, z.snd⟩ : TotalSpace Unit E) ∈ (A.chart i).source := by
      apply (A.chart i).mem_source.mpr
      change z.proj.val ∈ (A.chart i).baseSet
      rw [hz]
      simpa only [hbase, Set.mem_preimage] using hx
    have hvalue : A.chart i ⟨z.proj.val, z.snd⟩ = (x.val, v) := by
      apply Prod.ext
      · exact ((A.chart i).proj_toFun _ hsource).trans (congrArg Subtype.val hz)
      · rw [← hcoords i z]
        exact congrArg Prod.snd ((A.restrictOpenChart U i).apply_symm_apply' hx)
    rw [← hvalue]
    exact ((A.chart i).toPartialEquiv.left_inv hsource).symm
  constructor
  · intro x
    obtain ⟨i, hi⟩ := A.covers x.val
    exact ⟨i, by simpa only [hbase, Set.mem_preimage] using hi⟩
  · constructor
    · intro i x hx
      have hi : x.val ∈ (A.chart i).baseSet := by simpa only [hbase, Set.mem_preimage] using hx
      simpa only [hcoords] using A.linear i x.val hi
    · intro i j a
      -- Smooth transition columns restrict by composition with the inherited open inclusion.
      have hs := (A.contMDiffOn_coordChange i j a).comp
        (contMDiff_subtype_val (U := U)).contMDiffOn (fun x hx ↦ hx)
      rw [hbase i, hbase j]
      apply hs.congr
      intro x hx
      rw [hcoords]
      change (A.chart j
        (let z := (A.restrictOpenChart U i).toPartialEquiv.symm (x, Pi.single a 1);
          (⟨z.proj.val, z.snd⟩ : TotalSpace Unit E))).2 = _
      rw [hinverse i x (by simpa only [hbase, Set.mem_preimage] using hx.1)]
      rfl

/-- Open restriction with exactly the original index set, ranks and coordinates. -/
def restrictOpen : SmoothComplexBundleAtlas (n := n) (M := U)
    (ComplexBundle.Restrict E U) where
  Index := A.Index
  rank := A.rank
  chart := A.restrictOpenChart U
  covers := (A.restrictOpenChart_properties U).1
  linear := (A.restrictOpenChart_properties U).2.1
  contMDiffOn_coordChange := (A.restrictOpenChart_properties U).2.2

/-- The same original smooth Hermitian form restricts smoothly with the specified atlas. -/
theorem isSmoothHermitianMetric_restrictOpen (h : ComplexBundle.ContinuousHermitianMetric E)
    (hh : A.IsSmoothHermitianMetric h) :
    (A.restrictOpen U).IsSmoothHermitianMetric
      (h.pullback ⟨(Subtype.val : U → M), continuous_subtype_val⟩) := by
  /- The selected restricted chart has the original forward fiber coordinates,
  hence its inverse frame vectors are the same original inverse frame vectors
  on the restricted domain. Each Gram entry is therefore the original Gram
  entry composed with the smooth open inclusion. Apply hh on that domain.
  The form and both vectors stay in E(x); no auxiliary metric is selected. -/
  classical
  have hbase (i : A.Index) : (A.restrictOpenChart U i).baseSet =
      Subtype.val ⁻¹' (A.chart i).baseSet := (A.exists_restrictOpenChart U i).choose_spec.1
  have hcoords (i : A.Index) (z : TotalSpace Unit (ComplexBundle.Restrict E U)) :
      (A.restrictOpenChart U i z).2 = (A.chart i ⟨z.proj.val, z.snd⟩).2 :=
    (A.exists_restrictOpenChart U i).choose_spec.2 z
  -- Equal original coordinate functions force the same inverse frame vectors.
  have hinverse (i : A.Index) (x : U)
      (hx : x ∈ ((A.restrictOpen U).chart i).baseSet)
      (hx' : x.val ∈ (A.chart i).baseSet) (v : Fin (A.rank i) → ℂ) :
      ((A.restrictOpen U).frameLinearEquiv i x hx).symm v =
        (A.frameLinearEquiv i x.val hx').symm v := by
    apply (A.frameLinearEquiv i x.val hx').injective
    rw [LinearEquiv.apply_symm_apply]
    change (A.chart i ⟨x.val, ((A.restrictOpen U).frameLinearEquiv i x hx).symm v⟩).2 = v
    rw [← hcoords i ⟨x, ((A.restrictOpen U).frameLinearEquiv i x hx).symm v⟩]
    exact ((A.restrictOpen U).frameLinearEquiv i x hx).apply_symm_apply v
  intro i a b
  have hs := (hh i a b).comp (contMDiff_subtype_val (U := U)).contMDiffOn (fun x hx ↦ hx)
  have hdomain : ((A.restrictOpen U).chart i).baseSet =
      (Subtype.val : U → M) ⁻¹' (A.chart i).baseSet := hbase i
  apply (hs.mono hdomain.subset).congr
  intro x hxR
  have hx : x.val ∈ (A.chart i).baseSet := hdomain.subset hxR
  -- The pulled-back form is evaluated on precisely these same two original vectors.
  dsimp only [ComplexBundle.ContinuousHermitianMetric.pullback, Function.comp_apply]
  simp only [dite_eq_left hx, dite_eq_left hxR]
  change (h.toCore x.val).inner
      (((A.restrictOpen U).frameLinearEquiv i x hxR).symm (Pi.single a 1))
      (((A.restrictOpen U).frameLinearEquiv i x hxR).symm (Pi.single b 1)) =
    (h.toCore x.val).inner
      ((A.frameLinearEquiv i x.val hx).symm (Pi.single a 1))
      ((A.frameLinearEquiv i x.val hx).symm (Pi.single b 1))
  exact congrArg₂ (h.toCore x.val).inner
    (hinverse i x hxR hx (Pi.single a 1)) (hinverse i x hxR hx (Pi.single b 1))

end AtiyahSinger.SmoothComplexBundleAtlas
