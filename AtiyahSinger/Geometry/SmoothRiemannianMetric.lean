/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.VectorBundle.FiniteDimensional

import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth metrics on the original finite-dimensional real vector bundle

Public module ID: M1409.

A finite-dimensional smooth real vector bundle over a Hausdorff paracompact
finite-dimensional boundaryless smooth manifold admits a smooth positive
metric. The output is mathlib's native `ContMDiffRiemannianMetric`, whose
bilinear forms use the original fiber topologies and whose smoothness uses
the specified original vector-bundle atlas. No new metric structure or bundle
carrier is introduced, and no global fiber norm is required as an input.

Sources: HU III.9.5, printed p.38, gives metric existence for paracompact vector
bundles. Its smooth partition-of-unity refinement is the standard supplement
used here. SG Appendix A, pp.370--373, supplies the smooth bundle and frame
context. The actual quotient normal bundle of HU XVIII.2.6, printed p.265,
is one downstream application, using its existing selected smooth atlas.

If a consumer installs the resulting native `RiemannianBundle`, mathlib gives
a norm compatible with the original fiber topology. This does not assert
that the new metric norm equals any independently supplied fiber norm. Empty
bases and zero-dimensional model fibers are included. Existence is proved using
locally finite supported positive forms on the original bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Function Topology
open scoped Manifold ContDiff

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [hBase : FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [hManifold : IsManifold 𝓘(ℝ, EB) ∞ B]
  [hHausdorff : T2Space B] [hParacompact : ParacompactSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [hFiber : FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [hSmooth : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]

include hBase hManifold hHausdorff hParacompact hFiber hSmooth

set_option maxSynthPendingDepth 30 in
set_option linter.unusedSectionVars false in
/-- A smooth finite-dimensional real vector bundle admits a metric on its original topology. -/
theorem nonempty_contMDiffRiemannianMetric :
    Nonempty (ContMDiffRiemannianMetric 𝓘(ℝ, EB) ∞ F V) := by
  /- Pull one positive model form through the original smooth bundle frames.
  A paracompact refinement gives compact closed pieces inside locally finite
  frame neighborhoods. Finite smooth-bump sums on those pieces supply
  nonnegative smooth weights, with a positive weight at every point.
  Their locally finite weighted form is smooth and strictly positive, without
  any countability assumption or normalization of the weights. Finally transfer
  the induced unit-ball bound from a temporary normed copy to each original fiber. -/
  classical
  let (x : B) : IsNormableSpace ℝ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  -- Choose a fixed positive form on the model without changing its prescribed norm.
  let R : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ F)) ℝ).symm
  let Q : F →L[ℝ] F →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp R.toContinuousLinearMap R.toContinuousLinearMap
  let e (x : B) := trivializationAt F V x
  let q (i x : B) : V x →L[ℝ] V x →L[ℝ] ℝ :=
    Q.bilinearComp ((e i).continuousLinearMapAt ℝ x) ((e i).continuousLinearMapAt ℝ x)
  -- Pull the same model form back through each original smooth local frame.
  have hq (i : B) : ContMDiffOn 𝓘(ℝ, EB)
      ((𝓘(ℝ, EB)).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (q i x)) (e i).baseSet := by
    let t := trivializationAt ℝ (Bundle.Trivial B ℝ) i
    let d := (e i).continuousLinearMap (RingHom.id ℝ) t
    let f := (e i).continuousLinearMap (RingHom.id ℝ) d
    apply (f.contMDiffOn_section_iff (e i).open_baseSet ?_).mpr
    · apply (contMDiffOn_const (c := Q)).congr
      intro x hx
      ext u v
      rw [show f = (e i).continuousLinearMap (RingHom.id ℝ) d from rfl,
        Trivialization.continuousLinearMap_apply]
      simp only [ContinuousLinearMap.comp_apply]
      rw [d.continuousLinearMapAt_apply_of_mem ℝ ⟨hx, by simp [t]⟩]
      change (t.continuousLinearMapAt ℝ x)
        (q i x ((e i).symmL ℝ x u) ((e i).symmL ℝ x v)) = Q u v
      simp only [q, ContinuousLinearMap.bilinearComp_apply,
        (e i).continuousLinearMapAt_symmL hx]
      simp [t]
    · intro x hx
      exact ⟨hx, hx, by simp [t]⟩
  have hq_symm (i x : B) (u v : V x) : q i x u v = q i x v u := by
    change inner ℝ (R ((e i).continuousLinearMapAt ℝ x u))
      (R ((e i).continuousLinearMapAt ℝ x v)) = _
    exact real_inner_comm _ _
  have hq_nonneg (i x : B) (v : V x) : 0 ≤ q i x v v := by
    change 0 ≤ inner ℝ (R ((e i).continuousLinearMapAt ℝ x v))
      (R ((e i).continuousLinearMapAt ℝ x v))
    exact real_inner_self_nonneg
  have hq_pos (i x : B) (hx : x ∈ (e i).baseSet) (v : V x) (hv : v ≠ 0) :
      0 < q i x v v := by
    change 0 < inner ℝ (R ((e i).continuousLinearMapAt ℝ x v))
      (R ((e i).continuousLinearMapAt ℝ x v))
    apply real_inner_self_pos.mpr
    intro hzero
    have hcoord : (e i).continuousLinearMapAt ℝ x v = 0 :=
      R.injective (by simpa using hzero)
    have hinv := (e i).symmL_continuousLinearMapAt (R := ℝ) hx v
    rw [hcoord, map_zero] at hinv
    exact hv hinv.symm
  -- Paracompactness gives locally finite frame supports; compact refinements can be smoothed.
  have hweights : ∃ φ : B → B → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ (φ i)) ∧
      (∀ i x, 0 ≤ φ i x) ∧ (∀ x, ∃ i, 0 < φ i x) ∧
      LocallyFinite (fun i ↦ tsupport (φ i)) ∧
      ∀ i, tsupport (φ i) ⊆ (e i).baseSet := by
    -- Start with compact smooth-bump supports contained in the fixed original frames.
    have hb (x : B) : ∃ b : SmoothBumpFunction 𝓘(ℝ, EB) x,
        tsupport b ⊆ (e x).baseSet :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, EB)) x).mem_iff.mp
        ((e x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x)) |>.imp
          (fun b hb ↦ hb.2)
    choose b hb using hb
    obtain ⟨U, hUo, hUc, hUf, hUb⟩ := precise_refinement
      (fun x ↦ support (b x)) (fun x ↦ (b x).isOpen_support)
      (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, (b x).c_mem_support⟩)
    -- A continuous bump cover supplies compact closed pieces covering the whole base.
    obtain ⟨ρ, hρ⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite
      isClosed_univ U hUo hUf hUc.ge
    let K (i : B) : Set B := {x | ρ i x = 1}
    have hKclosed (i : B) : IsClosed (K i) := isClosed_eq (ρ i).continuous continuous_const
    have hKU (i : B) : K i ⊆ U i := by
      intro x hx
      apply hρ i
      apply subset_closure
      change ρ i x ≠ 0
      change ρ i x = 1 at hx
      simp [hx]
    have hKc : (univ : Set B) ⊆ ⋃ i, K i := by
      intro x hx
      exact mem_iUnion.mpr ⟨ρ.ind x hx, (ρ.eventuallyEq_one x hx).eq_of_nhds⟩
    have hKcompact (i : B) : IsCompact (K i) :=
      (b i).hasCompactSupport.of_isClosed_subset (hKclosed i)
        ((hKU i).trans ((hUb i).trans subset_closure))
    -- Smooth finitely many small bumps on each compact piece; their supports stay in U i.
    have hφ (i : B) : ∃ φ : B → ℝ,
        ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ φ ∧ (∀ x, 0 ≤ φ x) ∧
        (∀ x ∈ K i, 0 < φ x) ∧ tsupport φ ⊆ U i := by
      have hb' (x : K i) : ∃ b' : SmoothBumpFunction 𝓘(ℝ, EB) (x : B),
          tsupport b' ⊆ U i :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, EB)) (x : B)).mem_iff.mp
          ((hUo i).mem_nhds (hKU i x.property)) |>.imp (fun b' hb' ↦ hb'.2)
      choose c hc using hb'
      obtain ⟨t, ht⟩ := (hKcompact i).elim_finite_subcover
        (fun x : K i ↦ support (c x)) (fun x ↦ (c x).isOpen_support)
        (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, (c ⟨x, hx⟩).c_mem_support⟩)
      refine ⟨fun x ↦ ∑ y ∈ t, c y x, ?_, ?_, ?_, ?_⟩
      · exact contMDiff_finsetSum fun y hy ↦ (c y).contMDiff
      · intro x
        exact Finset.sum_nonneg fun y hy ↦ (c y).nonneg
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
        exact Finset.sum_pos' (fun z hz ↦ (c z).nonneg)
          ⟨y, hy, lt_of_le_of_ne (c y).nonneg (Ne.symm hxy)⟩
      · apply subset_trans (b := ⋃ y ∈ t, tsupport (c y))
        · apply closure_minimal
          · intro x hx
            by_contra hn
            apply hx
            apply Finset.sum_eq_zero
            intro y hy
            apply image_eq_zero_of_notMem_tsupport
            exact fun hxy ↦ hn (mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
          · exact isClosed_biUnion_finset fun y hy ↦ isClosed_closure
        · exact iUnion₂_subset fun y hy ↦ hc y
    choose φ hφsmooth hφnonneg hφpos hφsupport using hφ
    refine ⟨φ, hφsmooth, hφnonneg, ?_, hUf.subset hφsupport, ?_⟩
    · intro x
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hKc (mem_univ x))
      exact ⟨i, hφpos i x hi⟩
    · intro i
      exact (hφsupport i).trans ((hUb i).trans (subset_closure.trans (hb i)))
  obtain ⟨φ, hφsmooth, hφnonneg, hφpos, hφfinite, hφsupport⟩ := hweights
  -- Each supported local form extends smoothly by zero; the locally finite sum is smooth.
  let s (x : B) : V x →L[ℝ] V x →L[ℝ] ℝ := ∑ᶠ i, φ i x • q i x
  have hterm (i : B) : ContMDiff 𝓘(ℝ, EB)
      ((𝓘(ℝ, EB)).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (φ i x • q i x)) :=
    ContMDiffOn.smul_section_of_tsupport (hφsmooth i).contMDiffOn
      (e i).open_baseSet (hφsupport i) (hq i)
  have hs : ContMDiff 𝓘(ℝ, EB)
      ((𝓘(ℝ, EB)).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x)) := by
    apply ContMDiff.finsum_section_of_locallyFinite ?_ hterm
    apply hφfinite.subset
    intro i x hx
    exact subset_closure (show φ i x ≠ 0 from fun hz ↦ hx (by simp [hz]))
  have hfinite (x : B) : (support (fun i ↦ φ i x)).Finite :=
    (hφfinite.point_finite x).subset (fun i hi ↦ subset_closure hi)
  have hs_eval (x : B) (u v : V x) : s x u v = ∑ᶠ i, φ i x * q i x u v := by
    change (∑ᶠ i, φ i x • q i x) u v = _
    rw [finsum_eq_sum_of_support_subset (s := (hfinite x).toFinset) _]
    · simp only [sum_apply, smul_apply, smul_eq_mul]
      symm
      apply finsum_eq_sum_of_support_subset
      intro i hi
      exact (hfinite x).mem_toFinset.mpr (left_ne_zero_of_mul hi)
    · intro i hi
      exact (hfinite x).mem_toFinset.mpr (left_ne_zero_of_smul hi)
  -- A pointwise finite sum preserves symmetry; one positive summand gives strict positivity.
  have hsymm (x : B) (u v : V x) : s x u v = s x v u := by
    simp_rw [hs_eval, hq_symm]
  have hpos (x : B) (v : V x) (hv : v ≠ 0) : 0 < s x v v := by
    rw [hs_eval, finsum_eq_sum_of_support_subset (s := (hfinite x).toFinset) _]
    · obtain ⟨i, hi⟩ := hφpos x
      apply Finset.sum_pos' (fun j hj ↦ mul_nonneg (hφnonneg j x) (hq_nonneg j x v))
      refine ⟨i, (hfinite x).mem_toFinset.mpr hi.ne', mul_pos hi ?_⟩
      exact hq_pos i x (hφsupport i (subset_closure hi.ne')) v hv
    · intro i hi
      exact (hfinite x).mem_toFinset.mpr (left_ne_zero_of_mul hi)
  refine ⟨{ inner := s
            symm := hsymm
            pos := hpos
            isVonNBounded := ?_
            contMDiff := hs }⟩
  intro x
  -- A temporary copy carries the form's norm; boundedness transfers to the original topology.
  let : FiniteDimensional ℝ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).symm.toLinearEquiv.finiteDimensional
  let core : InnerProductSpace.Core ℝ (ULift.{0} (V x)) :=
    { inner u v := s x u.down v.down
      conj_inner_symm u v := hsymm x v.down u.down
      re_inner_nonneg v := by
        by_cases hv : v.down = 0
        · simp [hv]
        · exact (hpos x v.down hv).le
      add_left u v w := by simp
      smul_left a u v := by simp
      definite v h := by
        have hv : v.down = 0 := by
          by_contra hv
          exact (ne_of_gt (hpos x v.down hv)) h
        exact ULift.ext hv }
  let : InnerProductSpace.Core ℝ (ULift.{0} (V x)) := core
  let t : TopologicalSpace (ULift.{0} (V x)) :=
    core.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedAddCommGroup (ULift.{0} (V x)) := core.toNormedAddCommGroup
  let : NormedSpace ℝ (ULift.{0} (V x)) := InnerProductSpace.Core.toNormedSpace
  let : InnerProductSpace ℝ (ULift.{0} (V x)) := InnerProductSpace.ofCore core.toCore
  let : FiniteDimensional ℝ (ULift.{0} (V x)) :=
    (ULift.moduleEquiv (R := ℝ) (M := V x)).symm.finiteDimensional
  let : T2Space (V x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).symm.toHomeomorph.t2Space
  let L : ULift.{0} (V x) ≃L[ℝ] V x :=
    (ULift.moduleEquiv (R := ℝ) (M := V x)).toContinuousLinearEquiv
  have hball : Bornology.IsVonNBounded ℝ (Metric.ball (0 : ULift.{0} (V x)) 1) :=
    (NormedSpace.isVonNBounded_iff ℝ).mpr Metric.isBounded_ball
  have himage := hball.image L.toContinuousLinearMap
  have hset : L '' Metric.ball (0 : ULift.{0} (V x)) 1 = {v : V x | s x v v < 1} := by
    ext v
    simp only [Set.mem_image, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hnorm : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
      change s x u.down u.down = ‖u‖ ^ 2 at hnorm
      change s x u.down u.down < 1
      nlinarith [norm_nonneg u]
    · intro hv
      refine ⟨ULift.up v, ?_, rfl⟩
      have hnorm : inner ℝ (ULift.up v) (ULift.up v) =
          ‖(ULift.up v : ULift.{0} (V x))‖ ^ 2 := real_inner_self_eq_norm_sq _
      change s x v v = ‖(ULift.up v : ULift.{0} (V x))‖ ^ 2 at hnorm
      nlinarith [norm_nonneg (ULift.up v : ULift.{0} (V x))]
  change Bornology.IsVonNBounded ℝ (L '' Metric.ball (0 : ULift.{0} (V x)) 1) at himage
  rwa [hset] at himage

/-- One smooth metric selected on the specified original real vector bundle. -/
def smoothRiemannianMetric : ContMDiffRiemannianMetric 𝓘(ℝ, EB) ∞ F V :=
  (nonempty_contMDiffRiemannianMetric F V).some

end AtiyahSinger
