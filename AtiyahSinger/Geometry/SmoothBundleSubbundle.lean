/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.FiniteDimensional

import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness detected by a smooth subbundle inclusion

Public module ID: M1384.

A smooth fiberwise injection between finite-dimensional real vector bundles
has smooth local left inverses in the original atlases. A map into its source
bundle is therefore smooth when its composite with that injection is smooth.

Fix a linear left inverse at one base point and correct it by inversion of a
nearby square matrix. This is a local argument and needs no global metric,
compactness or paracompactness. Fiber and model universes remain independent.
The source keeps its supplied model with corners, including nested product models.

The criterion is used to recognize derivatives landing in the actual vertical
kernel bundle from smoothness in the ambient tangent bundle. It changes neither
the kernel fibers nor their previously selected native smooth atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A smooth bundle injection has a local smooth left inverse.
Private native-atlas adapter used to detect smoothness in the original subbundle. -/
private theorem exists_local_smooth_bundle_leftInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners ℝ E HB}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HB M]
  [IsManifold I ∞ M]
  {F : Type*} {G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V₀ : M → Type*} {W : M → Type*}
  [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
  [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
  [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ I]
  [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W I] (Q : ∀ x, W x
    →L[ℝ] V₀ x)
    (hQ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
    (hinjective : ∀ x, Injective (Q x)) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : ∀ y, V₀ y →L[ℝ] W y,
        ContMDiffOn I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
          (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U ∧
        ∀ y, y ∈ U → ∀ v, s y (Q y v) = v := by
  classical
  let a := trivializationAt F W x
  let b := trivializationAt G V₀ x
  let A (y : M) : F →L[ℝ] G :=
    (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
  let U := a.baseSet ∩ b.baseSet
  have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
  have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
  have hA : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] G) ∞ A U := by
    intro y hy
    have heval (v : F) : ContMDiffWithinAt I 𝓘(ℝ, G) ∞
        (fun z ↦ A z v) U y := by
      have hs : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞
          (fun z ↦ (⟨z, a.symmL ℝ z v⟩ : TotalSpace F W)) y := by
        apply a.contMDiffAt_iff (a.mem_source.mpr hy.1) |>.mpr
        refine ⟨contMDiffAt_id, ?_⟩
        apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
        filter_upwards [a.open_baseSet.mem_nhds hy.1] with z hz
        rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz]
        exact a.continuousLinearMapAt_symmL hz v
      have hq := hQ.contMDiffAt.comp y hs
      have hb := (b.contMDiffAt_iff (b.mem_source.mpr hy.2)).mp hq
      apply hb.2.contMDiffWithinAt.congr
      · intro z hz
        change (b.continuousLinearMapAt ℝ z) (Q z (a.symmL ℝ z v)) = _
        exact b.continuousLinearMapAt_apply_of_mem ℝ hz.2 _
      · exact b.continuousLinearMapAt_apply_of_mem ℝ hy.2 _
    rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    have hv := heval v
    rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
    exact hv
  -- A left inverse at the center persists after a smooth square-matrix correction.
  have hinj : Function.Injective (A x) := by
    intro u v huv
    have h := congrArg (b.symmL ℝ x) huv
    change b.symmL ℝ x (b.continuousLinearMapAt ℝ x (Q x (a.symmL ℝ x u))) =
      b.symmL ℝ x (b.continuousLinearMapAt ℝ x (Q x (a.symmL ℝ x v))) at h
    rw [b.symmL_continuousLinearMapAt (R := ℝ) hx.2,
      b.symmL_continuousLinearMapAt (R := ℝ) hx.2] at h
    have heq := congrArg (a.continuousLinearMapAt ℝ x) (hinjective x h)
    simpa only [a.continuousLinearMapAt_symmL hx.1] using heq
  obtain ⟨R₀, hR₀⟩ := (A x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let R : G →L[ℝ] F := R₀.toContinuousLinearMap
  let C (y : M) : F →L[ℝ] F := R.comp (A y)
  have hCx : C x = ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : F →ₗ[ℝ] F ↦ L v) hR₀
  have hC : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) ∞ C U :=
    contMDiffOn_const.clm_comp hA
  have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
  have hinv : (C x).IsInvertible := by
    rw [hCx]
    exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C y).IsInvertible :=
    Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
  obtain ⟨U', hsub, hU'o, hx'⟩ := mem_nhds_iff.mp hevent
  let P (y : M) : G →L[ℝ] F := (C y).inverse.comp R
  have hP : ContMDiffOn I 𝓘(ℝ, G →L[ℝ] F) ∞ P U' := by
    intro y hy
    have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
    have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
    exact (hInv.clm_comp contMDiffAt_const).contMDiffWithinAt
  -- Transport this corrected matrix back through the same two original trivializations.
  let s (y : M) : V₀ y →L[ℝ] W y :=
    (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
  let c := b.continuousLinearMap (RingHom.id ℝ) a
  have hs : ContMDiffOn I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U' := by
    apply (c.contMDiffOn_section_iff hU'o (fun y hy ↦ (hsub hy).1.symm)).mpr
    apply hP.congr
    intro y hy
    ext v
    rw [show c = b.continuousLinearMap (RingHom.id ℝ) a from rfl,
      Trivialization.continuousLinearMap_apply]
    change (a.continuousLinearMapAt ℝ y)
      (a.symmL ℝ y (P y (b.continuousLinearMapAt ℝ y (b.symmL ℝ y v)))) = P y v
    rw [b.continuousLinearMapAt_symmL (hsub hy).1.2,
      a.continuousLinearMapAt_symmL (hsub hy).1.1]
  have hleft (y : M) (hy : y ∈ U') (v : W y) : s y (Q y v) = v := by
    have hinj : Function.Injective (a.continuousLinearMapAt ℝ y) := by
      intro u v huv
      have heq := congrArg (a.symmL ℝ y) huv
      exact (a.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.1 u).symm.trans
        (heq.trans (a.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.1 v))
    apply hinj
    change a.continuousLinearMapAt ℝ y
      (a.symmL ℝ y ((C y).inverse (R (b.continuousLinearMapAt ℝ y (Q y v))))) =
        a.continuousLinearMapAt ℝ y v
    rw [a.continuousLinearMapAt_symmL (hsub hy).1.1]
    have hAvalue : A y (a.continuousLinearMapAt ℝ y v) =
        b.continuousLinearMapAt ℝ y (Q y v) := by
      change b.continuousLinearMapAt ℝ y
        (Q y (a.symmL ℝ y (a.continuousLinearMapAt ℝ y v))) = _
      rw [a.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.1]
    rw [← hAvalue]
    change (C y).inverse (C y (a.continuousLinearMapAt ℝ y v)) = _
    obtain ⟨e, he⟩ := (hsub hy).2
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.symm_apply_apply _
  exact ⟨U', hU'o, hx', s, hs, hleft⟩

/-- Smoothness is detected after the same fiberwise injective smooth bundle map. -/
theorem contMDiff_bundleMap_of_comp_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners ℝ E HB}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HB M]
  [IsManifold I ∞ M]
  {F : Type*} {G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V₀ : M → Type*} {W : M → Type*}
  [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
  [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
  [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ I]
  [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W I]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Z : M → Type*} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
    [∀ x, TopologicalSpace (Z x)] [∀ x, IsTopologicalAddGroup (Z x)]
    [∀ x, ContinuousSMul ℝ (Z x)] [TopologicalSpace (TotalSpace H Z)]
    [FiberBundle H Z] [VectorBundle ℝ H Z] [ContMDiffVectorBundle ∞ H Z I]
    (Q : ∀ x, W x →L[ℝ] V₀ x) (D : ∀ x, Z x →L[ℝ] W x)
    (hQ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
    (hinjective : ∀ x, Injective (Q x))
    (hQD : ContMDiff (I.prod 𝓘(ℝ, H)) (I.prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace H Z ↦ (⟨z.proj, Q z.proj (D z.proj z.snd)⟩ : TotalSpace G V₀))) :
    ContMDiff (I.prod 𝓘(ℝ, H)) (I.prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace H Z ↦ (⟨z.proj, D z.proj z.snd⟩ : TotalSpace F W)) := by
  intro z
  obtain ⟨U, hU, hz, s, hs, hleft⟩ :=
    exists_local_smooth_bundle_leftInverse Q hQ hinjective z.proj
  have hsAt := (hs z.proj hz).contMDiffAt (hU.mem_nhds hz)
  have htotal : ContMDiffAt (I.prod 𝓘(ℝ, H)) (I.prod 𝓘(ℝ, F)) ∞
      (fun w : TotalSpace H Z ↦
        (⟨w.proj, s w.proj (Q w.proj (D w.proj w.snd))⟩ : TotalSpace F W)) z :=
    (hsAt.comp z (Bundle.contMDiffAt_proj Z)).clm_bundle_apply hQD.contMDiffAt
  apply htotal.congr_of_eventuallyEq
  filter_upwards [((FiberBundle.continuous_proj H Z).continuousAt).preimage_mem_nhds
    (hU.mem_nhds hz)] with w hw
  change (⟨w.proj, D w.proj w.snd⟩ : TotalSpace F W) =
    ⟨w.proj, s w.proj (Q w.proj (D w.proj w.snd))⟩
  rw [hleft w.proj hw]

end AtiyahSinger
