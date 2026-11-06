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
# Smooth descent through a surjective bundle map

Public module ID: M1383.

A smooth surjective map of finite-dimensional real vector bundles has smooth
local right inverses in its original atlases. Consequently, a fiberwise linear
map is smooth whenever its composite with that surjection is smooth. This also
proves smoothness of the inverse of a fiberwise smooth linear equivalence.

The local construction fixes a right inverse at one point and corrects it by
inverting a nearby matrix. The same original frames transport the correction
back to the original bundles. No global splitting or paracompactness is needed.
The fiber types and their finite-dimensional models may have different universes.

This standard local splitting argument supplements the normal-bundle descent
and transverse-normal comparisons; it is not a new normal or quotient model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A surjective smooth real bundle map has a local smooth right inverse.
Private native-atlas adapter used by quotient descent with different fiber universes. -/
private theorem exists_local_smooth_bundle_rightInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} {G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V₀ : M → Type*} {W : M → Type*}
  [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
  [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
  [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
  [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)] (Q : ∀ x, W x
    →L[ℝ] V₀ x)
    (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
    (hsurjective : ∀ x, Surjective (Q x)) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : ∀ y, V₀ y →L[ℝ] W y,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
          (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U ∧
        ∀ y, y ∈ U → ∀ v, Q y (s y v) = v := by
  classical
  let a := trivializationAt F W x
  let b := trivializationAt G V₀ x
  let A (y : M) : F →L[ℝ] G :=
    (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
  let U := a.baseSet ∩ b.baseSet
  have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
  have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
  have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] G) ∞ A U := by
    intro y hy
    have heval (v : F) : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
        (fun z ↦ A z v) U y := by
      have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
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
  -- Choose one right inverse at the center; nearby invertible corrections vary smoothly.
  have hsurj : Function.Surjective (A x) := by
    intro v
    obtain ⟨w, hw⟩ := hsurjective x (b.symmL ℝ x v)
    refine ⟨a.continuousLinearMapAt ℝ x w, ?_⟩
    change (b.continuousLinearMapAt ℝ x) (Q x (a.symmL ℝ x
      (a.continuousLinearMapAt ℝ x w))) = v
    erw [a.symmL_continuousLinearMapAt (R := ℝ) hx.1]
    rw [hw, b.continuousLinearMapAt_symmL hx.2]
  obtain ⟨R₀, hR₀⟩ := (A x).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let R : G →L[ℝ] F := R₀.toContinuousLinearMap
  let C (y : M) : G →L[ℝ] G := (A y).comp R
  have hCx : C x = ContinuousLinearMap.id ℝ G := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : G →ₗ[ℝ] G ↦ L v) hR₀
  have hC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞ C U :=
    hA.clm_comp contMDiffOn_const
  have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
  have hinv : (C x).IsInvertible := by
    rw [hCx]
    exact ⟨ContinuousLinearEquiv.refl ℝ G, rfl⟩
  have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C y).IsInvertible :=
    Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
  obtain ⟨U', hsub, hU'o, hx'⟩ := mem_nhds_iff.mp hevent
  let P (y : M) : G →L[ℝ] F := R.comp (C y).inverse
  have hP : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] F) ∞ P U' := by
    intro y hy
    have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
    have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
    exact (contMDiffAt_const.clm_comp hInv).contMDiffWithinAt
  -- Transport this corrected matrix back through the same two original trivializations.
  let s (y : M) : V₀ y →L[ℝ] W y :=
    (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
  let c := b.continuousLinearMap (RingHom.id ℝ) a
  have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
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
  have hright (y : M) (hy : y ∈ U') (v : V₀ y) : Q y (s y v) = v := by
    have hinj : Function.Injective (b.continuousLinearMapAt ℝ y) := by
      intro u v huv
      have heq := congrArg (b.symmL ℝ y) huv
      exact (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 u).symm.trans
        (heq.trans (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 v))
    apply hinj
    change (A y) (R ((C y).inverse (b.continuousLinearMapAt ℝ y v))) =
      b.continuousLinearMapAt ℝ y v
    change (C y) ((C y).inverse (b.continuousLinearMapAt ℝ y v)) =
      b.continuousLinearMapAt ℝ y v
    obtain ⟨e, he⟩ := (hsub hy).2
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.apply_symm_apply _
  exact ⟨U', hU'o, hx', s, hs, hright⟩

/-- Smoothness descends through the same fiberwise surjective smooth bundle map. -/
theorem contMDiff_bundleMap_of_comp_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} {G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V₀ : M → Type*} {W : M → Type*}
  [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
  [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
  [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
  [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Z : M → Type*} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
    [∀ x, TopologicalSpace (Z x)] [∀ x, IsTopologicalAddGroup (Z x)]
    [∀ x, ContinuousSMul ℝ (Z x)] [TopologicalSpace (TotalSpace H Z)]
    [FiberBundle H Z] [VectorBundle ℝ H Z] [ContMDiffVectorBundle ∞ H Z 𝓘(ℝ, E)]
    (Q : ∀ x, W x →L[ℝ] V₀ x) (D : ∀ x, V₀ x →L[ℝ] Z x)
    (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
    (hsurjective : ∀ x, Surjective (Q x))
    (hDQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
      (fun z : TotalSpace F W ↦ (⟨z.proj, D z.proj (Q z.proj z.snd)⟩ : TotalSpace H Z))) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
      (fun z : TotalSpace G V₀ ↦ (⟨z.proj, D z.proj z.snd⟩ : TotalSpace H Z)) := by
  intro z
  obtain ⟨U, hU, hz, s, hs, hright⟩ :=
    exists_local_smooth_bundle_rightInverse Q hQ hsurjective z.proj
  have hsAt := (hs z.proj hz).contMDiffAt (hU.mem_nhds hz)
  have htotal : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
      (fun w : TotalSpace G V₀ ↦ (⟨w.proj, s w.proj w.snd⟩ : TotalSpace F W)) z := by
    exact (hsAt.comp z (Bundle.contMDiffAt_proj V₀)).clm_bundle_apply contMDiffAt_id
  apply (hDQ.contMDiffAt.comp z htotal).congr_of_eventuallyEq
  filter_upwards [((FiberBundle.continuous_proj G V₀).continuousAt).preimage_mem_nhds
    (hU.mem_nhds hz)] with w hw
  change (⟨w.proj, D w.proj w.snd⟩ : TotalSpace H Z) =
    ⟨w.proj, D w.proj (Q w.proj (s w.proj w.snd))⟩
  rw [hright w.proj hw]

end AtiyahSinger
