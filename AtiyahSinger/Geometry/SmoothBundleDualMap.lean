/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth dual maps in the native real bundle atlases

The transpose of a smooth real bundle map is smooth in the original continuous
linear dual bundles. Its formula is composition with that same original map.
The proof evaluates each target dual coordinate on an original local frame,
then uses smooth bundle evaluation. No replacement dual bundle, source model,
metric or global trivialization is introduced.

This is the native inverse-dual calculation needed for the actual frame-sphere
cotangent pole chart. Applied to the smooth inverse of its vertical derivative,
it retains the original covectors and the specified radial normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composition with the actual smooth fiber map is smooth on the native dual bundles. -/
theorem contMDiff_dualMap_of_bundleMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners ℝ E HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold I ∞ B]
    {F : Type*} {G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : B → Type*} {W : B → Type*}
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace F V)] [TopologicalSpace (TotalSpace G W)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
    (Q : ∀ x, V x →L[ℝ] W x)
    (hQ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F V ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G W))) :
    ContMDiff (I.prod 𝓘(ℝ, G →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun z : TotalSpace (G →L[ℝ] ℝ) (fun x : B ↦ W x →L[ℝ] ℝ) ↦
        (⟨z.proj, z.snd.comp (Q z.proj)⟩ :
          TotalSpace (F →L[ℝ] ℝ) (fun x : B ↦ V x →L[ℝ] ℝ))) := by
  intro z
  let X := TotalSpace (G →L[ℝ] ℝ) (fun x : B ↦ W x →L[ℝ] ℝ)
  let A := I.prod 𝓘(ℝ, G →L[ℝ] ℝ)
  let t := trivializationAt F V z.proj
  have hx : z.proj ∈ t.baseSet := mem_baseSet_trivializationAt F V z.proj
  have hb : ContMDiffAt A I ∞ (fun w : X ↦ w.proj) z := Bundle.contMDiffAt_proj _
  -- Each coordinate of the dual image evaluates the original covector on a smooth Q-image.
  have heval (v : F) : ContMDiffAt A 𝓘(ℝ, ℝ) ∞
      (fun w : X ↦ w.snd (Q w.proj (t.symmL ℝ w.proj v))) z := by
    have hv : ContMDiffAt A (I.prod 𝓘(ℝ, F)) ∞
        (fun w : X ↦ (⟨w.proj, t.symmL ℝ w.proj v⟩ : TotalSpace F V)) z := by
      apply (t.contMDiffAt_iff (t.mem_source.mpr hx)).mpr
      refine ⟨hb, ?_⟩
      apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
      filter_upwards [hb.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hx)] with w hw
      rw [← t.continuousLinearMapAt_apply_of_mem ℝ hw]
      exact t.continuousLinearMapAt_symmL hw v
    have himage := hQ.contMDiffAt.comp z hv
    have hscalar : ContMDiffAt A (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun w : X ↦ (⟨w.proj, w.snd (Q w.proj (t.symmL ℝ w.proj v))⟩ :
          TotalSpace ℝ (fun _ : B ↦ ℝ))) z :=
      (contMDiffAt_id : ContMDiffAt A A ∞ (id : X → X) z).clm_bundle_apply himage
    exact (Bundle.contMDiffAt_totalSpace.mp hscalar).2
  -- Scalar evaluation detects the full finite-dimensional dual coordinate matrix.
  rw [contMDiffAt_hom_bundle]
  refine ⟨hb, ?_⟩
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hv := heval v
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
  have hscalar (x : B) :
      (trivializationAt ℝ (fun _ : B ↦ ℝ) z.proj).continuousLinearMapAt ℝ x =
        ContinuousLinearMap.id ℝ ℝ := by
    change (Bundle.Trivial.trivialization B ℝ).continuousLinearMapAt ℝ x = _
    exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
  simp only [ContinuousLinearMap.inCoordinates, hscalar,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply, Function.comp_apply]
  convert! hv using 1

end AtiyahSinger
