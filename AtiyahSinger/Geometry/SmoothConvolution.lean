/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactJetIntegral
public import AtiyahSinger.Analysis.SmoothCompositionFamilies
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.MeasureTheory.Group.Integral

import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Smooth convolution with a continuous weight

Public module ID: M1388.

A compactly supported smooth real kernel on a finite-dimensional real Lie group
regularizes a continuous Banach-valued weight by integrating its left translates.
The measure need only be finite on compact sets; Haar invariance is not used here.
A fixed compact parameter set works near each base point, and only the kernel's
spatial derivatives enter the integral. The original weight remains merely continuous.

This is the standard local convolution argument used to prove automatic smoothness
of finite-dimensional continuous representations. It needs neither compactness of
the group nor a global countable atlas. The compact-parameter integration theorem
supplies the analytic derivative interchange after all joint jet bounds are established.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Filter Set Topology Manifold
open scoped ContDiff Pointwise

universe u v
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hDim : FiniteDimensional ℝ V]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace V G] [hLie : LieGroup 𝓘(ℝ, V) ∞ G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

include hDim hLie

set_option maxHeartbeats 800000 in
-- The local chart calculation tracks the compact parameter and all spatial jets.
/-- A compactly supported smooth translated kernel regularizes any continuous weight. -/
theorem contMDiff_integral_mul_smul_of_hasCompactSupport
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : G → ℝ) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ) ∞ f) (hsupp : HasCompactSupport f)
    (a : G → F) (ha : Continuous a) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ (fun x ↦ ∫ g, f (x * g) • a g ∂μ) := by
  classical
  intro x₀
  -- A compact neighborhood of the variable captures all translated kernel supports.
  obtain ⟨χ⟩ : Nonempty (SmoothBumpFunction 𝓘(ℝ, V) x₀) := inferInstance
  let C := tsupport χ
  let K := C⁻¹ * tsupport f
  have hC : IsCompact C := χ.hasCompactSupport
  have hK : IsCompact K := hC.inv.mul hsupp
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : Measure K := μ.comap Subtype.val
  let : IsFiniteMeasureOnCompacts ν :=
    IsFiniteMeasureOnCompacts.comap' μ continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hK.measurableSet)
  let : IsFiniteMeasure ν := inferInstance
  let c := chartAt V x₀
  let s := c.target ∩ c.symm ⁻¹' interior C
  have hs : IsOpen s :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target isOpen_interior
  have hx₀ : c x₀ ∈ s := by
    refine ⟨mem_chart_target V x₀, ?_⟩
    change c.symm (c x₀) ∈ interior C
    rw [c.left_inv (mem_chart_source V x₀)]
    exact mem_interior_iff_mem_nhds.mpr χ.tsupport_mem_nhds
  let b : G × V → ℝ := fun p ↦ f (c.symm p.2 * p.1)
  have hb : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, V)) 𝓘(ℝ) ∞ b (univ ×ˢ c.target) := by
    apply hf.comp_contMDiffOn
    apply ContMDiffOn.mul
    · exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, V)) (x := x₀)).comp
        contMDiff_snd.contMDiffOn (fun p hp ↦ hp.2)
    · exact contMDiff_fst.contMDiffOn
  -- Lift only the scalar codomain to reuse the existing universe-homogeneous jet theorem.
  let L : ULift.{u} ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.ulift
  have hblift : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, V)) 𝓘(ℝ, ULift.{u} ℝ) ∞
      (fun p ↦ L.symm (b p)) (univ ×ˢ c.target) :=
    L.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hb
  have hjb (k : ℕ) : ContinuousOn
      (fun p : G × V ↦ iteratedFDeriv ℝ k (fun y ↦ b (p.1, y)) p.2)
      (univ ×ˢ c.target) := by
    have hj := (contMDiffOn_iteratedFDeriv_parameter 𝓘(ℝ, V)
      (isOpen_univ.prod c.open_target) hblift k).continuousOn
    let D := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin k ↦ V) (ULift.{u} ℝ) ℝ L.toContinuousLinearMap
    apply (D.continuous.comp_continuousOn hj).congr
    intro p hp
    have heq := L.iteratedFDeriv_comp_left
      (f := fun y ↦ L.symm (b (p.1, y))) (x := p.2) (i := k)
    simpa only [Function.comp_def, L.apply_symm_apply, D,
      ContinuousLinearMap.compContinuousMultilinearMapL_apply] using heq
  have hslice (g : G) : ContDiffOn ℝ ∞ (fun y ↦ b (g, y)) c.target := by
    apply ContMDiffOn.contDiffOn
    exact hb.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun y hy ↦ ⟨mem_univ g, hy⟩)
  -- The continuous weight is constant in the differentiated variable.
  let d (g : K) (y : V) : F := b (g.val, y) • a g.val
  have hd (g : K) : ContDiffOn ℝ ∞ (d g) c.target := (hslice g.val).smul contDiffOn_const
  have hjd (k : ℕ) : ContinuousOn
      (fun p : K × V ↦ iteratedFDeriv ℝ k (d p.1) p.2) (univ ×ˢ c.target) := by
    have hj : ContinuousOn (fun p : K × V ↦
        iteratedFDeriv ℝ k (fun y ↦ b (p.1.val, y)) p.2) (univ ×ˢ c.target) := (hjb k).comp
      (continuous_subtype_val.prodMap continuous_id).continuousOn
      (fun p hp ↦ ⟨mem_univ p.1.val, hp.2⟩)
    let S := ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin k ↦ V) F
    have hc := (S.continuous.comp_continuousOn hj).clm_apply
      ((ha.comp (continuous_subtype_val.comp continuous_fst)).continuousOn)
    apply hc.congr
    intro p hp
    have hsmul := iteratedFDeriv_smul_const_apply (v := a p.1.val)
      (((hslice p.1.val) p.2 hp.2).contDiffAt
        (c.open_target.mem_nhds hp.2) |>.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    simp only [Function.comp_def, d, S, ContinuousMultilinearMap.smulRightL_apply]
    rw [hsmul]
    ext w
    rfl
  have hi := contDiffOn_integral_of_continuous_jets ν c.open_target hd hjd
  -- Outside this compact parameter set the original integrand vanishes identically.
  have heq (y : V) (hy : y ∈ s) :
      (∫ g : K, d g y ∂ν) = ∫ g : G, f (c.symm y * g) • a g ∂μ := by
    change (∫ g : K, f (c.symm y * g.val) • a g.val ∂(μ.comap Subtype.val)) = _
    calc
      _ = ∫ g in K, f (c.symm y * g) • a g ∂μ :=
        integral_subtype_comap hK.measurableSet (fun g : G ↦ f (c.symm y * g) • a g)
      _ = _ := ?_
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro g hg
    have hzero : f (c.symm y * g) = 0 := by
      by_contra hn
      have hc : c.symm y ∈ C := interior_subset hy.2
      have hfmem : c.symm y * g ∈ tsupport f := subset_tsupport f (by exact hn)
      apply hg
      exact ⟨(c.symm y)⁻¹, by simpa using hc, c.symm y * g, hfmem, by simp⟩
    change f (c.symm y * g) • a g = 0
    rw [hzero, zero_smul]
  -- Return from the local integral in coordinates to the original manifold integral.
  have hiAt : ContDiffAt ℝ ∞ (fun y ↦ ∫ g : K, d g y ∂ν) (c x₀) :=
    (hi _ hx₀.1).contDiffAt (c.open_target.mem_nhds hx₀.1)
  have hchart : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ c x₀ :=
    (contMDiffOn_chart (I := 𝓘(ℝ, V)) (x := x₀) x₀
      (mem_chart_source V x₀)).contMDiffAt (c.open_source.mem_nhds (mem_chart_source V x₀))
  apply (hiAt.contMDiffAt.comp x₀ hchart).congr_of_eventuallyEq
  have hcs : ∀ᶠ x in 𝓝 x₀, c x ∈ s := hchart.continuousAt.preimage_mem_nhds (hs.mem_nhds hx₀)
  filter_upwards [hcs, c.open_source.mem_nhds (mem_chart_source V x₀)] with x hxs hxc
  change (∫ g : G, f (x * g) • a g ∂μ) = ∫ g : K, d g (c x) ∂ν
  rw [heq _ hxs, c.left_inv hxc]

end AtiyahSinger
