/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereDeRhamLocalization

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local Poincaré exactness for forms closed near a point

Public module ID: M1297.

In a chart with full Euclidean target on a Hausdorff smooth manifold, a
smooth cutoff contracts the entire coordinate space into a ball where the
given form is closed, while fixing a neighborhood of the selected point.
The resulting global pullback is closed and the Euclidean Poincaré argument
applies. A second cutoff makes its primitive global on the original manifold,
without changing the local equality. Only local closedness is required.

Source: the local Poincaré lemma and smooth cutoff globalization,
Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Metric Set
open scoped ContDiff Manifold Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

set_option maxHeartbeats 2000000 in
-- Local closedness is transported through two actual smooth cutoff maps and their derivatives.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A positive-degree form closed near a point in a full chart
has a global smooth local primitive. -/
theorem exists_smoothFormPrimitive_near_of_eventually_closed (p : ℕ)
    (form : SmoothDifferentialForm (n := n) M (p + 1))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (htarget : c.target = univ)
    (x : M) (hx : x ∈ c.source)
    (hclosed : ∀ᶠ y in 𝓝 x,
      (smoothFormExteriorDerivative (n := n) (p + 1) form).val y = 0) :
    ∃ primitive : SmoothDifferentialForm (n := n) M p,
      ∀ᶠ y in 𝓝 x, (smoothFormExteriorDerivative (n := n) p primitive).val y = form.val y := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  let z₀ : V := c x
  have hcx : z₀ ∈ c.target := c.map_source hx
  have hzero : ∀ᶠ z in 𝓝 z₀,
      (smoothFormExteriorDerivative (n := n) (p + 1) form).val (c.symm z) = 0 := by
    have h := hclosed
    rw [← c.left_inv hx] at h
    exact (c.continuousAt_symm hcx).preimage_mem_nhds h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hzero
  let b : ContDiffBump z₀ := ⟨r / 2, r, by linarith, by linarith⟩
  let F (z : V) : V := z₀ + b z • (z - z₀)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.add (b.contDiff.smul (contDiff_id.sub contDiff_const))
  have hFball (z : V) : F z ∈ ball z₀ r := by
    change dist (z₀ + b z • (z - z₀)) z₀ < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    by_cases hz : b z = 0
    · rw [hz, zero_mul]
      exact hr
    · have hzr : ‖z - z₀‖ < r := by
        have hzb : z ∈ ball z₀ b.rOut := b.support_eq ▸ hz
        exact mem_ball_iff_norm.mp hzb
      exact (mul_le_of_le_one_left (norm_nonneg _) b.le_one).trans_lt hzr
  have hFid : F =ᶠ[𝓝 z₀] id := by
    filter_upwards [b.eventuallyEq_one] with z hz
    change z₀ + b z • (z - z₀) = z
    rw [show b z = (1 : ℝ) from hz, one_smul]
    abel
  have hcinv : ContMDiff I I ∞ c.symm := by
    intro z
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
      (htarget.symm ▸ mem_univ z)
  let g : V → M := c.symm ∘ F
  have hg : ContMDiff I I ∞ g := hcinv.comp hF.contMDiff
  let α := smoothFormPullback g hg (p + 1) form
  have hαclosed : smoothFormExteriorDerivative (n := n) (p + 1) α = 0 := by
    have h := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback g hg (p + 1)) form
    apply Subtype.ext
    funext z
    have hv := congrArg (fun a : SmoothDifferentialForm (n := n) V (p + 1 + 1) ↦ a.val z) h
    change (smoothFormExteriorDerivative (n := n) (p + 1) α).val z = _ at hv
    rw [hv, LinearMap.comp_apply, smoothFormPullback_apply]
    have hz : (smoothFormExteriorDerivative (n := n) (p + 1) form).val (g z) = 0 :=
      hball (hFball z)
    rw [hz]
    ext v
    rfl
  -- The globally closed pullback has a primitive near the same original coordinate point.
  obtain ⟨primitiveV, hprimitiveV⟩ := exists_smoothFormPrimitive_near_of_chart_target_univ p α
    hαclosed (OpenPartialHomeomorph.refl V) (chartedSpaceSelf_atlas.mpr rfl) rfl z₀ (mem_univ z₀)
  obtain ⟨a, _, ha⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (c.open_source.mem_nhds hx)
  let f (y : M) : V := a y • c y
  have hf : ContMDiff I I ∞ f := by
    intro y
    by_cases hy : y ∈ tsupport a
    · exact a.contMDiff.contMDiffAt.smul
        (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) (ha hy))
    · apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with z hz
      change a z • c z = 0
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have hfc : f =ᶠ[𝓝 x] c := by
    filter_upwards [a.eventuallyEq_one] with y hy
    change a y • c y = c y
    rw [show a y = (1 : ℝ) from hy, one_smul]
  have hcomp : g ∘ f =ᶠ[𝓝 x] id := by
    filter_upwards [hfc, (c.continuousAt hx).preimage_mem_nhds hFid,
      c.open_source.mem_nhds hx] with y hy hFy hyc
    change c.symm (F (f y)) = y
    rw [hy, show F (c y) = c y from hFy, c.left_inv hyc]
  let primitive := smoothFormPullback f hf p primitiveV
  refine ⟨primitive, ?_⟩
  have hfx : f x = z₀ := hfc.self_of_nhds
  have hnearV : ∀ᶠ y in 𝓝 x,
      (smoothFormExteriorDerivative (n := n) p primitiveV).val (f y) = α.val (f y) := by
    have h := hprimitiveV
    rw [← hfx] at h
    exact hf.continuous.continuousAt.preimage_mem_nhds h
  have hd := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback f hf p) primitiveV
  filter_upwards [hnearV, eventually_eventuallyEq_nhds.mpr hcomp] with y hy hgy
  have hvalue : g (f y) = y := hgy.self_of_nhds
  have hcancel : (mfderiv I I g (f y)).comp (mfderiv I I f y) = ContinuousLinearMap.id ℝ V := by
    have hc := mfderiv_comp y (hg.mdifferentiable (by simp) (f y))
      (hf.mdifferentiable (by simp) y)
    have hid := hgy.mfderiv_eq (I := I) (I' := I)
    rw [mfderiv_id] at hid
    exact hc.symm.trans hid
  have hv := congrArg (fun a : SmoothDifferentialForm (n := n) M (p + 1) ↦ a.val y) hd
  change (smoothFormExteriorDerivative (n := n) p primitive).val y = _ at hv
  rw [hv, LinearMap.comp_apply, smoothFormPullback_apply, hy]
  change (α.val (f y)).compContinuousLinearMap (mfderiv I I f y) = form.val y
  rw [show α.val (f y) = (form.val (g (f y))).compContinuousLinearMap
    (mfderiv I I g (f y)) from smoothFormPullback_apply g hg (p + 1) form (f y)]
  ext v
  change form.val (g (f y))
    (fun i ↦ mfderiv I I g (f y) (mfderiv I I f y (v i))) = form.val y v
  rw [hvalue]
  apply congrArg (form.val y)
  funext i
  exact congrArg (fun L ↦ L (v i)) hcancel

end AtiyahSinger
