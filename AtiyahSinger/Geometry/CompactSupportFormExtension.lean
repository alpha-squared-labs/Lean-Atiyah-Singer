/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DeRhamComplex

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Extension of compactly supported forms through a full chart

Public module ID: M1132.

A smooth compactly supported Euclidean form extends by zero through a full
manifold chart. Its original chart coefficients are unchanged, and its
exterior derivative vanishes outside that chart. Compactness of the same
transported support provides the neighborhood on which the extension is zero.

Source: the standard extension-by-zero construction for compactly supported
differential forms, as in Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set
open scoped ContDiff Manifold Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

set_option maxHeartbeats 2000000 in
-- Both chart covariance and the zero neighborhood use the actual dependent tangent instances.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A compactly supported Euclidean form extends smoothly by zero through a full atlas chart,
with the same coefficients and with exterior derivative zero outside that chart. -/
theorem exists_smoothFormExtension_of_compactSupport (p : ℕ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (htarget : c.target = univ)
    (η : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ)
    (hη : ContDiff ℝ ∞ η) (hcompact : HasCompactSupport η) :
    ∃ extension : SmoothDifferentialForm (n := n) M p,
      differentialFormInChart extension.val c = η ∧
      (∀ x, x ∉ c.source → ∀ᶠ y in 𝓝 x, extension.val y = 0) ∧
      ∀ x, x ∉ c.source →
        (smoothFormExteriorDerivative (n := n) p extension).val x = 0 := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  let β (x : M) : DifferentialFormFiber (n := n) p x :=
    if x ∈ c.source then (η (c x)).compContinuousLinearMap (mfderiv I I c x) else 0
  let K : Set M := c.symm '' tsupport η
  have hcsmooth : ContMDiff I I ∞ c.symm := by
    intro y
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
      (htarget.symm ▸ mem_univ y)
  have hK : IsCompact K := hcompact.image hcsmooth.continuous
  have hKsource : K ⊆ c.source := by
    rintro x ⟨y, _, rfl⟩
    exact c.map_target (htarget.symm ▸ mem_univ y)
  have hβoff (x : M) (hx : x ∉ K) : β x = 0 := by
    dsimp only [β]
    split_ifs with hxc
    · have hzero : η (c x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hx ⟨c x, h, c.left_inv hxc⟩
      rw [hzero]
      ext v
      rfl
    · rfl
  have hβnear (x : M) (hx : x ∉ K) : ∀ᶠ y in 𝓝 x, β y = 0 := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hβoff y hy
  -- Inside the chart, coordinate changes give the same ordinary pullback formula.
  have hsmooth : IsSmoothDifferentialForm (n := n) β := by
    intro a ha y hy
    by_cases hcy : a.symm y ∈ c.source
    · let g : V → V := c ∘ a.symm
      have hg : ContDiffAt ℝ ∞ g y := by
        apply contMDiffAt_iff_contDiffAt.mp
        exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hcy).comp y
          (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ha) hy)
      have hnear : differentialFormInChart β a =ᶠ[𝓝 y]
          (fun z ↦ (η (g z)).compContinuousLinearMap (fderiv ℝ g z)) := by
        filter_upwards [a.open_target.mem_nhds hy,
          (a.continuousAt_symm hy).preimage_mem_nhds (c.open_source.mem_nhds hcy)]
          with z hza hzc
        have hdf : fderiv ℝ g z =
            (mfderiv I I c (a.symm z)).comp (mfderiv I I a.symm z) := by
          have h := mfderiv_comp z
            ((mdifferentiable_of_mem_atlas (I := I) hc).mdifferentiableAt hzc)
            ((mdifferentiable_of_mem_atlas (I := I) ha).mdifferentiableAt_symm hza)
          rw [mfderiv_eq_fderiv] at h
          exact h
        change (β (a.symm z)).compContinuousLinearMap _ = _
        dsimp only [β]
        rw [ite_eq_left (show a.symm z ∈ c.source from hzc), hdf]
        ext v
        rfl
      have hop : ContDiffAt ℝ ∞
          (ContinuousAlternatingMap.compContinuousLinearMapCLM :
            (V →L[ℝ] V) → (V [⋀^Fin p]→L[ℝ] ℂ) →L[ℝ] V [⋀^Fin p]→L[ℝ] ℂ)
          (fderiv ℝ g y) :=
        (ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM _).contDiffAt
      have hlocal := (hop.comp y (hg.fderiv_right (m := ∞) (by simp))).clm_apply
        (hη.contDiffAt.comp y hg)
      exact (hlocal.congr_of_eventuallyEq hnear).contDiffWithinAt
    · -- Outside the chart, the same compact support leaves an open zero neighborhood.
      have hyK : a.symm y ∉ K := fun h ↦ hcy (hKsource h)
      have hnear : differentialFormInChart β a =ᶠ[𝓝 y] (fun _ ↦ 0) := by
        filter_upwards [(a.continuousAt_symm hy).preimage_mem_nhds (hβnear _ hyK)] with z hz
        change (β (a.symm z)).compContinuousLinearMap _ = 0
        rw [hz]
        ext v
        rfl
      exact (contDiffAt_const.congr_of_eventuallyEq hnear).contDiffWithinAt
  let extension : SmoothDifferentialForm (n := n) M p := ⟨β, hsmooth⟩
  refine ⟨extension, ?_, ?_, ?_⟩
  · -- The two actual chart derivatives cancel; the coefficient function is unchanged.
    funext y
    have hy : y ∈ c.target := htarget.symm ▸ mem_univ y
    change (β (c.symm y)).compContinuousLinearMap _ = η y
    dsimp only [β]
    rw [ite_eq_left (c.map_target hy), c.right_inv hy]
    ext v
    apply congrArg (η y)
    funext i
    exact congrArg (fun L ↦ L (v i))
      ((mdifferentiable_of_mem_atlas (I := I) hc).comp_symm_deriv hy)
  · intro x hx
    exact hβnear x (fun h ↦ hx (hKsource h))
  · -- Local vanishing also kills the selected original coordinate exterior derivative.
    intro x hx
    let a := chartAt V x
    have hxa : x ∈ a.source := mem_chart_source V x
    have hya : a x ∈ a.target := a.map_source hxa
    have hnear : differentialFormInChart extension.val a =ᶠ[𝓝 (a x)] (fun _ ↦ 0) := by
      have hz : ∀ᶠ z in 𝓝 (a.symm (a x)), β z = 0 := by
        rw [a.left_inv hxa]
        exact hβnear x (fun h ↦ hx (hKsource h))
      filter_upwards [(a.continuousAt_symm hya).preimage_mem_nhds hz] with z hz
      change (β (a.symm z)).compContinuousLinearMap _ = 0
      rw [hz]
      ext v
      rfl
    have hext : extDeriv (differentialFormInChart extension.val a) (a x) = 0 := by
      rw [hnear.extDeriv_eq]
      simp only [extDeriv, fderiv_const_apply]
      exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ).map_zero
    have hspec : (smoothFormExteriorDerivative (n := n) p extension).val x =
        differentialFormExteriorDerivative extension.val x :=
      (existsUnique_smoothFormExteriorDerivative (n := n) (M := M) p).exists.choose_spec
        extension x
    rw [hspec]
    change (extDeriv (differentialFormInChart extension.val a) (a x)).compContinuousLinearMap
      (mfderiv I I a x) = 0
    rw [hext]
    ext v
    rfl

end AtiyahSinger
