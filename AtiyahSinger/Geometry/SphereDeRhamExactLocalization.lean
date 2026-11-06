/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.LocalPoincareLemma
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Compact-support primitives of localized exact sphere forms

Public module ID: M1426.

An original global primitive is closed near the omitted point. In positive
degree, local Poincaré exactness removes it there without changing its
derivative. In degree zero, a constant adjustment does the same. The native
punctured-sphere chart then gives a compactly supported Euclidean primitive.
This is the injectivity step for the actual compact-support/sphere quotient.

Source: the de Rham localization argument, Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Metric Set ContinuousAlternatingMap
open scoped ContDiff Manifold Topology

set_option maxHeartbeats 2000000 in
-- The exact primitive, local correction and original punctured chart are kept through all degrees.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A localized sphere form with an original global primitive has a compactly supported
Euclidean primitive in the same punctured-sphere chart. -/
theorem exists_sphereExactForm_compactlySupported_primitive (r p : ℕ)
    (form : SmoothDifferentialForm (n := r) (OrthogonalSphere r) (p + 1))
    (x : OrthogonalSphere r) (hzero : ∀ᶠ y in 𝓝 x, form.val y = 0)
    (primitive : SmoothDifferentialForm (n := r) (OrthogonalSphere r) p)
    (hprimitive : smoothFormExteriorDerivative (n := r) p primitive = form) :
    ∃ η : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r) [⋀^Fin p]→L[ℝ] ℂ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      ∀ z, extDeriv η z = differentialFormInChart form.val (stereographic' r x) z := by
  classical
  let S := OrthogonalSphere r
  let V := EuclideanSpace ℝ (Fin r)
  let c := chartAt V x
  have hc : c ∈ atlas V S := chart_mem_atlas V x
  have hcx : x ∈ c.source := mem_chart_source V x
  have hct : c.target = univ := stereographic'_target (-x)
  have hclosedNear : ∀ᶠ y in 𝓝 x,
      (smoothFormExteriorDerivative (n := r) p primitive).val y = 0 := hprimitive.symm ▸ hzero
  have hadjusted : ∃ u : SmoothDifferentialForm (n := r) S p,
      smoothFormExteriorDerivative (n := r) p u = form ∧ ∀ᶠ y in 𝓝 x, u.val y = 0 := by
    cases p with
    | succ p =>
      obtain ⟨v, hv⟩ := exists_smoothFormPrimitive_near_of_eventually_closed p primitive
        c hc hct x hcx hclosedNear
      let u := primitive - smoothFormExteriorDerivative (n := r) p v
      refine ⟨u, ?_, ?_⟩
      · change smoothFormExteriorDerivative (n := r) (p + 1)
          (primitive - smoothFormExteriorDerivative (n := r) p v) = form
        rw [map_sub, hprimitive]
        have hdd := LinearMap.congr_fun (smoothFormExteriorDerivative_comp (n := r) (M := S) p) v
        change smoothFormExteriorDerivative (n := r) (p + 1)
          (smoothFormExteriorDerivative (n := r) p v) = 0 at hdd
        rw [hdd, sub_zero]
      · filter_upwards [hv] with y hy
        change primitive.val y - (smoothFormExteriorDerivative (n := r) p v).val y = 0
        rw [hy, sub_self]
    | zero =>
      -- In degree zero, local closedness means that the same scalar coefficient is constant.
      let F (z : V) : ℂ := primitive.val (c.symm z) 0
      have hcoeff : differentialFormInChart primitive.val c =
          fun z ↦ constOfIsEmpty ℝ V (Fin 0) (F z) := by
        ext z v
        change primitive.val (c.symm z) _ = primitive.val (c.symm z) 0
        exact congrArg (primitive.val (c.symm z)) (Subsingleton.elim _ _)
      have hF : ContDiff ℝ ∞ F := by
        have h := (constOfIsEmptyLIE ℝ V ℂ (Fin 0)).symm.contDiff.comp_contDiffOn
          (primitive.property c hc)
        rw [hcoeff] at h
        exact contDiffOn_univ.mp (hct ▸ h)
      have hnearD : ∀ᶠ z in 𝓝 (c x), fderiv ℝ F z = 0 := by
        have hnear := hclosedNear
        rw [← c.left_inv hcx] at hnear
        filter_upwards [(c.continuousAt_symm (c.map_source hcx)).preimage_mem_nhds hnear]
          with z hz
        have h := smoothFormExteriorDerivative_inChart primitive c hc z
          (hct.symm ▸ mem_univ z)
        have hleft : differentialFormInChart
            (smoothFormExteriorDerivative (n := r) 0 primitive).val c z = 0 := by
          change ((smoothFormExteriorDerivative (n := r) 0 primitive).val
            (c.symm z)).compContinuousLinearMap _ = 0
          rw [hz]
          ext v
          rfl
        rw [hleft, hcoeff, extDeriv_constOfIsEmpty] at h
        apply ContinuousLinearMap.ext
        intro v
        exact congrArg (fun a ↦ a (fun _ : Fin 1 ↦ v)) h.symm
      obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.mp hnearD
      have hconstant (z : V) (hz : z ∈ ball (c x) ε) : F z = F (c x) :=
        isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (c x) ε).isPreconnected
          (hF.differentiable (by simp)).differentiableOn
          (fun z hz ↦ hεD hz) hz (mem_ball_self hε)
      let constant : SmoothDifferentialForm (n := r) S 0 :=
        ⟨fun _ ↦ constOfIsEmpty ℝ V (Fin 0) (F (c x)), by
          intro a ha
          convert (contDiffOn_const : ContDiffOn ℝ ∞
            (fun _ : V ↦ constOfIsEmpty ℝ V (Fin 0) (F (c x))) a.target) using 1
          ext z v
          rfl⟩
      have hdconstant : smoothFormExteriorDerivative (n := r) 0 constant = 0 := by
        apply Subtype.ext
        funext y
        have hs : (smoothFormExteriorDerivative (n := r) 0 constant).val y =
            differentialFormExteriorDerivative constant.val y :=
          (existsUnique_smoothFormExteriorDerivative (n := r) (M := S) 0).exists.choose_spec
            constant y
        rw [hs]
        have hcoef : differentialFormInChart constant.val (chartAt V y) =
            fun _ : V ↦ constOfIsEmpty ℝ V (Fin 0) (F (c x)) := by ext z v; rfl
        dsimp only [differentialFormExteriorDerivative]
        rw [hcoef]
        have hd : extDeriv (fun _ : V ↦ constOfIsEmpty ℝ V (Fin 0) (F (c x)))
            (chartAt V y y) = 0 := by
          simp only [extDeriv, fderiv_const_apply]
          exact (alternatizeUncurryFinCLM ℝ V ℂ).map_zero
        rw [hd]
        ext v
        rfl
      refine ⟨primitive - constant, ?_, ?_⟩
      · rw [map_sub, hprimitive, hdconstant, sub_zero]
      · filter_upwards [(c.continuousAt hcx).preimage_mem_nhds (ball_mem_nhds (c x) hε),
          c.open_source.mem_nhds hcx] with y hy hyc
        ext v
        change primitive.val y v - F (c x) = 0
        have h := hconstant (c y) hy
        change primitive.val (c.symm (c y)) 0 = F (c x) at h
        rw [c.left_inv hyc] at h
        rw [show v = 0 from Subsingleton.elim _ _, h, sub_self]
  obtain ⟨u, hdu, hunear⟩ := hadjusted
  let a := stereographic' r x
  have ha : a ∈ atlas V S := ⟨x, rfl⟩
  have hat : a.target = univ := stereographic'_target x
  let η : V → V [⋀^Fin p]→L[ℝ] ℂ := differentialFormInChart u.val a
  have hη : ContDiff ℝ ∞ η := contDiffOn_univ.mp (hat ▸ u.property a ha)
  refine ⟨η, hη, ?_, ?_⟩
  · -- The original support is a compact subset of the punctured sphere.
    let K : Set S := closure {y : S | u.val y ≠ 0}
    have hK : IsCompact K := isClosed_closure.isCompact
    have hxK : x ∉ K := by
      intro hxK
      obtain ⟨y, hy, hyK⟩ := mem_closure_iff_nhds.mp hxK {y : S | u.val y = 0} hunear
      exact hyK hy
    have hKa : K ⊆ a.source := by
      intro y hy
      change y ∈ (stereographic' r x).source
      rw [stereographic'_source]
      intro hyx
      exact hxK (show x ∈ K from (mem_singleton_iff.mp hyx) ▸ hy)
    have himage : IsCompact (a '' K) := hK.image_of_continuousOn (a.continuousOn.mono hKa)
    apply himage.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ himage.isClosed
    intro z hz
    have hzK : a.symm z ∈ K := by
      apply subset_closure
      intro hz0
      apply hz
      change (u.val (a.symm z)).compContinuousLinearMap _ = 0
      rw [hz0]
      ext v
      rfl
    exact ⟨a.symm z, hzK, a.right_inv (hat.symm ▸ mem_univ z)⟩
  · intro z
    have h := smoothFormExteriorDerivative_inChart u a ha z (hat.symm ▸ mem_univ z)
    rw [hdu] at h
    exact h.symm

end AtiyahSinger
