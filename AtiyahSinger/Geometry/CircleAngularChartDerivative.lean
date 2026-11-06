/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.CircleCotangent

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The positive period-one covering and original circle covectors

Public module ID: M1121.

The derivative adjoint of an actual angular-to-native chart reads the original
cotangent coefficient with the positive factor 2π. This is an equality on the
same chart and covector, not a sign convention for a chosen stereographic chart.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The actual period-one covering contributes the positive factor 2π to native covectors. -/
theorem circlePeriodOne_fderiv_adjoint
    (c : OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle)
    (e : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (he : ∀ y, e y = c (Circle.exp (2 * Real.pi *
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm y)))
    (x η : EuclideanSpace ℝ (Fin 1))
    (hx : Circle.exp (2 * Real.pi *
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x) ∈ c.source) :
    let l := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    l ((fderiv ℝ e x).adjoint η) = (2 * Real.pi) *
      circleCovectorCoordinate (Circle.exp (2 * Real.pi * l x))
        (covectorFromChart c (Circle.exp (2 * Real.pi * l x)) η) := by
  classical
  let X := EuclideanSpace ℝ (Fin 1)
  let I := 𝓘(ℝ, X)
  let l : X ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let z : Circle := Circle.exp (2 * Real.pi * l x)
  let γ (t : ℝ) : Circle := z * Circle.exp t
  let g (t : ℝ) : X := c (γ t)
  have hγ0 : γ 0 = z := by simp [γ]
  -- The centered rotation curve uses precisely the tangent in circleCovectorCoordinate.
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    (show ContMDiff 𝓘(ℝ, ℝ) I ∞ γ from
      contMDiff_const.mul contMDiff_circleExp).mdifferentiableAt (by simp)
  have hcAt : MDifferentiableAt I I c z :=
    ((contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc)) z hx).contMDiffAt
        (c.open_source.mem_nhds hx) |>.mdifferentiableAt (by simp)
  have hcg := mfderiv_comp_of_eq (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I)
    hcAt hγ hγ0
  have hg : DifferentiableAt ℝ g 0 := by
    apply mdifferentiableAt_iff_differentiableAt.mp
    exact (hcAt.comp_of_eq 0 hγ hγ0)
  have hg1 : fderiv ℝ g 0 1 = mfderiv I I c z (circleAngularTangent z) := by
    have h := congrArg (fun L ↦ L (1 : ℝ)) hcg
    rw [mfderiv_eq_fderiv] at h
    have ht : circleAngularTangent z = mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) := by
      simp only [circleAngularTangent]
      rfl
    change fderiv ℝ g 0 (1 : ℝ) =
      mfderiv I I c (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) at h
    rw [hγ0] at h
    exact h.trans (congrArg (fun v : X ↦ mfderiv I I c z v) ht.symm)
  -- Recenter the exact given chart formula and differentiate its explicit positive scaling.
  let a (y : X) : ℝ := 2 * Real.pi * (l y - l x)
  have ha0 : a x = 0 := by simp [a]
  have ha : HasFDerivAt a ((2 * Real.pi) •
      l.toContinuousLinearEquiv.toContinuousLinearMap) x := by
    exact (l.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.sub_const
      (l x)).const_smul (2 * Real.pi)
  have hfun (y : X) : e y = g (a y) := by
    rw [he]
    change c (Circle.exp (2 * Real.pi * l y)) =
      c (Circle.exp (2 * Real.pi * l x) * Circle.exp (2 * Real.pi * (l y - l x)))
    rw [← Circle.exp_add]
    apply congrArg c
    apply congrArg Circle.exp
    ring
  have heder : fderiv ℝ e x = (fderiv ℝ g 0).comp
      ((2 * Real.pi) • l.toContinuousLinearEquiv.toContinuousLinearMap) := by
    have hgg : HasFDerivAt g (fderiv ℝ g 0) (a x) := ha0.symm ▸ hg.hasFDerivAt
    exact ((hgg.comp x ha).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hfun)).fderiv
  -- The real adjoint reads the same chart derivative on the canonical positive unit vector.
  let v : X := l.symm 1
  have hread (w : X) : l w = inner ℝ w v := by
    rw [← l.inner_map_map]
    simp [v]
  change l ((fderiv ℝ e x).adjoint η) = (2 * Real.pi) * _
  rw [hread, ContinuousLinearMap.adjoint_inner_left, heder]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    v, l.apply_symm_apply, smul_eq_mul, mul_one]
  have hgperiod : fderiv ℝ g 0 (2 * Real.pi) =
      (2 * Real.pi) • mfderiv I I c z (circleAngularTangent z) := by
    calc
      _ = fderiv ℝ g 0 ((2 * Real.pi) • (1 : ℝ)) := by simp
      _ = _ := by
        rw [map_smul, hg1]
        rfl
  rw [hgperiod]
  change inner ℝ η ((2 * Real.pi) • (mfderiv I I c z (circleAngularTangent z) : X)) =
    (2 * Real.pi) * inner ℝ η (mfderiv I I c z (circleAngularTangent z) : X)
  exact real_inner_smul_right _ _ _

end AtiyahSinger
