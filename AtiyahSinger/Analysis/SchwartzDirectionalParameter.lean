/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzParameterCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Fréchet differentiation of a parameterized Schwartz map

Public module ID: M0940.

Continuous directional Schwartz derivatives, paired with the same continuous
linear map, give an actual Fréchet derivative when the paired derivative
is a continuous field of bounded linear maps. The mean-value estimate is uniform
along the short segment; pointwise directional differentiability alone is not
substituted for Fréchet differentiability.

This extends the scalar-parameter integral argument to the local parameter
spaces used in SG III.13.6. No norm on Schwartz space is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology Asymptotics
open scoped ContDiff SchwartzMap

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Continuous paired directional derivatives give the full derivative of a Schwartz map. -/
theorem hasFDerivAt_schwartzMap
    (F : D → 𝓢(E, ℂ)) (G : D → D → 𝓢(E, ℂ))
    (hG : Continuous (fun z : D × D ↦ G z.1 z.2))
    (hderiv : ∀ (x v : D) (t : ℝ) (y : E),
      HasDerivAt (fun u ↦ F (x + u • v) y) (G (x + t • v) v y) t)
    (L : 𝓢(E, ℂ) →L[ℂ] V) (d : D → D →L[ℝ] V) (hd : Continuous d)
    (hL : ∀ x v : D, L (G x v) = d x v) (x : D) :
    HasFDerivAt (fun z ↦ L (F z)) (d x) x := by
  have hline (v : D) (t : ℝ) :
      HasDerivAt (fun u ↦ L (F (x + u • v))) (d (x + t • v) v) t := by
    have hc : Continuous (fun u : ℝ ↦ G (x + u • v) v) :=
      hG.comp ((continuous_const.add (continuous_id.smul continuous_const)).prodMk
        continuous_const)
    have h := hasDerivAt_schwartzMap (fun u ↦ F (x + u • v))
      (fun u ↦ G (x + u • v) v) hc (hderiv x v) L t
    rw [hL] at h
    exact h
  -- Continuity of the paired derivative gives one bound valid on the whole short segment.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hd.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : D) hδ] with v hv
  have hvδ : ‖v‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  let f (t : ℝ) : V := L (F (x + t • v)) - t • d x v
  let f' (t : ℝ) : V := d (x + t • v) v - d x v
  have hdf (t : ℝ) : HasDerivAt f (f' t) t := by
    have h := (hline v t).sub ((hasDerivAt_id t).smul_const (d x v))
    change HasDerivAt f (d (x + t • v) v - (1 : ℝ) • d x v) t at h
    simpa only [one_smul] using h
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖f' t‖ ≤ ε * ‖v‖ := by
    have htNorm : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2.le
    have hy : dist (x + t • v) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg v) htNorm).trans_lt hvδ
    have hnorm : ‖d (x + t • v) - d x‖ < ε := by
      simpa only [dist_eq_norm] using hclose hy
    change ‖(d (x + t • v) - d x) v‖ ≤ _
    exact (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg v))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (hdf t).hasDerivWithinAt) hbound
  -- The endpoints of the same segment give the actual Fréchet remainder.
  have heq : f 1 - f 0 = L (F (x + v)) - L (F x) - d x v := by
    dsimp only [f]
    simp only [one_smul, zero_smul, add_zero, sub_zero]
    abel
  rwa [heq] at h

end AtiyahSinger
