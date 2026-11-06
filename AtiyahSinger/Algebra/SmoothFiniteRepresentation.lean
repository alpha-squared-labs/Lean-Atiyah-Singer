/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

import AtiyahSinger.Geometry.SmoothConvolution
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Automatic smoothness of an original finite continuous representation

Public module ID: M0058.

A jointly continuous finite-dimensional complex representation of a
finite-dimensional real Lie group has a jointly real-smooth action. The
statement retains the specified representation on `Fin dimension → ℂ`, its
original linear operators and the original group manifold structure. It
introduces no replacement representation or group action.

Finite dimensionality of the full real group model is explicit: mathlib's
`LieGroup` alone does not impose it. No compactness, global countability,
connectedness, positive representation rank or invariant inner product is
needed. The target smoothness is real smoothness, not complex analyticity
of a general real Lie group.

SG III.9, pp.211--212, gives the finite representation background. The
automatic smoothness theorem is proved here by the standard Haar convolution
argument: a small smooth bump gives an invertible average of the original
matrices; smoothness of its convolution then recovers those same matrices.

For a downstream representation product bundle, keep the original Pi fibers
and diagonal action. `EuclideanSpace.equiv` supplies fixed continuous linear
coordinates when the smooth-bundle model is Euclidean. That coordinate change
does not replace the bundle or its action. Smoothness for an unrelated bundle
atlas must not be inferred without compatibility with this original global frame.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.FiniteContinuousRepresentation

open MeasureTheory Filter Set Topology
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]

include hDim hLie

set_option maxHeartbeats 1000000 in
-- Track the normed operator integral, its inverse, and the original real-smooth action.
/-- The actual jointly continuous finite representation action is jointly real smooth. -/
theorem contMDiff_action (ρ : FiniteContinuousRepresentation G) :
    ContMDiff (𝓘(ℝ, VG).prod 𝓘(ℝ, Fin ρ.dimension → ℂ))
      𝓘(ℝ, Fin ρ.dimension → ℂ) ∞
      (fun p : G × (Fin ρ.dimension → ℂ) ↦ ρ.representation p.1 p.2) := by
  classical
  -- Local Hausdorff coordinates separate the identity in the original topological group.
  let : T2Space G := by
    apply IsTopologicalGroup.t2Space_of_one_sep
    intro x hx
    let c := chartAt VG (1 : G)
    have h1 : (1 : G) ∈ c.source := mem_chart_source VG 1
    by_cases hxc : x ∈ c.source
    · have hne : c 1 ≠ c x := fun h ↦ hx (c.injOn hxc h1 h.symm)
      let U := c.source ∩ c ⁻¹' ({c x}ᶜ)
      have hU : IsOpen U :=
        c.continuousOn.isOpen_inter_preimage c.open_source isClosed_singleton.isOpen_compl
      exact ⟨U, hU.mem_nhds ⟨h1, hne⟩, fun h ↦ h.2 rfl⟩
    · exact ⟨c.source, c.open_source.mem_nhds h1, hxc⟩
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace VG G
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  let W := Fin ρ.dimension → ℂ
  have hρ : Continuous (fun g : G ↦ ρ.representation g) := by
    apply continuous_clm_apply.mpr
    intro v
    exact ρ.continuous_action.comp (continuous_id.prodMk continuous_const)
  -- A bump supported where the actual matrices are near identity gives an invertible average.
  have hex : ∃ φ : SmoothBumpFunction 𝓘(ℝ, VG) (1 : G),
      IsUnit (∫ g, ((φ g) / (∫ g, φ g ∂μ)) • ρ.representation g ∂μ) := by
    have hnear : {g : G | ‖ρ.representation g - 1‖ < (1 / 2 : ℝ)} ∈ 𝓝 1 := by
      have hc : ContinuousAt (fun g : G ↦ ‖ρ.representation g - 1‖) 1 :=
        (hρ.sub continuous_const).norm.continuousAt
      have h0 : ‖ρ.representation (1 : G) - 1‖ < (1 / 2 : ℝ) := by
        simp only [map_one, sub_self, norm_zero]
        norm_num
      exact hc.preimage_mem_nhds (Iio_mem_nhds h0)
    obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
      (I := 𝓘(ℝ, VG)) (1 : G)).mem_iff.mp hnear
    let J := ∫ g, φ g ∂μ
    have hJ : 0 < J := φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      φ.hasCompactSupport (fun g ↦ φ.nonneg (x := g)) (by rw [φ.eq_one]; norm_num)
    let η : G → ℝ := fun g ↦ φ g / J
    have hηcont : Continuous η := φ.continuous.div_const J
    have hηsupp : HasCompactSupport η := by
      rw [hasCompactSupport_iff_eventuallyEq]
      filter_upwards [hasCompactSupport_iff_eventuallyEq.mp φ.hasCompactSupport] with g hg
      change φ g / J = 0
      change φ g = 0 at hg
      rw [hg, zero_div]
    have hηint : Integrable η μ := hηcont.integrable_of_hasCompactSupport hηsupp
    have hηnonneg (g : G) : 0 ≤ η g := div_nonneg (φ.nonneg (x := g)) hJ.le
    have hηone : (∫ g, η g ∂μ) = 1 := by
      change (∫ g, φ g / J ∂μ) = 1
      rw [integral_div]
      exact div_self hJ.ne'
    have herrint : Integrable (fun g ↦ η g • (ρ.representation g - 1)) μ :=
      (hηcont.smul (hρ.sub continuous_const)).integrable_of_hasCompactSupport
        hηsupp.smul_right
    have hmainint : Integrable (fun g ↦ η g • ρ.representation g) μ :=
      (hηcont.smul hρ).integrable_of_hasCompactSupport hηsupp.smul_right
    have hconstint : Integrable (fun g ↦ η g • (1 : W →L[ℂ] W)) μ :=
      hηint.smul_const _
    have heq : (∫ g, η g • ρ.representation g ∂μ) - 1 =
        ∫ g, η g • (ρ.representation g - 1) ∂μ := by
      simp_rw [smul_sub]
      rw [integral_sub hmainint hconstint, integral_smul_const, hηone, one_smul]
    have hbound : ‖∫ g, η g • (ρ.representation g - 1) ∂μ‖ ≤ (1 / 2 : ℝ) := by
      calc
        _ ≤ ∫ g, ‖η g • (ρ.representation g - 1)‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ g, η g / 2 ∂μ := by
          apply integral_mono herrint.norm (hηint.div_const 2)
          intro g
          change ‖η g • (ρ.representation g - 1)‖ ≤ η g / 2
          rw [norm_smul, Real.norm_of_nonneg (hηnonneg g)]
          by_cases hg : g ∈ tsupport φ
          · have hb : ‖ρ.representation g - 1‖ ≤ (1 / 2 : ℝ) := le_of_lt (hφ hg)
            nlinarith [mul_le_mul_of_nonneg_left hb (hηnonneg g)]
          · have hz : η g = 0 := by simp [η, image_eq_zero_of_notMem_tsupport hg]
            rw [hz]
            norm_num
        _ = 1 / 2 := by rw [integral_div, hηone]
    refine ⟨φ, ?_⟩
    have hn : ‖1 - ∫ g, η g • ρ.representation g ∂μ‖ < 1 := by
      rw [norm_sub_rev, heq]
      linarith
    have hu := (Units.oneSub (1 - ∫ g, η g • ρ.representation g ∂μ) hn).isUnit
    simpa only [Units.val_oneSub, sub_sub_self] using hu
  obtain ⟨φ, hφ⟩ := hex
  let J := ∫ g, φ g ∂μ
  let η : G → ℝ := fun g ↦ φ g / J
  have hη : ContMDiff 𝓘(ℝ, VG) 𝓘(ℝ) ∞ η := by
    apply (((ContinuousLinearMap.mul ℝ ℝ).flip J⁻¹).contMDiff.comp φ.contMDiff).congr
    intro g
    exact div_eq_mul_inv (φ g) J
  have hηsupp : HasCompactSupport η := by
    rw [hasCompactSupport_iff_eventuallyEq]
    filter_upwards [hasCompactSupport_iff_eventuallyEq.mp φ.hasCompactSupport] with g hg
    change φ g / J = 0
    change φ g = 0 at hg
    rw [hg, zero_div]
  have hint : Integrable (fun g ↦ η g • ρ.representation g) μ :=
    (hη.continuous.smul hρ).integrable_of_hasCompactSupport hηsupp.smul_right
  let A := ∫ g, η g • ρ.representation g ∂μ
  have hA : IsUnit A := hφ
  obtain ⟨U, hU⟩ := hA
  let H : G → (W →L[ℂ] W) := fun x ↦ ∫ g, η (x * g) • ρ.representation g ∂μ
  -- Smoothness comes from the translated bump; the original representation remains continuous.
  have hH : ContMDiff 𝓘(ℝ, VG) 𝓘(ℝ, W →L[ℂ] W) ∞ H :=
    contMDiff_integral_mul_smul_of_hasCompactSupport μ η hη hηsupp _ hρ
  have hformula (x : G) : H x = ρ.representation x⁻¹ * A := by
    have hchange := integral_mul_left_eq_self (μ := μ)
      (fun g : G ↦ η (x * g) • ρ.representation g) x⁻¹
    calc
      H x = ∫ g, η g • ρ.representation (x⁻¹ * g) ∂μ := by
        simpa only [H, mul_inv_cancel_left] using hchange.symm
      _ = ∫ g, ρ.representation x⁻¹ * (η g • ρ.representation g) ∂μ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro g
        change η g • ρ.representation (x⁻¹ * g) =
          ρ.representation x⁻¹ * (η g • ρ.representation g)
        rw [map_mul, mul_smul_comm]
      _ = ρ.representation x⁻¹ * A := integral_const_mul_of_integrable hint
  -- The same invertible average recovers every original matrix from the smooth convolution.
  have hmatrix : ContMDiff 𝓘(ℝ, VG) 𝓘(ℝ, W →L[ℂ] W) ∞
      (fun x : G ↦ ρ.representation x) := by
    have hh := (((ContinuousLinearMap.mul ℝ (W →L[ℂ] W)).flip
      (↑U⁻¹ : W →L[ℂ] W)).contMDiff).comp
        (hH.comp (contMDiff_inv 𝓘(ℝ, VG) ∞))
    apply hh.congr
    intro x
    change ρ.representation x = H x⁻¹ * ↑U⁻¹
    rw [hformula, inv_inv, ← hU, mul_assoc]
    simp
  -- Evaluation of these original operators is real smooth in the vector as well.
  have hreal := (ContinuousLinearMap.restrictScalarsL ℂ W W ℝ ℝ).contMDiff.comp hmatrix
  exact (hreal.comp contMDiff_fst).clm_apply contMDiff_snd

end AtiyahSinger.FiniteContinuousRepresentation
