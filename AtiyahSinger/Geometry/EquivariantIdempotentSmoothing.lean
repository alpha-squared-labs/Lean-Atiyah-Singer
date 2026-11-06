/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.IdempotentHomotopy
public import AtiyahSinger.Analysis.SmoothIdempotentCorrection
public import AtiyahSinger.Geometry.CompactParameterIntegral
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.RepresentationTheory.Continuous.Basic

import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Equivariant smoothing of finite idempotent families

Public module ID: M1193.

Smooth approximation, compact-group conjugation averaging and the analytic
idempotent correction preserve the specified representation. The resulting
smooth idempotent has an invertible canonical intertwiner with the original
continuous family. Neither self-adjointness nor a fixed image rank is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Topology
open scoped Manifold ContDiff

/-- The power-series idempotent correction is natural under continuous algebra isomorphisms. -/
theorem map_idempotentCorrection {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [NormedRing B] [NormedAlgebra ℝ B] (e : A ≃A[ℝ] B) (a : A) :
    e (idempotentCorrection a) = idempotentCorrection (e a) := by
  have ht (f : ℕ → A) : e (∑' k, f k) = ∑' k, e (f k) :=
    e.toContinuousLinearEquiv.map_tsum
  simp only [idempotentCorrection, map_smul, map_add, map_one, map_mul, map_sub,
    ht, map_pow]

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]
  [MulAction G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A finite continuous equivariant idempotent family has a smooth equivariant
idempotent family with an invertible canonical intertwiner. -/
theorem exists_smooth_equivariant_idempotent
    (ρ : ContRepresentation ℂ G V)
    (hρ : ContMDiff 𝓘(ℝ, VG) 𝓘(ℝ, V →L[ℂ] V) ∞ (fun g ↦ ρ g))
    (P : M → V →L[ℂ] V) (hP : Continuous P)
    (hPP : ∀ x, P x * P x = P x)
    (hcov : ∀ (g : G) (x : M), P (g • x) * ρ g = ρ g * P x) :
    ∃ Q : M → V →L[ℂ] V,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞ Q ∧
      (∀ x, Q x * Q x = Q x) ∧
      (∀ (g : G) (x : M), Q (g • x) * ρ g = ρ g * Q x) ∧
      ∀ x, IsUnit (idempotentIntertwiner (Q x) (P x)) := by
  classical
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haar
  let μ : Measure G := (ν Set.univ)⁻¹ • ν
  let A := V →L[ℂ] V
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let IG := 𝓘(ℝ, VG)
  have hcancel (g : G) : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hcancel' (g : G) : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hPconj (g : G) (x : M) : ρ g * P (g⁻¹ • x) * ρ g⁻¹ = P x := by
    rw [← hcov, smul_inv_smul, mul_assoc, hcancel, mul_one]
  -- One open neighborhood controls both analytic correction and the
  -- invertibility of the original-to-corrected image intertwiner.
  let Ω : Set (A × A) := {z | ‖(4 : ℝ) • (z.2 * z.2 - z.2)‖ < 1 ∧
    ‖idempotentIntertwiner (idempotentCorrection z.2) z.1 - 1‖ < 1}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hd : Continuous (fun w : A × A ↦ ‖(4 : ℝ) • (w.2 * w.2 - w.2)‖) := by
      fun_prop
    have hQ : ContinuousAt (fun w : A × A ↦ idempotentCorrection w.2) z :=
      (contDiffAt_idempotentCorrection z.2 hz.1).continuousAt.comp
        continuous_snd.continuousAt
    have hT : ContinuousAt (fun w : A × A ↦
        ‖idempotentIntertwiner (idempotentCorrection w.2) w.1 - 1‖) z := by
      dsimp only [idempotentIntertwiner]
      exact (((continuousAt_const.sub hQ).sub continuousAt_fst).add
        ((continuousAt_const.mul hQ).mul continuousAt_fst) |>.sub continuousAt_const).norm
    exact (hd.continuousAt.eventually_lt continuousAt_const hz.1).and
      (hT.eventually_lt continuousAt_const hz.2)
  have hdiag : IsCompact (Set.range (fun x : M ↦ (P x, P x))) :=
    isCompact_range (hP.prodMk hP)
  have hdiagΩ : Set.range (fun x : M ↦ (P x, P x)) ⊆ Ω := by
    rintro _ ⟨x, rfl⟩
    constructor
    · simp only [hPP, sub_self, smul_zero, norm_zero, zero_lt_one]
    · rw [idempotentCorrection_eq (P x) (hPP x)]
      have hid : idempotentIntertwiner (P x) (P x) = 1 := by
        dsimp only [idempotentIntertwiner]
        noncomm_ring [hPP x]
      rw [hid, sub_self, norm_zero]
      exact zero_lt_one
  obtain ⟨ε, hε, hεΩ⟩ := hdiag.exists_thickening_subset_open hΩ hdiagΩ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuous.continuousOn
  let K : ℝ := max C 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKbound (g : G) : ‖ρ g‖ ≤ K := (hC g (Set.mem_univ _)).trans (le_max_left _ _)
  let δ : ℝ := ε / (2 * K ^ 2)
  have hδ : 0 < δ := div_pos hε (mul_pos two_pos (sq_pos_of_pos hK))
  obtain ⟨a, ha, _⟩ := hP.exists_contMDiff_approx I (⊤ : ℕ∞)
    continuous_const (fun _ ↦ hδ)
  let R (x : M) (g : G) : A := ρ g * a (g⁻¹ • x) * ρ g⁻¹
  have hmul : ContDiff ℝ ∞ (fun z : A × A ↦ z.1 * z.2) :=
    contDiff_fst.mul contDiff_snd
  have hR : ContMDiff (IG.prod I) 𝓘(ℝ, A) ∞ (fun z : G × M ↦ R z.2 z.1) := by
    have hleft := hmul.contMDiff.comp ((hρ.comp contMDiff_fst).prodMk_space
      (a.contMDiff.comp (((contMDiff_inv IG ∞).comp contMDiff_fst).smul contMDiff_snd)))
    exact hmul.contMDiff.comp
      (hleft.prodMk_space (hρ.comp ((contMDiff_inv IG ∞).comp contMDiff_fst)))
  have hRI (x : M) : Integrable (R x) μ :=
    (hR.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let b (x : M) : A := ∫ g, R x g ∂μ
  -- Spatial differentiation under this compact-parameter integral makes the
  -- averaged family smooth, in the original manifold charts.
  have hb : ContMDiff I 𝓘(ℝ, A) ∞ b := by
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hchart : ContMDiffOn (IG.prod I) 𝓘(ℝ, A) ∞
        (fun z : G × EuclideanSpace ℝ (Fin n) ↦ R (c.symm z.2) z.1)
        (Set.univ ×ˢ c.target) :=
      hR.comp_contMDiffOn (contMDiffOn_fst.prodMk
        ((contMDiffOn_chart_symm (I := I) (x := x)).comp contMDiffOn_snd
          (fun _ hz ↦ hz.2)))
    have hi := contDiffOn_integral_of_compact_manifold IG μ c.open_target hchart
    have hx := c.map_source (mem_chart_source _ x)
    have hl := (hi.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hx)).comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := I) x)
        (mem_chart_source _ x))
    apply hl.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x)] with y hy
    dsimp only [Function.comp_apply, b]
    rw [c.left_inv hy]
  have hberr (x : M) : ‖b x - P x‖ < ε := by
    have hd (g : G) : ‖R x g - P x‖ ≤ K ^ 2 * δ := by
      have he : R x g - P x = ρ g * (a (g⁻¹ • x) - P (g⁻¹ • x)) * ρ g⁻¹ := by
        rw [mul_sub, sub_mul, hPconj]
      have herr : ‖a (g⁻¹ • x) - P (g⁻¹ • x)‖ ≤ δ :=
        (show ‖a (g⁻¹ • x) - P (g⁻¹ • x)‖ < δ by
          simpa only [dist_eq_norm] using ha (g⁻¹ • x)).le
      rw [he]
      calc
        _ ≤ ‖ρ g‖ * ‖a (g⁻¹ • x) - P (g⁻¹ • x)‖ * ‖ρ g⁻¹‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ K * δ * K := by gcongr <;> apply hKbound
        _ = K ^ 2 * δ := by ring
    have hle : ‖b x - P x‖ ≤ K ^ 2 * δ := by
      have he : b x - P x = ∫ g, R x g - P x ∂μ := by
        rw [integral_sub (hRI x) (integrable_const _)]; simp [b]
      rw [he]
      calc
        _ ≤ ∫ g, ‖R x g - P x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ _g : G, K ^ 2 * δ ∂μ :=
          integral_mono ((hRI x).sub (integrable_const _)).norm (integrable_const _) hd
        _ = _ := by simp
    have hval : K ^ 2 * δ = ε / 2 := by dsimp only [δ]; field_simp
    exact hle.trans_lt (hval ▸ half_lt_self hε)
  have hbΩ (x : M) : (P x, b x) ∈ Ω := by
    apply hεΩ
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(P x, P x), ⟨x, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
    change dist (b x : V →L[ℂ] V) (P x) < ε
    rw [dist_eq_norm]
    exact hberr x
  have hbconj (g : G) (x : M) : ρ g * b x * ρ g⁻¹ = b (g • x) := by
    let e := ContinuousLinearEquiv.ofUnit (ρ.toMonoidHom.toHomUnits g)
    have hI := e.conjContinuousAlgEquiv.toContinuousLinearEquiv.integral_comp_comm (μ := μ) (R x)
    change (∫ h, ρ g * R x h * ρ g⁻¹ ∂μ) = ρ g * b x * ρ g⁻¹ at hI
    rw [← hI]
    calc
      _ = ∫ h, R (g • x) (g * h) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with h
        simp only [R, map_mul, mul_inv_rev, mul_smul, inv_smul_smul]
        noncomm_ring
      _ = _ := integral_mul_left_eq_self (μ := μ) (R (g • x)) g
  let Q (x : M) : A := idempotentCorrection (b x)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (contDiffAt_idempotentCorrection (b x) (hbΩ x).1).contMDiffAt.comp x (hb x)
  · intro x
    exact isIdempotentElem_idempotentCorrection (b x) (hbΩ x).1
  · intro g x
    let e := ContinuousLinearEquiv.ofUnit (ρ.toMonoidHom.toHomUnits g)
    let γ : A ≃A[ℝ] A := {
      __ := e.conjContinuousAlgEquiv.toAlgEquiv.restrictScalars ℝ
      continuous_toFun := e.conjContinuousAlgEquiv.continuous
      continuous_invFun := e.conjContinuousAlgEquiv.symm.continuous }
    have hnat := map_idempotentCorrection γ (b x)
    change ρ g * Q x * ρ g⁻¹ = idempotentCorrection (ρ g * b x * ρ g⁻¹) at hnat
    rw [hbconj] at hnat
    change ρ g * Q x * ρ g⁻¹ = Q (g • x) at hnat
    rw [← hnat, mul_assoc, hcancel', mul_one]
  · intro x
    exact isUnit_idempotentIntertwiner_of_norm_lt (Q x) (P x) (hbΩ x).2

end AtiyahSinger
