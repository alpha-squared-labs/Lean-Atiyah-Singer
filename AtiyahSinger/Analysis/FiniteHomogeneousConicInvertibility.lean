/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform conic invertibility of finite homogeneous sums

A compact family of finite real weighted sums is invertible in one uniform
cone about the horizontal axis if its actual axis sum is elliptic. The summands
need only be continuous near that axis. Openness of invertibility and the
compact unit sphere give one transverse neighborhood; homogeneity rescales it
to the full cone. The real weights may be signed and remain the specified ones.

This is the compactness step needed for the actual associated-sphere chart
splittings. A homotopy parameter can be included in the compact parameter
space. The result does not identify the original chart symbols, remove their
frequency cutoffs, or assert a compact-support K-class equality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped Topology

variable {Z X Y E F ι : Type*} [TopologicalSpace Z] [CompactSpace Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [Fintype ι]

/-- The same finite weighted homogeneous sum is uniformly invertible near its elliptic axis. -/
theorem exists_bijective_weightedHomogeneousSum_in_cone
    (a : ι → Z → X → Y → E →L[ℂ] F) (w : ι → Z → ℝ) (m : ℝ)
    (hw : ∀ i, Continuous (w i))
    (ha : ∀ i z ξ, ξ ≠ 0 →
      ContinuousAt (fun u : Z × X × Y ↦ a i u.1 u.2.1 u.2.2) (z, ξ, 0))
    (hhom : ∀ i z ξ η s, 0 < s →
      a i z (s • ξ) (s • η) = ((s ^ m : ℝ) : ℂ) • a i z ξ η)
    (haxis : ∀ z ξ, ξ ≠ 0 → Function.Bijective
      (∑ i, (w i z : ℂ) • a i z ξ 0 : E →L[ℂ] F)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ξ η, ξ ≠ 0 → ‖η‖ < δ * ‖ξ‖ →
      Function.Bijective (∑ i, (w i z : ℂ) • a i z ξ η : E →L[ℂ] F) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let A (z : Z) (ξ : X) (η : Y) : E →L[ℂ] F := ∑ i, (w i z : ℂ) • a i z ξ η
  -- Work with the complete original sum, so no positivity of its weights is needed.
  have hcontinuous (z : Z) (ξ : X) (hξ : ξ ≠ 0) :
      ContinuousAt (fun u : Y × (Z × X) ↦ A u.2.1 u.2.2 u.1) (0, z, ξ) := by
    apply tendsto_finsetSum
    intro i _
    have hweight : ContinuousAt (fun u : Y × (Z × X) ↦ (w i u.2.1 : ℂ)) (0, z, ξ) :=
      Complex.continuous_ofReal.continuousAt.comp
        ((hw i).continuousAt.comp (by fun_prop))
    have hterm : ContinuousAt (fun u : Y × (Z × X) ↦ a i u.2.1 u.2.2 u.1)
        (0, z, ξ) := (ha i z ξ hξ).comp
          (f := fun u : Y × (Z × X) ↦ (u.2.1, u.2.2, u.1))
          (x := (0, z, ξ)) (by fun_prop)
    exact hweight.smul hterm
  let K : Set (Z × X) := Set.univ ×ˢ Metric.sphere (0 : X) 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere (0 : X) 1)
  have hnear : ∀ᶠ η in 𝓝 (0 : Y), ∀ zξ ∈ K, (A zξ.1 zξ.2 η).IsInvertible := by
    apply hK.eventually_forall_of_forall_eventually
    intro zξ hzξ
    have hnorm : ‖zξ.2‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hzξ.2
    have hξ : zξ.2 ≠ 0 := by
      intro hzero
      simp [hzero] at hnorm
    have hinvertible : (A zξ.1 zξ.2 0).IsInvertible :=
      ⟨(LinearEquiv.ofBijective (A zξ.1 zξ.2 0).toLinearMap
        (haxis zξ.1 zξ.2 hξ)).toContinuousLinearEquiv, rfl⟩
    exact (hcontinuous zξ.1 zξ.2 hξ).eventually hinvertible.eventually_nhds
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro z ξ η hξ hη
  -- Normalize both covectors by the same positive horizontal length.
  have hlength : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let ξ₀ : X := ‖ξ‖⁻¹ • ξ
  let η₀ : Y := ‖ξ‖⁻¹ • η
  have hξ₀ : ‖ξ₀‖ = 1 := by
    simpa [ξ₀] using norm_smul_inv_norm (𝕜 := ℝ) hξ
  have hη₀ : ‖η₀‖ < δ := by
    rw [show ‖η₀‖ = ‖ξ‖⁻¹ * ‖η‖ by
      simp [η₀, norm_smul]]
    calc
      ‖ξ‖⁻¹ * ‖η‖ < ‖ξ‖⁻¹ * (δ * ‖ξ‖) :=
        mul_lt_mul_of_pos_left hη (inv_pos.mpr hlength)
      _ = δ := by field_simp
  have hnormalized : (A z ξ₀ η₀).IsInvertible := hball
    (by simpa only [Metric.mem_ball, dist_zero_right] using hη₀)
    (z, ξ₀) ⟨Set.mem_univ _, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hξ₀⟩
  have hrecξ : ‖ξ‖ • ξ₀ = ξ := smul_inv_smul₀ hlength.ne' ξ
  have hrecη : ‖ξ‖ • η₀ = η := smul_inv_smul₀ hlength.ne' η
  -- Positive homogeneity scales the whole same-weight sum by one nonzero scalar.
  have hscale : A z ξ η = ((‖ξ‖ ^ m : ℝ) : ℂ) • A z ξ₀ η₀ := by
    calc
      A z ξ η = ∑ i, (w i z : ℂ) • a i z (‖ξ‖ • ξ₀) (‖ξ‖ • η₀) := by
        rw [hrecξ, hrecη]
      _ = ∑ i, ((‖ξ‖ ^ m : ℝ) : ℂ) • ((w i z : ℂ) • a i z ξ₀ η₀) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hhom i z ξ₀ η₀ ‖ξ‖ hlength, smul_comm]
      _ = ((‖ξ‖ ^ m : ℝ) : ℂ) • A z ξ₀ η₀ := by simp only [A, Finset.smul_sum]
  change Function.Bijective (A z ξ η)
  rw [hscale]
  have hscalar : ((‖ξ‖ ^ m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hlength m).ne'
  exact (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hscalar)).comp hnormalized.bijective

end AtiyahSinger
