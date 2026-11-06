/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Analysis.FiniteHomogeneousConicInvertibility

/-!
# One exterior for the full Hermitian split homotopy

Interpolate each specified horizontal covector shift linearly to zero, keeping
the vertical covector and the original real partition weights fixed. The full
horizontal map need only recover its original elliptic homogeneous symbol at
large frequency. The vertical full map is assumed invertible at large vertical
frequency. One radius works for the complete homotopy and the original maps.

The reverse horizontal entry is the sum with exactly the same real weights
and the prescribed adjoints. This statement supplies the pointwise uniform
exterior for the uncut split homotopy. Native bundle continuity, the actual
chart identities and frequency-cutoff saturation are separate inputs to the
associated-sphere K-class comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct Topology unitInterval

variable {Z X Y E₀ E₁ F₀ F₁ ι : Type*} [TopologicalSpace Z] [CompactSpace Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [Fintype ι]

/-- The actual full maps and their same-weight adjoints remain invertible on one exterior. -/
theorem exists_splitHermitianSymbol_bijective_at_infinity
    (L : ι → Z → Y →L[ℝ] X) (w : ι → Z → ℝ)
    (hL : ∀ i, Continuous (L i)) (hw : ∀ i, Continuous (w i))
    (hsum : ∀ z, ∑ i, w i z = 1)
    (p₀ : Z → X → E₀ →L[ℂ] E₁) (m : ℝ)
    (hp₀ : ∀ z ξ, ξ ≠ 0 → ContinuousAt (fun u : Z × X ↦ p₀ u.1 u.2) (z, ξ))
    (hhom : ∀ z ξ s, 0 < s → p₀ z (s • ξ) = ((s ^ m : ℝ) : ℂ) • p₀ z ξ)
    (helliptic : ∀ z ξ, ξ ≠ 0 → Function.Bijective (p₀ z ξ))
    (p : Z → X → E₀ →ₗ[ℂ] E₁) (pi : Z → X → E₁ →ₗ[ℂ] E₀)
    (hpi : ∀ z ξ, pi z ξ = (p z ξ).adjoint)
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (hrecover : ∀ z ξ, R₀ ≤ ‖ξ‖ → p z ξ = (p₀ z ξ).toLinearMap)
    (q : Z → Y → F₀ →ₗ[ℂ] F₁) (qi : Z → Y → F₁ →ₗ[ℂ] F₀)
    (hqi : ∀ z η, qi z η = (q z η).adjoint)
    (S₀ : ℝ) (hS₀ : 0 ≤ S₀)
    (hq : ∀ z η, S₀ ≤ ‖η‖ → Function.Bijective (q z η)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (t : unitInterval) z ξ η, R ≤ ‖ξ‖ + ‖η‖ →
      Function.Bijective (reciprocalTensorSymbol
        (∑ i, (w i z : ℂ) • p z (ξ + (t : ℝ) • L i z η))
        (∑ i, (w i z : ℂ) • pi z (ξ + (t : ℝ) • L i z η)) (q z η) (qi z η)) := by
  classical
  -- Include the complete closed time interval in the compact parameter space.
  let a (i : ι) (z : unitInterval × Z) (ξ : X) (η : Y) : E₀ →L[ℂ] E₁ :=
    p₀ z.2 (ξ + (z.1 : ℝ) • L i z.2 η)
  let weights (i : ι) (z : unitInterval × Z) : ℝ := w i z.2
  have hweights (i : ι) : Continuous (weights i) := (hw i).comp continuous_snd
  have hcontinuous (i : ι) (z : unitInterval × Z) (ξ : X) (hξ : ξ ≠ 0) :
      ContinuousAt (fun u : (unitInterval × Z) × X × Y ↦ a i u.1 u.2.1 u.2.2)
        (z, ξ, 0) := by
    have hinner : Continuous (fun u : (unitInterval × Z) × X × Y ↦
        (u.1.2, u.2.1 + (u.1.1 : ℝ) • L i u.1.2 u.2.2)) := by
      fun_prop
    have hbase : ContinuousAt (fun u : Z × X ↦ p₀ u.1 u.2)
        (z.2, ξ + (z.1 : ℝ) • L i z.2 0) := by
      simpa only [map_zero, smul_zero, add_zero] using hp₀ z.2 ξ hξ
    exact hbase.comp
        (f := fun u : (unitInterval × Z) × X × Y ↦
          (u.1.2, u.2.1 + (u.1.1 : ℝ) • L i u.1.2 u.2.2))
        (x := (z, ξ, 0)) hinner.continuousAt
  have hscale (i : ι) (z : unitInterval × Z) (ξ : X) (η : Y) (s : ℝ) (hs : 0 < s) :
      a i z (s • ξ) (s • η) = ((s ^ m : ℝ) : ℂ) • a i z ξ η := by
    have harg : s • ξ + (z.1 : ℝ) • L i z.2 (s • η) =
        s • (ξ + (z.1 : ℝ) • L i z.2 η) := by
      rw [map_smul]
      module
    dsimp only [a]
    rw [harg, hhom z.2 _ s hs]
  have haxis (z : unitInterval × Z) (ξ : X) (hξ : ξ ≠ 0) :
      Function.Bijective (∑ i, (weights i z : ℂ) • a i z ξ 0 : E₀ →L[ℂ] E₁) := by
    simpa only [a, weights, map_zero, smul_zero, add_zero, ← Finset.sum_smul,
      ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul] using helliptic z.2 ξ hξ
  obtain ⟨δ, hδ, hcone⟩ := exists_bijective_weightedHomogeneousSum_in_cone
    a weights m hweights hcontinuous hscale haxis
  -- Compactness bounds all original shifts, without choosing replacement splittings.
  have hnormContinuous : Continuous (fun z : Z ↦ ∑ i, ‖L i z‖) :=
    continuous_finsetSum _ (fun i _ ↦ (hL i).norm)
  obtain ⟨C₀, hC₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    hnormContinuous.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (i : ι) (z : Z) : ‖L i z‖ ≤ C := by
    have hsumNorm : ‖L i z‖ ≤ ∑ j, ‖L j z‖ :=
      Finset.single_le_sum (fun j _ ↦ norm_nonneg (L j z)) (Finset.mem_univ i)
    have htotal : ∑ j, ‖L j z‖ ≤ C₀ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
        (fun j _ ↦ norm_nonneg (L j z)))] using hC₀ z (Set.mem_univ z)
    exact hsumNorm.trans (htotal.trans (le_max_left _ _))
  let S := S₀ + 1
  let R := R₀ + C * S + S + S / δ + 1
  have hS : 0 < S := by dsimp [S]; linarith
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro t z ξ η hlarge
  have hforward : Function.Bijective (∑ i, (w i z : ℂ) •
      p z (ξ + (t : ℝ) • L i z η) : E₀ →ₗ[ℂ] E₁) ∨ Function.Bijective (q z η) := by
    by_cases hηlarge : S ≤ ‖η‖
    · right
      apply hq
      exact (show S₀ ≤ S by dsimp [S]; linarith).trans hηlarge
    · left
      have hηsmall : ‖η‖ < S := lt_of_not_ge hηlarge
      have hpositive : 0 < ‖ξ‖ := by
        have hnonneg : 0 ≤ C * S + S / δ := by positivity
        dsimp only [R] at hlarge
        linarith
      have hratio : ‖η‖ < δ * ‖ξ‖ := by
        have hξlarge : S / δ < ‖ξ‖ := by
          have hCS : 0 ≤ C * S := mul_nonneg hC hS.le
          dsimp only [R] at hlarge
          linarith
        have hSδ : S < ‖ξ‖ * δ := (div_lt_iff₀ hδ).mp hξlarge
        nlinarith
      have hrecoverAll (i : ι) : p z (ξ + (t : ℝ) • L i z η) =
          (p₀ z (ξ + (t : ℝ) • L i z η)).toLinearMap := by
        apply hrecover
        have hshift : ‖(t : ℝ) • L i z η‖ ≤ C * S := by
          calc
            ‖(t : ℝ) • L i z η‖ = (t : ℝ) * ‖L i z η‖ :=
              by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
            _ ≤ 1 * (‖L i z‖ * ‖η‖) :=
              mul_le_mul t.property.2 ((L i z).le_opNorm η) (norm_nonneg _) zero_le_one
            _ ≤ C * S := by
              rw [one_mul]
              exact mul_le_mul (hbound i z) hηsmall.le (norm_nonneg η) hC
        have htriangle : ‖ξ‖ ≤ ‖ξ + (t : ℝ) • L i z η‖ + ‖(t : ℝ) • L i z η‖ := by
          simpa only [add_sub_cancel_right] using
            norm_sub_le (ξ + (t : ℝ) • L i z η) ((t : ℝ) • L i z η)
        have hnonneg : 0 ≤ S / δ := by positivity
        dsimp only [R] at hlarge
        linarith
      have hhomogeneous := hcone (t, z) ξ η (norm_pos_iff.mp hpositive) hratio
      convert hhomogeneous using 1
      ext v
      simp only [a, weights, LinearMap.sum_apply, LinearMap.smul_apply,
        sum_apply, smul_apply, hrecoverAll,
        ContinuousLinearMap.coe_coe]
  -- Both reverse entries are exactly the adjoints of the same original forward entries.
  have hadjoint : (∑ i, (w i z : ℂ) • pi z (ξ + (t : ℝ) • L i z η)) =
      (∑ i, (w i z : ℂ) • p z (ξ + (t : ℝ) • L i z η)).adjoint := by
    simp only [map_sum, map_smulₛₗ, Complex.conj_ofReal, hpi]
  rw [hadjoint, hqi]
  simpa only [weightedGradedTensorSymbol, Complex.ofReal_one, one_smul] using
    weightedGradedTensorSymbol_bijective
      (∑ i, (w i z : ℂ) • p z (ξ + (t : ℝ) • L i z η)) (q z η) 1 1
      (hforward.imp (fun h ↦ ⟨one_ne_zero, h⟩) (fun h ↦ ⟨one_ne_zero, h⟩))

end AtiyahSinger
