/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Analysis.FullSymbolConicPerturbation

/-!
# Affine interpolation of the actual two tensor factors

Two full horizontal factors are close to the same elliptic axis by a linear
transverse error, including its bounded lower-order term. The cutoff family
recovers the second factor in a sufficiently small horizontal cone and the
original vertical factor outside that cone. The affine interpolation of the
two original pairs then has one invertible exterior for the whole interval.

This is the analytic input for the associated-sphere supported homotopy.
Continuity comes from the original endpoint bundle maps, separately. No
homogeneous replacement or global change of covector is required here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct unitInterval

variable {Z X Y E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]

/-- Two-cone recovery controls the affine path of the original Hermitian tensor factors. -/
theorem exists_affineTensorHomotopy_bijective_at_infinity
    (a : Z → X → E₀ →L[ℂ] E₁)
    (p₀ p₁ : Z → X → Y → E₀ →L[ℂ] E₁)
    (p : ℝ → Z → X → Y → E₀ →L[ℂ] E₁)
    (q₀ : Z → Y → F₀ →ₗ[ℂ] F₁)
    (q : ℝ → Z → X → Y → F₀ →ₗ[ℂ] F₁)
    (R₀ C D B S : ℝ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (ha : ∀ z ξ, R₀ ≤ ‖ξ‖ →
      (a z ξ).IsInvertible ∧ ‖(a z ξ).inverse‖ ≤ C / (1 + ‖ξ‖))
    (hp₀ : ∀ z ξ η, R₀ ≤ ‖ξ‖ → ‖p₀ z ξ η - a z ξ‖ ≤ D * ‖η‖ + B)
    (hp₁ : ∀ z ξ η, R₀ ≤ ‖ξ‖ → ‖p₁ z ξ η - a z ξ‖ ≤ D * ‖η‖ + B)
    (hq₀ : ∀ z η, S ≤ ‖η‖ → Function.Bijective (q₀ z η))
    (hcut : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ δ ε₀ : ℝ,
      0 < δ ∧ δ ≤ δ₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ξ η,
          (‖η‖ ≤ δ * ‖ξ‖ → p ε z ξ η = p₁ z ξ η) ∧
          (δ * ‖ξ‖ ≤ ‖η‖ → q ε z ξ η = q₀ z η)) :
    ∃ ε₀ R : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (t : unitInterval) z ξ η,
        R ≤ ‖ξ‖ + ‖η‖ →
          let P := (1 - (t : ℂ)) • p₀ z ξ η + (t : ℂ) • p ε z ξ η
          let Q := (1 - (t : ℂ)) • q₀ z η + (t : ℂ) • q ε z ξ η
          Function.Bijective (reciprocalTensorSymbol
            P.toLinearMap P.toLinearMap.adjoint Q Q.adjoint) := by
  let b (z : unitInterval × Z) (ξ : X) (η : Y) : E₀ →L[ℂ] E₁ :=
    (1 - (z.1 : ℂ)) • p₀ z.2 ξ η + (z.1 : ℂ) • p₁ z.2 ξ η
  -- Convexity retains the same error bound for both full endpoints, including the constant.
  have herr (z : unitInterval × Z) (ξ : X) (η : Y) (hξ : R₀ ≤ ‖ξ‖) :
      ‖b z ξ η - a z.2 ξ‖ ≤ D * ‖η‖ + B := by
    have heq : b z ξ η - a z.2 ξ =
        (1 - (z.1 : ℂ)) • (p₀ z.2 ξ η - a z.2 ξ) +
          (z.1 : ℂ) • (p₁ z.2 ξ η - a z.2 ξ) := by
      dsimp only [b]
      module
    have ht : ‖(z.1 : ℂ)‖ = (z.1 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
    have hs : ‖1 - (z.1 : ℂ)‖ = 1 - (z.1 : ℝ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr z.1.property.2)]
    rw [heq]
    calc
      _ ≤ ‖(1 - (z.1 : ℂ)) • (p₀ z.2 ξ η - a z.2 ξ)‖ +
          ‖(z.1 : ℂ) • (p₁ z.2 ξ η - a z.2 ξ)‖ := norm_add_le _ _
      _ = (1 - (z.1 : ℝ)) * ‖p₀ z.2 ξ η - a z.2 ξ‖ +
          (z.1 : ℝ) * ‖p₁ z.2 ξ η - a z.2 ξ‖ := by rw [norm_smul, norm_smul, hs, ht]
      _ ≤ (1 - (z.1 : ℝ)) * (D * ‖η‖ + B) + (z.1 : ℝ) * (D * ‖η‖ + B) :=
        add_le_add (mul_le_mul_of_nonneg_left (hp₀ z.2 ξ η hξ)
          (sub_nonneg.mpr z.1.property.2))
            (mul_le_mul_of_nonneg_left (hp₁ z.2 ξ η hξ) z.1.property.1)
      _ = D * ‖η‖ + B := by ring
  obtain ⟨δ₁, R₁, hδ₁, hR₁, hinverse⟩ := exists_conic_inverse_bound_of_linear_error
    (fun z : unitInterval × Z ↦ a z.2) b R₀ C D B hR₀ hC hD hB
      (fun z ξ hξ ↦ ha z.2 ξ hξ) herr
  -- Choose the cutoff only after the uniform perturbation cone has been fixed.
  obtain ⟨δ, ε₀, hδ, hδle, hε₀, hε₀one, hsaturate⟩ := hcut δ₁ hδ₁
  let R := (1 + δ) * R₁ + (1 + δ⁻¹) * S + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨ε₀, R, hε₀, hε₀one, hR, ?_⟩
  intro ε hε hεle t z ξ η hlarge P Q
  have hfactor : Function.Bijective P ∨ Function.Bijective Q := by
    by_cases hcone : ‖η‖ ≤ δ * ‖ξ‖
    · left
      have hξ : R₁ ≤ ‖ξ‖ := by
        have hpos : 0 ≤ (1 + δ⁻¹) * S := by positivity
        dsimp only [R] at hlarge
        nlinarith
      have hP : P = b (t, z) ξ η := by
        dsimp only [P, b]
        rw [(hsaturate ε hε hεle z ξ η).1 hcone]
      rw [hP]
      exact (hinverse (t, z) ξ η hξ
        (hcone.trans (mul_le_mul_of_nonneg_right hδle (norm_nonneg ξ)))).1.bijective
    · right
      have hcone' : δ * ‖ξ‖ ≤ ‖η‖ := (lt_of_not_ge hcone).le
      have hη : S ≤ ‖η‖ := by
        have hξ : ‖ξ‖ ≤ δ⁻¹ * ‖η‖ := (le_inv_mul_iff₀ hδ).mpr hcone'
        have hpos : 0 ≤ (1 + δ) * R₁ := by positivity
        dsimp only [R] at hlarge
        by_contra! hnot
        have h := mul_lt_mul_of_pos_left hnot (show 0 < 1 + δ⁻¹ by positivity)
        nlinarith
      have hQ : Q = q₀ z η := by
        dsimp only [Q]
        rw [(hsaturate ε hε hεle z ξ η).2 hcone']
        module
      rw [hQ]
      exact hq₀ z η hη
  -- Both reverse entries are the adjoints of these same interpolated factors.
  simpa only [weightedGradedTensorSymbol, Complex.ofReal_one, one_smul] using
    weightedGradedTensorSymbol_bijective P.toLinearMap Q 1 1
      (hfactor.imp (fun h ↦ ⟨one_ne_zero, h⟩) (fun h ↦ ⟨one_ne_zero, h⟩))

end AtiyahSinger
