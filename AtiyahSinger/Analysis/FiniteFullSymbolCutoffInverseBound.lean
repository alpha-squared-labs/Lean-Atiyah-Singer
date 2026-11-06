/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianTensorInverseBound
public import AtiyahSinger.Analysis.FullSymbolConicPerturbation
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation

/-!
# Quantitative ellipticity for the actual finite cutoff factors

The two complementary cone argument retains both specified finite full-symbol
sums and their actual adjoints. On the horizontal cone the transverse error is
absorbed by the specified axis inverse; on its complement the actual vertical
sum saturates. Quantitative inverse bounds for either factor then control the
original Hermitian tensor matrix in the existing product norm. One exterior,
cutoff range and first-order inverse constant work for the whole homotopy.

This is the analytic estimate needed for full-symbol ellipticity. Applying it
to an atlas still requires the actual chart block bounds, finite symbol sums
and their source estimates; eventual bijectivity alone does not supply these.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct unitInterval

variable {Z X Y E₀ E₁ F₀ F₁ ι : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [Fintype ι]

/-- The same finite full cutoff matrix has a uniform first-order inverse bound. -/
theorem exists_finiteFullSymbolCutoffHomotopy_inverse_bound
    (w v : ι → Z → ℝ)
    (p : ι → unitInterval → Z → X → Y → E₀ →L[ℂ] E₁)
    (q : ι → Z → Y → F₀ →L[ℂ] F₁)
    (r : unitInterval → Z → X → Y → E₀ →L[ℂ] E₁)
    (a : Z → X → E₀ →L[ℂ] E₁)
    (A : ι → Z → X →L[ℝ] X) (B : ι → Z → Y →L[ℝ] X)
    (V : ι → Z → Y →L[ℝ] Y)
    (D : ℝ) (hD : 1 ≤ D)
    (hgeom : ∀ i z, w i z ≠ 0 ∨ v i z ≠ 0 →
      ‖A i z‖ ≤ D ∧ (∀ ξ, ‖ξ‖ ≤ D * ‖A i z ξ‖) ∧ ‖B i z‖ ≤ D ∧
        ‖V i z‖ ≤ D ∧ ∀ η, ‖η‖ ≤ D * ‖V i z η‖)
    (R₀ C L N : ℝ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (haxis : ∀ z ξ, R₀ ≤ ‖ξ‖ →
      (a z ξ).IsInvertible ∧ ‖(a z ξ).inverse‖ ≤ C / (1 + ‖ξ‖))
    (herror : ∀ t z ξ η, R₀ ≤ ‖ξ‖ →
      ‖((∑ i, (w i z : ℂ) • p i t z ξ η) + r t z ξ η) - a z ξ‖ ≤ L * ‖η‖ + N)
    (S CQ : ℝ) (hS : 0 ≤ S) (hCQ : 0 ≤ CQ)
    (hq : ∀ z η, S ≤ ‖η‖ →
      (∑ i, (v i z : ℂ) • q i z η).IsInvertible ∧
        ‖(∑ i, (v i z : ℂ) • q i z η).inverse‖ ≤ CQ / (1 + ‖η‖)) :
    ∃ ε₀ R K : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R ∧ 0 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (t : unitInterval) z ξ η, R ≤ ‖ξ‖ + ‖η‖ →
        let P := (∑ i, ((w i z * productCutoffHomotopyWeight ε t
          ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
        let Q := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
          ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) • q i z η
        let T := (reciprocalTensorSymbol P.toLinearMap P.toLinearMap.adjoint
          Q.toLinearMap Q.toLinearMap.adjoint).toContinuousLinearMap
        T.IsInvertible ∧ ‖T.inverse‖ ≤ K / (1 + ‖ξ‖ + ‖η‖) := by
  classical
  let b (z : unitInterval × Z) (ξ : X) (η : Y) : E₀ →L[ℂ] E₁ :=
    (∑ i, (w i z.2 : ℂ) • p i z.1 z.2 ξ η) + r z.1 z.2 ξ η
  -- First obtain inverse stability for the original full horizontal sum.
  obtain ⟨δ₁, R₁, hδ₁, hR₁, hinverse⟩ := exists_conic_inverse_bound_of_linear_error
    (fun z : unitInterval × Z ↦ a z.2) b R₀ C L N hR₀ hC hL hN
    (fun z ξ hξ ↦ haxis z.2 ξ hξ) (fun z ξ η hξ ↦ herror z.1 z.2 ξ η hξ)
  -- Bounds are needed only on the original union of active horizontal and vertical patches.
  let Active := { iz : ι × Z // w iz.1 iz.2 ≠ 0 ∨ v iz.1 iz.2 ≠ 0 }
  obtain ⟨δ, ε₀, hδ, hδle, hε₀, hε₀one, hsaturate⟩ :=
    exists_productCutoffHomotopyWeight_eq_one_in_split_cones
      (fun iz : Active ↦ A iz.val.1 iz.val.2)
      (fun iz : Active ↦ B iz.val.1 iz.val.2)
      (fun iz : Active ↦ V iz.val.1 iz.val.2) D δ₁ hD hδ₁
      (fun iz ↦ (hgeom iz.val.1 iz.val.2 iz.property).1)
      (fun iz ↦ (hgeom iz.val.1 iz.val.2 iz.property).2.1)
      (fun iz ↦ (hgeom iz.val.1 iz.val.2 iz.property).2.2.1)
      (fun iz ↦ (hgeom iz.val.1 iz.val.2 iz.property).2.2.2.1)
      (fun iz ↦ (hgeom iz.val.1 iz.val.2 iz.property).2.2.2.2)
  let R := (1 + δ) * R₁ + (1 + δ⁻¹) * S + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let K₀ := 2 * C * (1 + δ) + CQ * (1 + δ⁻¹)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨ε₀, R, 2 * K₀, hε₀, hε₀one, hR, by positivity, ?_⟩
  intro ε hε hεle t z ξ η hlarge
  dsimp only
  let P : E₀ →L[ℂ] E₁ :=
    (∑ i, ((w i z * productCutoffHomotopyWeight ε t
      ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
  let Q : F₀ →L[ℂ] F₁ := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
    ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) • q i z η
  have hden : 0 < 1 + ‖ξ‖ + ‖η‖ := by positivity
  have hfactor : (P.IsInvertible ∧ ‖P.inverse‖ ≤ K₀ / (1 + ‖ξ‖ + ‖η‖)) ∨
      (Q.IsInvertible ∧ ‖Q.inverse‖ ≤ K₀ / (1 + ‖ξ‖ + ‖η‖)) := by
    by_cases hcone : ‖η‖ ≤ δ * ‖ξ‖
    · left
      have hξ : R₁ ≤ ‖ξ‖ := by
        have hpos : 0 ≤ (1 + δ⁻¹) * S := by positivity
        dsimp only [R] at hlarge
        nlinarith
      have hP : P = b (t, z) ξ η := by
        apply congrArg (fun L : E₀ →L[ℂ] E₁ ↦ L + r t z ξ η)
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : w i z = 0
        · simp [hi]
        · have hc := (hsaturate ε hε hεle t (⟨(i, z), Or.inl hi⟩ : Active) ξ η).1 hcone
          change productCutoffHomotopyWeight ε t
            ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ = 1 at hc
          rw [hc, mul_one]
      rw [hP]
      obtain ⟨hb, hbnd⟩ := hinverse (t, z) ξ η hξ
        (hcone.trans (mul_le_mul_of_nonneg_right hδle (norm_nonneg ξ)))
      refine ⟨hb, hbnd.trans ?_⟩
      have hdenle : 1 + ‖ξ‖ + ‖η‖ ≤ (1 + δ) * (1 + ‖ξ‖) := by nlinarith
      calc
        2 * C / (1 + ‖ξ‖) ≤ (2 * C * (1 + δ)) / (1 + ‖ξ‖ + ‖η‖) := by
          apply (div_le_div_iff₀ (by positivity) hden).mpr
          have hmul := mul_le_mul_of_nonneg_left hdenle (show 0 ≤ 2 * C by positivity)
          nlinarith
        _ ≤ K₀ / (1 + ‖ξ‖ + ‖η‖) := by
          apply div_le_div_of_nonneg_right _ hden.le
          dsimp only [K₀]
          exact le_add_of_nonneg_right (by positivity)
    · right
      have hcone' : δ * ‖ξ‖ ≤ ‖η‖ := (lt_of_not_ge hcone).le
      have hξ : ‖ξ‖ ≤ δ⁻¹ * ‖η‖ := by
        have h := mul_le_mul_of_nonneg_left hcone' (inv_pos.mpr hδ).le
        simpa only [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] using h
      have hη : S ≤ ‖η‖ := by
        have hpos : 0 ≤ (1 + δ) * R₁ := by positivity
        dsimp only [R] at hlarge
        by_contra! hnot
        have hs := mul_lt_mul_of_pos_left hnot (show 0 < 1 + δ⁻¹ by positivity)
        nlinarith
      have hQ : Q = ∑ i, (v i z : ℂ) • q i z η := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : v i z = 0
        · simp [hi]
        · have hc := (hsaturate ε hε hεle t (⟨(i, z), Or.inr hi⟩ : Active) ξ η).2 hcone'
          change productCutoffHomotopyWeight ε t
            ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ = 1 at hc
          rw [hc, mul_one]
      rw [hQ]
      obtain ⟨hb, hbnd⟩ := hq z η hη
      refine ⟨hb, hbnd.trans ?_⟩
      have hdenle : 1 + ‖ξ‖ + ‖η‖ ≤ (1 + δ⁻¹) * (1 + ‖η‖) := by
        have hδinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
        nlinarith
      calc
        CQ / (1 + ‖η‖) ≤ (CQ * (1 + δ⁻¹)) / (1 + ‖ξ‖ + ‖η‖) := by
          apply (div_le_div_iff₀ (by positivity) hden).mpr
          have hmul := mul_le_mul_of_nonneg_left hdenle hCQ
          nlinarith
        _ ≤ K₀ / (1 + ‖ξ‖ + ‖η‖) := by
          apply div_le_div_of_nonneg_right _ hden.le
          dsimp only [K₀]
          exact le_add_of_nonneg_left (by positivity)
  -- Quantitative Hermitian energy uses the same finite factors and their actual adjoints.
  have hmatrix := reciprocalTensorSymbol_isInvertible_of_inverse_bound P Q
    (K₀ / (1 + ‖ξ‖ + ‖η‖)) (div_nonneg hK₀ hden.le) hfactor
  simpa only [P, Q, mul_div_assoc] using hmatrix

end AtiyahSinger
