/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolConicPerturbation
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation

/-!
# A common exterior for both finite full-symbol cutoffs

Both original factor sums carry their own real partition and SG frequency
cutoff. The horizontal uncut sum has a linear transverse error relative to
the specified quantitatively elliptic axis. The vertical uncut sum is
invertible at large vertical frequency. All reverse entries are the adjoints
of these exact full sums.

Uniform bounds for the same active mixed cotangent blocks yield one small
cutoff range and one exterior for the entire homotopy. Inside the refined
horizontal cone every active horizontal weight saturates; outside it every
active vertical weight saturates. Thus signed partitions cannot cancel the
factor used in either region. No homogeneous representative is substituted.

Actual full-symbol error estimates and active-chart bounds are hypotheses,
to be provided for the original atlas. Native continuity, endpoint identities
and compact-support K-class transport are not asserted here.
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

/-- Both actual finite SG cutoff sums remain Hermitian invertible on one common exterior. -/
theorem exists_finiteFullSymbolCutoffHomotopy_bijective_at_infinity
    (w v : ι → Z → ℝ)
    (p : ι → unitInterval → Z → X → Y → E₀ →L[ℂ] E₁)
    (q : ι → Z → Y → F₀ →ₗ[ℂ] F₁)
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
    (S : ℝ) (hS : 0 ≤ S)
    (hq : ∀ z η, S ≤ ‖η‖ →
      Function.Bijective (∑ i, (v i z : ℂ) • q i z η : F₀ →ₗ[ℂ] F₁)) :
    ∃ ε₀ R : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (t : unitInterval) z ξ η, R ≤ ‖ξ‖ + ‖η‖ →
        let P := (∑ i, ((w i z * productCutoffHomotopyWeight ε t
          ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
        let Q := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
          ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) • q i z η
        Function.Bijective (reciprocalTensorSymbol
          P.toLinearMap P.toLinearMap.adjoint Q Q.adjoint) := by
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
  refine ⟨ε₀, R, hε₀, hε₀one, hR, ?_⟩
  intro ε hε hεle t z ξ η hlarge
  dsimp only
  let P : E₀ →L[ℂ] E₁ :=
    (∑ i, ((w i z * productCutoffHomotopyWeight ε t
      ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
  let Q : F₀ →ₗ[ℂ] F₁ := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
    ‖V i z η‖ ‖A i z ξ + (t : ℝ) • B i z η‖ : ℝ) : ℂ) • q i z η
  have hfactor : Function.Bijective P ∨ Function.Bijective Q := by
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
      exact (hinverse (t, z) ξ η hξ
        (hcone.trans (mul_le_mul_of_nonneg_right hδle (norm_nonneg ξ)))).1.bijective
    · right
      have hcone' : δ * ‖ξ‖ ≤ ‖η‖ := (lt_of_not_ge hcone).le
      have hη : S ≤ ‖η‖ := by
        have hξ : ‖ξ‖ ≤ δ⁻¹ * ‖η‖ := by
          have h := mul_le_mul_of_nonneg_left hcone' (inv_pos.mpr hδ).le
          simpa only [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] using h
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
      exact hq z η hη
  -- Both reverse blocks use the exact same cutoff sums, preserving the Hermitian argument.
  change Function.Bijective (reciprocalTensorSymbol P.toLinearMap P.toLinearMap.adjoint Q Q.adjoint)
  simpa only [weightedGradedTensorSymbol, Complex.ofReal_one, one_smul] using
    weightedGradedTensorSymbol_bijective P.toLinearMap Q 1 1
      (hfactor.imp (fun h ↦ ⟨one_ne_zero, h⟩) (fun h ↦ ⟨one_ne_zero, h⟩))

end AtiyahSinger
