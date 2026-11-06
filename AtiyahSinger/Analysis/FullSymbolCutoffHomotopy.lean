/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Analysis.FiniteAtlasProductCutoff
public import AtiyahSinger.Analysis.FullSymbolConicPerturbation

/-!
# One exterior for a finite full-symbol cutoff homotopy

The given full symbols are evaluated at their actual base and mixed cotangent
blocks, with the original real weights and SG cutoffs. Uniform frequency
Lipschitz bounds control the mixed shifts; a bounded remainder is retained.
The actual weighted horizontal axis has a first-order inverse estimate.

For large vertical frequency the original vertical map gives graded
invertibility. For bounded vertical frequency, sufficiently large horizontal
frequency saturates every active cutoff and makes the shifted full sum
invertible. Thus one exterior works throughout the closed homotopy interval,
even for signed weights. No homogeneous recovery, nonnegative partition,
vanishing mixed block, or replacement of the given maps is used.

The hypotheses are uniform bounds on the specified finite chart data. Actual
bundle continuity, identification of both endpoints, and compactness in the
native cotangent bundle are separate parts of the K-class construction.
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

/-- Actual shifted full symbols, signed weights and cutoffs admit one Hermitian exterior. -/
theorem exists_fullSymbolCutoffHomotopy_bijective_at_infinity
    (w : ι → Z → ℝ) (p : ι → Z → X → E₀ →L[ℂ] E₁)
    (A : ι → Z → X →L[ℝ] X) (B : ι → Z → Y →L[ℝ] X)
    (V : ι → Z → Y →L[ℝ] Y)
    (r : unitInterval → Z → X → Y → E₀ →L[ℂ] E₁)
    (C R₀ : ℝ) (hC : 1 ≤ C) (hR₀ : 0 ≤ R₀)
    (hweights : ∀ z, ∑ i, |w i z| ≤ C)
    (hA : ∀ i z ξ, w i z ≠ 0 → ‖ξ‖ ≤ C * ‖A i z ξ‖)
    (hB : ∀ i z, w i z ≠ 0 → ‖B i z‖ ≤ C)
    (hV : ∀ i z, w i z ≠ 0 → ‖V i z‖ ≤ C)
    (hp : ∀ i z ξ ζ, w i z ≠ 0 → ‖p i z ζ - p i z ξ‖ ≤ C * ‖ζ - ξ‖)
    (hr : ∀ t z ξ η, ‖r t z ξ η‖ ≤ C)
    (haxis : ∀ z ξ, R₀ ≤ ‖ξ‖ →
      (∑ i, (w i z : ℂ) • p i z (A i z ξ)).IsInvertible ∧
        ‖(∑ i, (w i z : ℂ) • p i z (A i z ξ)).inverse‖ ≤ C / (1 + ‖ξ‖))
    (q : Z → Y → F₀ →ₗ[ℂ] F₁) (S₀ : ℝ) (hS₀ : 0 ≤ S₀)
    (hq : ∀ z η, S₀ ≤ ‖η‖ → Function.Bijective (q z η))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (t : unitInterval) z ξ η, R ≤ ‖ξ‖ + ‖η‖ →
      let P := (∑ i, ((w i z * productCutoffHomotopyWeight ε t
        ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) •
          p i z (A i z ξ + (t : ℝ) • B i z η)) + r t z ξ η
      Function.Bijective (reciprocalTensorSymbol
        P.toLinearMap P.toLinearMap.adjoint (q z η) (q z η).adjoint) := by
  classical
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let a (z : unitInterval × Z) (ξ : X) : E₀ →L[ℂ] E₁ :=
    ∑ i, (w i z.2 : ℂ) • p i z.2 (A i z.2 ξ)
  let b (z : unitInterval × Z) (ξ : X) (η : Y) : E₀ →L[ℂ] E₁ :=
    (∑ i, (w i z.2 : ℂ) • p i z.2 (A i z.2 ξ + (z.1 : ℝ) • B i z.2 η)) +
      r z.1 z.2 ξ η
  -- The full shifted sum differs from its original axis by a linear transverse error.
  have hshift (i : ι) (t : unitInterval) (z : Z) (η : Y) (hi : w i z ≠ 0) :
      ‖(t : ℝ) • B i z η‖ ≤ C * ‖η‖ := by
    calc
      ‖(t : ℝ) • B i z η‖ = (t : ℝ) * ‖B i z η‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      _ ≤ 1 * (‖B i z‖ * ‖η‖) :=
        mul_le_mul t.property.2 ((B i z).le_opNorm η) (norm_nonneg _) zero_le_one
      _ ≤ C * ‖η‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (hB i z hi) (norm_nonneg η)
  have herror (z : unitInterval × Z) (ξ : X) (η : Y) :
      ‖b z ξ η - a z ξ‖ ≤ C ^ 3 * ‖η‖ + C := by
    have hterm (i : ι) :
        ‖(w i z.2 : ℂ) •
          (p i z.2 (A i z.2 ξ + (z.1 : ℝ) • B i z.2 η) - p i z.2 (A i z.2 ξ))‖ ≤
          |w i z.2| * (C * (C * ‖η‖)) := by
      by_cases hi : w i z.2 = 0
      · simp [hi]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ C * ‖(z.1 : ℝ) • B i z.2 η‖ := by
          simpa only [add_sub_cancel_left] using
            hp i z.2 (A i z.2 ξ) (A i z.2 ξ + (z.1 : ℝ) • B i z.2 η) hi
        _ ≤ C * (C * ‖η‖) :=
          mul_le_mul_of_nonneg_left (hshift i z.1 z.2 η hi) hCpos.le
    have heq : b z ξ η - a z ξ =
        (∑ i, (w i z.2 : ℂ) •
          (p i z.2 (A i z.2 ξ + (z.1 : ℝ) • B i z.2 η) - p i z.2 (A i z.2 ξ))) +
            r z.1 z.2 ξ η := by
      dsimp only [a, b]
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib]
      abel
    rw [heq]
    calc
      _ ≤ ‖∑ i, (w i z.2 : ℂ) •
          (p i z.2 (A i z.2 ξ + (z.1 : ℝ) • B i z.2 η) - p i z.2 (A i z.2 ξ))‖ +
            ‖r z.1 z.2 ξ η‖ := norm_add_le _ _
      _ ≤ (∑ i, |w i z.2| * (C * (C * ‖η‖))) + C :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ hterm i)))
          (hr z.1 z.2 ξ η)
      _ ≤ C ^ 3 * ‖η‖ + C := by
        rw [← Finset.sum_mul]
        have h := mul_le_mul_of_nonneg_right (hweights z.2)
          (show 0 ≤ C * (C * ‖η‖) by positivity)
        nlinarith
  obtain ⟨δ, R₁, hδ, hR₁, hcone⟩ := exists_conic_inverse_bound_of_linear_error
    a b R₀ C (C ^ 3) C hR₀ hCpos.le (by positivity) hCpos.le
    (fun z ξ hξ ↦ haxis z.2 ξ hξ) (fun z ξ η _ ↦ herror z ξ η)
  -- Bounded vertical frequency eventually saturates all active cutoffs at every time.
  let S := S₀ + 1
  let R := R₁ + S / δ + C * ((C + ε * C) * S) + S + 1
  have hS : 0 < S := by dsimp [S]; linarith
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro t z ξ η hlarge
  dsimp only
  let P : E₀ →L[ℂ] E₁ :=
    (∑ i, ((w i z * productCutoffHomotopyWeight ε t
      ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) •
        p i z (A i z ξ + (t : ℝ) • B i z η)) + r t z ξ η
  have hfactor : Function.Bijective P ∨ Function.Bijective (q z η) := by
    by_cases hη : S ≤ ‖η‖
    · exact Or.inr (hq z η ((show S₀ ≤ S by dsimp [S]; linarith).trans hη))
    · left
      have hηsmall : ‖η‖ < S := lt_of_not_ge hη
      have hgeom : 0 ≤ C * ((C + ε * C) * S) := by positivity
      have hξ : R₁ ≤ ‖ξ‖ := by
        have hratio : 0 ≤ S / δ := by positivity
        dsimp only [R] at hlarge
        linarith
      have hratio : ‖η‖ ≤ δ * ‖ξ‖ := by
        have hξδ : S / δ < ‖ξ‖ := by
          dsimp only [R] at hlarge
          linarith
        have h := (div_lt_iff₀ hδ).mp hξδ
        nlinarith
      have hcut (i : ι) (hi : w i z ≠ 0) :
          productCutoffHomotopyWeight ε t
            ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ = 1 := by
        have hbase := hA i z ξ hi
        have htri : ‖A i z ξ‖ ≤
            ‖A i z ξ + (t : ℝ) • B i z η‖ + ‖(t : ℝ) • B i z η‖ := by
          simpa only [add_sub_cancel_right] using
            norm_sub_le (A i z ξ + (t : ℝ) • B i z η) ((t : ℝ) • B i z η)
        have hshift' : ‖(t : ℝ) • B i z η‖ ≤ C * S :=
          (hshift i t z η hi).trans (mul_le_mul_of_nonneg_left hηsmall.le hCpos.le)
        have hvertical : ‖V i z η‖ ≤ C * S :=
          ((V i z).le_opNorm η).trans
            (mul_le_mul (hV i z hi) hηsmall.le (norm_nonneg η) hCpos.le)
        have hξlarge : C * ((C + ε * C) * S) < ‖ξ‖ := by
          have hratio' : 0 ≤ S / δ := by positivity
          dsimp only [R] at hlarge
          linarith
        have hdom : ε * ‖V i z η‖ ≤ ‖A i z ξ + (t : ℝ) • B i z η‖ := by
          have hv := mul_le_mul_of_nonneg_left hvertical hε.le
          nlinarith
        have hc := productFrequencyCutoff_eq_one_of_mul_le ε
          ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ hε
          (norm_nonneg _) (norm_nonneg _) hdom
        simp only [productCutoffHomotopyWeight, hc]
        ring
      have hP : P = b (t, z) ξ η := by
        apply congrArg (fun L : E₀ →L[ℂ] E₁ ↦ L + r t z ξ η)
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : w i z = 0
        · simp [hi]
        · rw [hcut i hi, mul_one]
      rw [hP]
      exact (hcone (t, z) ξ η hξ hratio).1.bijective
  -- The reverse horizontal entry is the adjoint of the same full sum and remainder.
  change Function.Bijective
    (reciprocalTensorSymbol P.toLinearMap P.toLinearMap.adjoint (q z η) (q z η).adjoint)
  simpa only [weightedGradedTensorSymbol, Complex.ofReal_one, one_smul] using
    weightedGradedTensorSymbol_bijective P.toLinearMap (q z η) 1 1
      (hfactor.imp (fun h ↦ ⟨one_ne_zero, h⟩) (fun h ↦ ⟨one_ne_zero, h⟩))

end AtiyahSinger
