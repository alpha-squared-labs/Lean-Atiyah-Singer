/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolEllipticity

/-!
# Full-symbol inverse estimates in a uniform cone

A first-order inverse estimate on the actual horizontal axis absorbs an error
bounded by the vertical frequency plus a constant. One cone and one radius
work for every specified parameter. The original maps need not be homogeneous.
The input estimates are required only beyond the stated horizontal radius.

For the associated-sphere construction, the frequency derivative bound of each
original order-one chart symbol controls the covector-shift error, and the
actual order-zero symbol remainder supplies the constant term. This theorem
retains those maps and gives a quantitative inverse bound throughout the cone.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {Z X Y E F : Type*}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A uniform linear transverse error preserves the original full-symbol inverse bound in a cone. -/
theorem exists_conic_inverse_bound_of_linear_error
    (a : Z → X → E →L[ℂ] F) (b : Z → X → Y → E →L[ℂ] F)
    (R₀ C D B : ℝ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (ha : ∀ z ξ, R₀ ≤ ‖ξ‖ →
      (a z ξ).IsInvertible ∧ ‖(a z ξ).inverse‖ ≤ C / (1 + ‖ξ‖))
    (herror : ∀ z ξ η, R₀ ≤ ‖ξ‖ → ‖b z ξ η - a z ξ‖ ≤ D * ‖η‖ + B) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ z ξ η, R ≤ ‖ξ‖ → ‖η‖ ≤ δ * ‖ξ‖ →
      (b z ξ η).IsInvertible ∧ ‖(b z ξ η).inverse‖ ≤ 2 * C / (1 + ‖ξ‖) := by
  let δ := (4 * ((C + 1) * (D + 1)))⁻¹
  let R := R₀ + 4 * ((C + 1) * (B + 1)) + 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hCD : C * D * δ ≤ 1 / 4 := by
    have hprod : C * D ≤ (C + 1) * (D + 1) := by nlinarith
    have h := mul_le_mul_of_nonneg_right hprod hδ.le
    have hcancel : ((C + 1) * (D + 1)) * δ = 1 / 4 := by
      dsimp [δ]
      field_simp
    rwa [hcancel] at h
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro z ξ η hlarge hcone
  have hbaseRadius : R₀ ≤ ‖ξ‖ := by
    have hpositive : 0 ≤ 4 * ((C + 1) * (B + 1)) := by positivity
    dsimp only [R] at hlarge
    linarith
  obtain ⟨hinvertible, hinverse⟩ := ha z ξ hbaseRadius
  let T := b z ξ η
  let e := b z ξ η - a z ξ
  have herr : ‖e‖ ≤ D * ‖η‖ + B := herror z ξ η hbaseRadius
  -- Both the transverse shift and the bounded order-zero part fit one relative half bound.
  have hconstant : C * B ≤ ‖ξ‖ / 4 := by
    have hprod : C * B ≤ (C + 1) * (B + 1) := by nlinarith
    dsimp only [R] at hlarge
    linarith
  have hscaled : C * (D * ‖η‖ + B) ≤ (1 + ‖ξ‖) / 2 := by
    have htransverse : C * D * ‖η‖ ≤ (1 / 4) * ‖ξ‖ := by
      calc
        C * D * ‖η‖ ≤ C * D * (δ * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left hcone (mul_nonneg hC hD)
        _ = (C * D * δ) * ‖ξ‖ := by ring
        _ ≤ (1 / 4) * ‖ξ‖ := mul_le_mul_of_nonneg_right hCD (norm_nonneg ξ)
    nlinarith
  have hden : 0 < 1 + ‖ξ‖ := by positivity
  have hsmall : ‖(a z ξ).inverse‖ * ‖e‖ ≤ 1 / 2 := by
    calc
      ‖(a z ξ).inverse‖ * ‖e‖ ≤ (C / (1 + ‖ξ‖)) * (D * ‖η‖ + B) :=
        mul_le_mul hinverse herr (norm_nonneg e) (div_nonneg hC hden.le)
      _ = (C * (D * ‖η‖ + B)) / (1 + ‖ξ‖) := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hden).mpr (by nlinarith [hscaled])
  -- Absorb the actual error using the original axis inverse, on every input vector.
  have hlower (v : E) : ‖v‖ ≤ (2 * ‖(a z ξ).inverse‖) * ‖T v‖ := by
    have hidentity : (a z ξ).inverse (T v - e v) = v := by
      simp only [T, e, sub_apply, sub_sub_cancel, hinvertible.inverse_apply_self]
    have hbound : ‖v‖ ≤ ‖(a z ξ).inverse‖ * ‖T v‖ + (1 / 2) * ‖v‖ := by
      calc
        ‖v‖ = ‖(a z ξ).inverse (T v) - (a z ξ).inverse (e v)‖ := by
          rw [← map_sub, hidentity]
        _ ≤ ‖(a z ξ).inverse (T v)‖ + ‖(a z ξ).inverse (e v)‖ := norm_sub_le _ _
        _ ≤ ‖(a z ξ).inverse‖ * ‖T v‖ +
            ‖(a z ξ).inverse‖ * (‖e‖ * ‖v‖) :=
          add_le_add ((a z ξ).inverse.le_opNorm _)
            (((a z ξ).inverse.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (e.le_opNorm v) (norm_nonneg _)))
        _ ≤ ‖(a z ξ).inverse‖ * ‖T v‖ + (1 / 2) * ‖v‖ := by
          rw [← mul_assoc]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (norm_nonneg v))
    nlinarith
  have hinjective : Function.Injective T := by
    intro v w hvw
    have h := hlower (v - w)
    rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  -- The same axis equivalence supplies the dimension comparison needed for surjectivity.
  let L := (a z ξ).inverse.comp T
  have hLinjective : Function.Injective L := by
    intro v w hvw
    apply hinjective
    have h := congrArg (a z ξ) hvw
    simpa only [L, ContinuousLinearMap.comp_apply, hinvertible.self_apply_inverse] using h
  have hLsurjective : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinjective
  have hsurjective : Function.Surjective T := by
    intro v
    obtain ⟨w, hw⟩ := hLsurjective ((a z ξ).inverse v)
    refine ⟨w, ?_⟩
    have h := congrArg (a z ξ) hw
    simpa only [L, ContinuousLinearMap.comp_apply, hinvertible.self_apply_inverse] using h
  have hT : T.IsInvertible :=
    ⟨(LinearEquiv.ofBijective T.toLinearMap ⟨hinjective, hsurjective⟩).toContinuousLinearEquiv, rfl⟩
  refine ⟨hT, ?_⟩
  have hnorm : ‖T.inverse‖ ≤ 2 * ‖(a z ξ).inverse‖ := by
    apply T.inverse.opNorm_le_bound (by positivity)
    intro v
    simpa only [hT.self_apply_inverse] using hlower (T.inverse v)
  exact hnorm.trans (by
    calc
      2 * ‖(a z ξ).inverse‖ ≤ 2 * (C / (1 + ‖ξ‖)) := by gcongr
      _ = 2 * C / (1 + ‖ξ‖) := by ring)

end AtiyahSinger
