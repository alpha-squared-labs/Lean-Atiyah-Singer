/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianTensorInverseBound
public import AtiyahSinger.Analysis.FiniteFullSymbolCutoffInverseBound
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation

/-!
# Uniform cutoff inverse estimates on the original varying Hilbert fibers

The finite full-symbol two-cone argument works with a different finite
Hermitian fiber over every parameter. Its cone, radius and inverse coefficient
are chosen from the original uniform bounds before fixing the fiber. This
permits the actual bundle metrics without replacing arbitrary frames by
orthonormal frames or making a continuous choice of isometries.

The finite cutoff factors, their exact metric adjoints and their original
product norm remain unchanged. Actual symbol and active-chart bounds are
still inputs; the theorem does not assert that an arbitrary associated PDO
has these bounds.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct unitInterval

variable {Z X Y ι : Type*} {E₀ E₁ F₀ F₁ : Z → Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [∀ z, NormedAddCommGroup (E₀ z)] [∀ z, InnerProductSpace ℂ (E₀ z)]
  [∀ z, FiniteDimensional ℂ (E₀ z)]
  [∀ z, NormedAddCommGroup (E₁ z)] [∀ z, InnerProductSpace ℂ (E₁ z)]
  [∀ z, FiniteDimensional ℂ (E₁ z)]
  [∀ z, NormedAddCommGroup (F₀ z)] [∀ z, InnerProductSpace ℂ (F₀ z)]
  [∀ z, FiniteDimensional ℂ (F₀ z)]
  [∀ z, NormedAddCommGroup (F₁ z)] [∀ z, InnerProductSpace ℂ (F₁ z)]
  [∀ z, FiniteDimensional ℂ (F₁ z)]
  [Fintype ι]

/-- The same finite full cutoff matrix has a uniform first-order inverse bound. -/
theorem exists_finiteFiberFullSymbolCutoffHomotopy_inverse_bound
    (w v : ι → Z → ℝ)
    (p : ι → unitInterval → ∀ z : Z, X → Y → E₀ z →L[ℂ] E₁ z)
    (q : ι → ∀ z : Z, Y → F₀ z →L[ℂ] F₁ z)
    (r : unitInterval → ∀ z : Z, X → Y → E₀ z →L[ℂ] E₁ z)
    (a : ∀ z : Z, X → E₀ z →L[ℂ] E₁ z)
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
  let b (z : unitInterval × Z) (ξ : X) (η : Y) : E₀ z.2 →L[ℂ] E₁ z.2 :=
    (∑ i, (w i z.2 : ℂ) • p i z.1 z.2 ξ η) + r z.1 z.2 ξ η
  -- The same explicit cone and radius are fixed before choosing any of the varying fibers.
  have hconic : ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ (z : unitInterval × Z) ξ η,
      R ≤ ‖ξ‖ → ‖η‖ ≤ δ * ‖ξ‖ →
        (b z ξ η).IsInvertible ∧ ‖(b z ξ η).inverse‖ ≤ 2 * C / (1 + ‖ξ‖) := by
    let δ := (4 * ((C + 1) * (L + 1)))⁻¹
    let R := R₀ + 4 * ((C + 1) * (N + 1)) + 1
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hR : 0 < R := by dsimp [R]; positivity
    have hCD : C * L * δ ≤ 1 / 4 := by
      have hprod : C * L ≤ (C + 1) * (L + 1) := by nlinarith
      have h := mul_le_mul_of_nonneg_right hprod hδ.le
      have hcancel : ((C + 1) * (L + 1)) * δ = 1 / 4 := by
        dsimp [δ]
        field_simp
      rwa [hcancel] at h
    refine ⟨δ, R, hδ, hR, ?_⟩
    intro z ξ η hlarge hcone
    have hbaseRadius : R₀ ≤ ‖ξ‖ := by
      have hpositive : 0 ≤ 4 * ((C + 1) * (N + 1)) := by positivity
      dsimp only [R] at hlarge
      linarith
    obtain ⟨hinvertible, hinverse⟩ := haxis z.2 ξ hbaseRadius
    let T := b z ξ η
    let e := b z ξ η - a z.2 ξ
    have herr : ‖e‖ ≤ L * ‖η‖ + N := herror z.1 z.2 ξ η hbaseRadius
    -- Both the transverse shift and the bounded order-zero part fit one relative half bound.
    have hconstant : C * N ≤ ‖ξ‖ / 4 := by
      have hprod : C * N ≤ (C + 1) * (N + 1) := by nlinarith
      dsimp only [R] at hlarge
      linarith
    have hscaled : C * (L * ‖η‖ + N) ≤ (1 + ‖ξ‖) / 2 := by
      have htransverse : C * L * ‖η‖ ≤ (1 / 4) * ‖ξ‖ := by
        calc
          C * L * ‖η‖ ≤ C * L * (δ * ‖ξ‖) :=
            mul_le_mul_of_nonneg_left hcone (mul_nonneg hC hL)
          _ = (C * L * δ) * ‖ξ‖ := by ring
          _ ≤ (1 / 4) * ‖ξ‖ := mul_le_mul_of_nonneg_right hCD (norm_nonneg ξ)
      nlinarith
    have hden : 0 < 1 + ‖ξ‖ := by positivity
    have hsmall : ‖(a z.2 ξ).inverse‖ * ‖e‖ ≤ 1 / 2 := by
      calc
        ‖(a z.2 ξ).inverse‖ * ‖e‖ ≤ (C / (1 + ‖ξ‖)) * (L * ‖η‖ + N) :=
          mul_le_mul hinverse herr (norm_nonneg e) (div_nonneg hC hden.le)
        _ = (C * (L * ‖η‖ + N)) / (1 + ‖ξ‖) := by ring
        _ ≤ 1 / 2 := (div_le_iff₀ hden).mpr (by nlinarith [hscaled])
    -- Absorb the actual error using the original axis inverse, on every input vector.
    have hlower (v : E₀ z.2) : ‖v‖ ≤ (2 * ‖(a z.2 ξ).inverse‖) * ‖T v‖ := by
      have hidentity : (a z.2 ξ).inverse (T v - e v) = v := by
        simp only [T, e, sub_apply, sub_sub_cancel, hinvertible.inverse_apply_self]
      have hbound : ‖v‖ ≤ ‖(a z.2 ξ).inverse‖ * ‖T v‖ + (1 / 2) * ‖v‖ := by
        calc
          ‖v‖ = ‖(a z.2 ξ).inverse (T v) - (a z.2 ξ).inverse (e v)‖ := by
            rw [← map_sub, hidentity]
          _ ≤ ‖(a z.2 ξ).inverse (T v)‖ + ‖(a z.2 ξ).inverse (e v)‖ := norm_sub_le _ _
          _ ≤ ‖(a z.2 ξ).inverse‖ * ‖T v‖ +
              ‖(a z.2 ξ).inverse‖ * (‖e‖ * ‖v‖) :=
            add_le_add ((a z.2 ξ).inverse.le_opNorm _)
              (((a z.2 ξ).inverse.le_opNorm _).trans
                (mul_le_mul_of_nonneg_left (e.le_opNorm v) (norm_nonneg _)))
          _ ≤ ‖(a z.2 ξ).inverse‖ * ‖T v‖ + (1 / 2) * ‖v‖ := by
            rw [← mul_assoc]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (norm_nonneg v))
      nlinarith
    have hinjective : Function.Injective T := by
      intro v w hvw
      have h := hlower (v - w)
      rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    -- The same axis equivalence supplies the dimension comparison needed for surjectivity.
    let L := (a z.2 ξ).inverse.comp T
    have hLinjective : Function.Injective L := by
      intro v w hvw
      apply hinjective
      have h := congrArg (a z.2 ξ) hvw
      simpa only [L, ContinuousLinearMap.comp_apply, hinvertible.self_apply_inverse] using h
    have hLsurjective : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinjective
    have hsurjective : Function.Surjective T := by
      intro v
      obtain ⟨w, hw⟩ := hLsurjective ((a z.2 ξ).inverse v)
      refine ⟨w, ?_⟩
      have h := congrArg (a z.2 ξ) hw
      simpa only [L, ContinuousLinearMap.comp_apply, hinvertible.self_apply_inverse] using h
    have hT : T.IsInvertible :=
      ⟨(LinearEquiv.ofBijective T.toLinearMap
        ⟨hinjective, hsurjective⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨hT, ?_⟩
    have hnorm : ‖T.inverse‖ ≤ 2 * ‖(a z.2 ξ).inverse‖ := by
      apply T.inverse.opNorm_le_bound (by positivity)
      intro v
      simpa only [hT.self_apply_inverse] using hlower (T.inverse v)
    exact hnorm.trans (by
      calc
        2 * ‖(a z.2 ξ).inverse‖ ≤ 2 * (C / (1 + ‖ξ‖)) := by gcongr
        _ = 2 * C / (1 + ‖ξ‖) := by ring)
  obtain ⟨δ₁, R₁, hδ₁, hR₁, hinverse⟩ := hconic
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
  let P : E₀ z →L[ℂ] E₁ z :=
    (∑ i, ((w i z * productCutoffHomotopyWeight ε t
      ‖A i z ξ + (t : ℝ) • B i z η‖ ‖V i z η‖ : ℝ) : ℂ) • p i t z ξ η) + r t z ξ η
  let Q : F₀ z →L[ℂ] F₁ z := ∑ i, ((v i z * productCutoffHomotopyWeight ε t
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
        apply congrArg (fun L : E₀ z →L[ℂ] E₁ z ↦ L + r t z ξ η)
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
