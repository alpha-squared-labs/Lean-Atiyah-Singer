/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.WienerModule
public import Mathlib.Algebra.Module.Opposite

/-!
# Right modules of positive Wiener series

Public module ID: M0936.

UL04 and KL02: retain the existing positive sequence carrier, with its actual
nonnegative coefficients and original norm. A matrix over a noncommutative
algebra acts on columns on the left and is linear for scalar multiplication
on the right. Lean expresses this right A-module as a left Aᵐᵒᵖ-module.
Neither the matrices nor their products are transposed or reversed.

The Toeplitz action is the same convergent coefficient convolution as in the
commutative construction. The grouped certificate below supplies its actual
summability and linearity laws, without introducing another series space.

Sources: Karoubi, K-Theory, II.3.10, p.74 (right free modules), and
III.1.17--1.18, pp.117--119 (positive series and multiplier cokernels).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator

namespace RightWiener

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  {n : ℕ}

local instance : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- Summability and right linearity of the actual positive convolution formula.
This grouped certificate supplies the fields of one standard Toeplitz operator. -/
theorem toeplitz_properties (g : WienerLoop (Matrix (Fin n) (Fin n) A)) :
    (∀ x : PositiveWienerModule A n,
      Memℓp (fun k : ℕ ↦ ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j)) 1) ∧
    (∀ (x y : PositiveWienerModule A n) (k : ℕ),
      (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec ((x + y) j)) =
        (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j)) +
          ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (y j)) ∧
    (∀ (a : Aᵐᵒᵖ) (x : PositiveWienerModule A n) (k : ℕ),
      (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec ((a • x) j)) =
        a • ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j)) := by
  -- At each output coefficient, the fixed matrix norm bounds an absolutely convergent series.
  have hsum (x : PositiveWienerModule A n) (k : ℕ) :
      Summable (fun j : ℕ ↦ (g ((k : ℤ) - j)).mulVec (x j)) := by
    have hx : Summable (fun j : ℕ ↦ ‖x j‖) := by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
    apply (hx.mul_left ‖g‖).of_norm_bounded
    intro j
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by simp) g _) (norm_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · intro x
    -- Embed the two nonnegative indices in the full bilateral-by-positive product.
    have hg : Summable (fun i : ℤ ↦ ‖g i‖) := by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using g.2.summable (by simp)
    have hx : Summable (fun j : ℕ ↦ ‖x j‖) := by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
    have hfull : Summable (fun p : ℤ × ℕ ↦ ‖g p.1‖ * ‖x p.2‖) :=
      Summable.mul_of_nonneg (f := fun i : ℤ ↦ ‖g i‖) (g := fun j : ℕ ↦ ‖x j‖)
        hg hx (fun i ↦ norm_nonneg (g i)) (fun j ↦ norm_nonneg (x j))
    have hinj : Function.Injective (fun p : ℕ × ℕ ↦ ((p.1 : ℤ) - p.2, p.2)) := by
      intro p q hpq
      have h₁ := congrArg Prod.fst hpq
      have h₂ := congrArg Prod.snd hpq
      dsimp at h₁ h₂
      exact Prod.ext (by omega) h₂
    have hmajor : Summable (fun p : ℕ × ℕ ↦ ‖g ((p.1 : ℤ) - p.2)‖ * ‖x p.2‖) :=
      hfull.comp_injective (i := fun p : ℕ × ℕ ↦ ((p.1 : ℤ) - p.2, p.2)) hinj
    -- The matrix operator norm controls each vector term, before summing in either index.
    have hnorm : Summable (fun p : ℕ × ℕ ↦
        ‖(g ((p.1 : ℤ) - p.2)).mulVec (x p.2)‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun p ↦ Matrix.linfty_opNorm_mulVec (g ((p.1 : ℤ) - p.2)) (x p.2)) hmajor
    apply memℓp_gen
    simp only [ENNReal.toReal_one, Real.rpow_one]
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hnorm.prod
    intro k
    exact norm_tsum_le_tsum_norm (hnorm.prod_factor k)
  · intro x y k
    change (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j + y j)) = _
    simp_rw [Matrix.mulVec_add]
    exact (hsum x k).tsum_add (hsum y k)
  · intro a x k
    -- The right scalar stays on the right of every original matrix-vector product.
    change (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (a • x j)) = _
    simp_rw [Matrix.mulVec_smul]
    exact (hsum x k).tsum_const_smul a

/-- The standard positive Toeplitz operator, linear for the original right scalar action. -/
def toeplitz (g : WienerLoop (Matrix (Fin n) (Fin n) A)) :
    PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n where
  toFun x :=
    ⟨fun k ↦ ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j),
      (toeplitz_properties g).1 x⟩
  map_add' x y := by
    apply lp.ext
    funext k
    exact (toeplitz_properties g).2.1 x y k
  map_smul' a x := by
    apply lp.ext
    funext k
    exact (toeplitz_properties g).2.2 a x k

/-- The right-linear Toeplitz operator obeys the usual convolution norm bound. -/
theorem toeplitz_norm_le (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (x : PositiveWienerModule A n) : ‖toeplitz g x‖ ≤ ‖g‖ * ‖x‖ := by
  -- Embed the two nonnegative indices in the full bilateral-by-positive product.
  have hg : Summable (fun i : ℤ ↦ ‖g i‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using g.2.summable (by simp)
  have hx : Summable (fun j : ℕ ↦ ‖x j‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
  have hfull : Summable (fun p : ℤ × ℕ ↦ ‖g p.1‖ * ‖x p.2‖) :=
    Summable.mul_of_nonneg (f := fun i : ℤ ↦ ‖g i‖) (g := fun j : ℕ ↦ ‖x j‖)
      hg hx (fun i ↦ norm_nonneg (g i)) (fun j ↦ norm_nonneg (x j))
  have hinj : Function.Injective (fun p : ℕ × ℕ ↦ ((p.1 : ℤ) - p.2, p.2)) := by
    intro p q hpq
    have h₁ := congrArg Prod.fst hpq
    have h₂ := congrArg Prod.snd hpq
    dsimp at h₁ h₂
    exact Prod.ext (by omega) h₂
  have hmajor : Summable (fun p : ℕ × ℕ ↦ ‖g ((p.1 : ℤ) - p.2)‖ * ‖x p.2‖) :=
    hfull.comp_injective (i := fun p : ℕ × ℕ ↦ ((p.1 : ℤ) - p.2, p.2)) hinj
  -- Bound each convergent output coefficient by its scalar majorant.
  have hcoeff (k : ℕ) : ‖(toeplitz g x) k‖ ≤
      ∑' j : ℕ, ‖g ((k : ℤ) - j)‖ * ‖x j‖ := by
    have hnorm : Summable (fun j : ℕ ↦ ‖(g ((k : ℤ) - j)).mulVec (x j)‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun j ↦ Matrix.linfty_opNorm_mulVec (g ((k : ℤ) - j)) (x j)) (hmajor.prod_factor k)
    exact (norm_tsum_le_tsum_norm hnorm).trans
      (hnorm.tsum_le_tsum (fun j ↦ Matrix.linfty_opNorm_mulVec (g ((k : ℤ) - j)) (x j))
        (hmajor.prod_factor k))
  have hy : Summable (fun k : ℕ ↦ ‖(toeplitz g x) k‖) := by
    simpa using (toeplitz g x).2.summable
  -- Positive outputs form a subset of all bilateral outputs, so restriction only reduces the bound.
  calc
    ‖toeplitz g x‖ = ∑' k : ℕ, ‖(toeplitz g x) k‖ := by
      simpa using lp.norm_eq_tsum_rpow (by simp) (toeplitz g x)
    _ ≤ ∑' k : ℕ, ∑' j : ℕ, ‖g ((k : ℤ) - j)‖ * ‖x j‖ :=
      hy.tsum_le_tsum hcoeff hmajor.prod
    _ = ∑' p : ℕ × ℕ, ‖g ((p.1 : ℤ) - p.2)‖ * ‖x p.2‖ := hmajor.tsum_prod.symm
    _ ≤ ∑' p : ℤ × ℕ, ‖g p.1‖ * ‖x p.2‖ :=
      Summable.tsum_le_tsum_of_inj (fun p : ℕ × ℕ ↦ ((p.1 : ℤ) - p.2, p.2)) hinj
        (fun p _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun _ ↦ le_rfl) hmajor hfull
    _ = (∑' i : ℤ, ‖g i‖) * ∑' j : ℕ, ‖x j‖ := (hg.tsum_mul_tsum hx hfull).symm
    _ = ‖g‖ * ‖x‖ := by
      congr 1
      · simpa using (lp.norm_eq_tsum_rpow (by simp) g).symm
      · simpa using (lp.norm_eq_tsum_rpow (by simp) x).symm

/-- The same actual Toeplitz action bundled as a continuous right-linear map. -/
def toeplitzContinuous (g : WienerLoop (Matrix (Fin n) (Fin n) A)) :
    PositiveWienerModule A n →L[Aᵐᵒᵖ] PositiveWienerModule A n :=
  (toeplitz g).mkContinuous ‖g‖ (toeplitz_norm_le g)

/-- Include the first d coefficient vectors as an actual finite positive series. -/
def lowPolynomialEmbedding (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    (n d : ℕ) : (Fin d → Fin n → A) →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
  ∑ j : Fin d, (lp.lsingle 1 (j : ℕ)).comp (LinearMap.proj j)

end RightWiener

end AtiyahSinger
