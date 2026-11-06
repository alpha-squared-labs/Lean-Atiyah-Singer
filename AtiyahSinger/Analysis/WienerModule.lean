/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.WienerLoop
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Positive Wiener modules and Toeplitz operators

Public module ID: M1054.

The module `A⟨z⟩ⁿ` is the actual space of absolutely summable sequences of vectors.
Multiplication by a bilateral matrix series followed by positive projection is the
Toeplitz operator given by its coefficient formula. The finite free submodule of
polynomials of degree less than `d` is embedded by single-coordinate sequences.

Sources: Karoubi, K-Theory, III.1.17--1.18, pp.117--118. We use commutative complex
Banach coefficients, so matrix multiplication on column vectors is left A-linear.
The book's noncommutative version requires a consistent right-module formulation
and is not claimed here. Matrix coefficients carry the submultiplicative infinity
operator norm; vectors have the existing finite-product supremum norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator

/-- The standard positive Wiener module of ℓ¹ vector coefficients indexed by ℕ. -/
abbrev PositiveWienerModule (A : Type u) [NormedAddCommGroup A] (n : ℕ) : Type u :=
  lp (fun _ : ℕ ↦ Fin n → A) 1

variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
variable {n : ℕ}

local instance : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- The actual positive convolution coefficients are absolutely summable. -/
theorem positiveWienerToeplitz_memℓp (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (x : PositiveWienerModule A n) :
    Memℓp (fun k : ℕ ↦ ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j)) 1 := by
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

/-- The actual coefficient formula is additive and A-linear.
Commutativity of A is used for the left scalar action on column vectors. -/
theorem positiveWienerToeplitz_linear (g : WienerLoop (Matrix (Fin n) (Fin n) A)) :
    (∀ (x y : PositiveWienerModule A n) (k : ℕ),
      (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec ((x + y) j)) =
        (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j)) +
          ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (y j)) ∧
    (∀ (a : A) (x : PositiveWienerModule A n) (k : ℕ),
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
  constructor
  · intro x y k
    change (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j + y j)) = _
    simp_rw [Matrix.mulVec_add]
    exact (hsum x k).tsum_add (hsum y k)
  · intro a x k
    -- Commutativity makes left scalar multiplication commute with each matrix entry.
    change (∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (a • x j)) = _
    simp_rw [Matrix.mulVec_smul]
    exact (hsum x k).tsum_const_smul a

/-- The standard Toeplitz operator P₊ M_g i on vector coefficients of nonnegative degree. -/
def positiveWienerToeplitz (g : WienerLoop (Matrix (Fin n) (Fin n) A)) :
    PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n where
  toFun x :=
    ⟨fun k ↦ ∑' j : ℕ, (g ((k : ℤ) - j)).mulVec (x j),
      positiveWienerToeplitz_memℓp g x⟩
  map_add' x y := by
    apply lp.ext
    funext k
    exact (positiveWienerToeplitz_linear g).1 x y k
  map_smul' a x := by
    apply lp.ext
    funext k
    exact (positiveWienerToeplitz_linear g).2 a x k

/-- The Toeplitz operator is bounded by the ℓ¹ norm of its matrix coefficients. -/
theorem positiveWienerToeplitz_norm_le (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (x : PositiveWienerModule A n) :
    ‖positiveWienerToeplitz g x‖ ≤ ‖g‖ * ‖x‖ := by
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
  have hcoeff (k : ℕ) : ‖(positiveWienerToeplitz g x) k‖ ≤
      ∑' j : ℕ, ‖g ((k : ℤ) - j)‖ * ‖x j‖ := by
    have hnorm : Summable (fun j : ℕ ↦ ‖(g ((k : ℤ) - j)).mulVec (x j)‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun j ↦ Matrix.linfty_opNorm_mulVec (g ((k : ℤ) - j)) (x j)) (hmajor.prod_factor k)
    exact (norm_tsum_le_tsum_norm hnorm).trans
      (hnorm.tsum_le_tsum (fun j ↦ Matrix.linfty_opNorm_mulVec (g ((k : ℤ) - j)) (x j))
        (hmajor.prod_factor k))
  have hy : Summable (fun k : ℕ ↦ ‖(positiveWienerToeplitz g x) k‖) := by
    simpa using (positiveWienerToeplitz g x).2.summable
  -- Positive outputs form a subset of all bilateral outputs, so restriction only reduces the bound.
  calc
    ‖positiveWienerToeplitz g x‖ = ∑' k : ℕ, ‖(positiveWienerToeplitz g x) k‖ := by
      simpa using lp.norm_eq_tsum_rpow (by simp) (positiveWienerToeplitz g x)
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

/-- The same coefficient operator, bundled with its boundedness estimate. -/
def positiveWienerToeplitzContinuous (g : WienerLoop (Matrix (Fin n) (Fin n) A)) :
    PositiveWienerModule A n →L[A] PositiveWienerModule A n :=
  (positiveWienerToeplitz g).mkContinuous ‖g‖ (positiveWienerToeplitz_norm_le g)

/-- The canonical embedding of the first d vector coefficients as a finite polynomial. -/
def lowPolynomialEmbedding (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    (n d : ℕ) : (Fin d → Fin n → A) →ₗ[A] PositiveWienerModule A n :=
  ∑ j : Fin d, (lp.lsingle 1 (j : ℕ)).comp (LinearMap.proj j)

end AtiyahSinger

