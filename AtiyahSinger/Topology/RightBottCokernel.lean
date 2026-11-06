/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RightBottLoop
public import AtiyahSinger.Topology.RightLaurentCokernel

/-!
# The right cokernel of the specified positive Bott loop

Public module ID: M2105.

The Laurent polynomial (1-p)+z*p represents exactly the previously
constructed Bott loop. At shift zero its actual right-module multiplier
cokernel is the right image of the original p. The quotient equivalence is
specified on every positive series by [x] -> p*x(0), retaining its scalar
side, matrix entries and positive orientation.

Sources: Karoubi, K-Theory, III.1.20, pp.119--120. This is the generator
calculation for the actual cokernel inverse, not an abstract choice of a
left inverse. The calculation uses positive Wiener series for the original loop.
Coefficients may be any unital complex Banach algebra. The image is taken
over the opposite ring to express right linearity; no transpose, coefficient
commutation or involution is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RightKTheory

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The actual affine Laurent representative of this same idempotent's positive Bott loop. -/
def bottLaurentLoop (p : IdempotentMatrix A) : LaurentMatrixLoop A :=
  LaurentMatrixLoop.affine (1 - p.matrix) p.matrix (sub_add_cancel 1 p.matrix)
    (fun z ↦ by
      have h : IsUnit ((z : ℂ) • p.matrix + (1 - p.matrix)) :=
        (bottMatrixUnit p z).isUnit
      simpa only [add_comm] using h)

/-- The original Laurent and Bott constructions give the same stable based loop class. -/
theorem bottLaurentLoop_stableClass (p : IdempotentMatrix A) :
    (bottLaurentLoop p).stableClass = bottMatrixLoopClass p := by
  /- Stage 1: evaluate the two coefficients of the affine Laurent polynomial.
  Its value (1-p)+z*p equals z*p+(1-p) by commutativity of addition alone.
  The units therefore agree by equality of their underlying matrices; no
  coefficient products are commuted, and the inverse witness is irrelevant.
  Stage 2: both constructions use the positive Circle.exp(2*pi*t) parameter,
  the same original matrix size and the identity base point. Their finite
  paths and hence their original stable based-homotopy classes coincide. -/
  set_option backward.isDefEq.respectTransparency false in
    have hval (z : Circle) :
        laurentPolynomialCircleValue
          (LaurentPolynomial.C (1 - p.matrix) +
            LaurentPolynomial.C p.matrix * LaurentPolynomial.T 1) z =
          (z : ℂ) • p.matrix + (1 - p.matrix) := by
      rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_single]
      simp [Finsupp.sum_add_index, Finsupp.sum_sub_index, smul_add, smul_sub, add_comm]
    apply congrArg stableMatrixLoopClass
    change (⟨p.size, (bottLaurentLoop p).toFiniteMatrixLoop.loop⟩ : FiniteMatrixLoop A) =
      ⟨p.size, (bottMatrixLoop p).loop⟩
    congr 1
    apply Path.ext
    funext t
    apply Units.ext
    change ((bottLaurentLoop p).invertible
      (Circle.exp (2 * Real.pi * (t : ℝ)))).unit.val = _
    rw [IsUnit.unit_spec]
    exact hval _

/-- KA III.1.20: the unshifted right cokernel is the image of exactly the original p.
The displayed representative formula specifies the quotient isomorphism, including
its right scalar action and constant coefficient; an unrelated model is insufficient. -/
theorem exists_bottLaurentLoop_cokernel_equiv (p : IdempotentMatrix A) :
    ∃ hp : ((bottLaurentLoop p).shift (0 : ℤ)).IsPolynomial,
      ∃ e : (bottLaurentLoop p).RightShiftedCokernel 0 hp ≃ₗ[Aᵐᵒᵖ] p.image,
        ∀ x : PositiveWienerModule A p.size,
          ((e (RightWiener.polynomialCokernelMk
            ((bottLaurentLoop p).shift (0 : ℤ)).polynomial hp x)) : Fin p.size → A) =
              p.matrix.mulVec (x 0) := by
  /- Stage 1: the two Laurent coefficients are 1-p in degree zero and p in
  degree one. Zero shift preserves them. The original complementary
  projections split the right column module into their two right images,
  and their bounded coefficientwise actions preserve positive l1 series.
  Stage 2: the specified multiplier acts by z on p-valued coefficients and
  by identity on the complementary coefficients. The map x -> p*x(0)
  is right-linear and surjects onto the actual image of p, with constant
  series providing preimages. Associativity suffices for linearity.
  Stage 3: if p*x(0)=0, let y(k)=p*x(k+1)+(1-p)*x(k). These same bounded
  projections and the backward shift preserve absolute summability, and
  ((1-p)+z*p)y=x. Conversely the multiplier's constant term is (1-p)y(0),
  annihilated by p. Thus this map's kernel is exactly the original right
  multiplier range. The quotient first-isomorphism theorem supplies e and
  its displayed value on every original series representative. Empty matrix
  size and the zero coefficient ring are allowed throughout. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    -- Keep the exact zero-shift polynomial and its two original coefficients.
    let f : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      ((bottLaurentLoop p).shift (0 : ℤ)).polynomial
    have hf : f = LaurentPolynomial.C (1 - p.matrix) +
        LaurentPolynomial.C p.matrix * LaurentPolynomial.T 1 := by
      change LaurentPolynomial.T 0 *
        (LaurentPolynomial.C (1 - p.matrix) +
          LaurentPolynomial.C p.matrix * LaurentPolynomial.T 1) = _
      rw [LaurentPolynomial.T_zero, one_mul]
    have hcoeff (j : ℤ) : f.coeff j =
        (if 0 = j then 1 - p.matrix else 0) + (if 1 = j then p.matrix else 0) := by
      rw [hf, ← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
        Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    have hp : ((bottLaurentLoop p).shift (0 : ℤ)).IsPolynomial := by
      intro j hj
      change f.coeff j = 0
      rw [hcoeff]
      simp only [show (0 : ℤ) ≠ j by omega, show (1 : ℤ) ≠ j by omega,
        ite_false, add_zero]
    let X := PositiveWienerModule A p.size
    let T : X →ₗ[Aᵐᵒᵖ] X := RightWiener.polynomialMultiplier f hp
    have hTzero (x : X) : T x 0 = (1 - p.matrix).mulVec (x 0) := by
      change RightWiener.polynomialMultiplier f hp x 0 = _
      rw [RightWiener.polynomialMultiplier_coeff]
      simp [hcoeff]
    have hTsucc (x : X) (k : ℕ) : T x (k + 1) =
        (1 - p.matrix).mulVec (x (k + 1)) + p.matrix.mulVec (x k) := by
      change RightWiener.polynomialMultiplier f hp x (k + 1) = _
      rw [RightWiener.polynomialMultiplier_coeff]
      calc
        _ = ∑ j ∈ ({0, 1} : Finset ℕ), (f.coeff (j : ℤ)).mulVec (x (k + 1 - j)) := by
          symm
          apply Finset.sum_subset
          · intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            simp only [Finset.mem_range]
            rcases hj with rfl | rfl <;> omega
          · intro j hj hnot
            simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
            have hj0 : (0 : ℤ) ≠ (j : ℤ) := by omega
            have hj1 : (1 : ℤ) ≠ (j : ℤ) := by omega
            simp only [hcoeff, hj0, hj1, ite_false, add_zero, Matrix.zero_mulVec]
        _ = _ := by simp [hcoeff]
    -- The projection and backward shift are existing bounded Toeplitz maps on ℓ¹.
    have hsingle (d : ℤ) (b : Matrix (Fin p.size) (Fin p.size) A)
        (x : X) (k : ℕ) (h : 0 ≤ (k : ℤ) - d) :
        RightWiener.toeplitz (lp.single 1 d b) x k =
          b.mulVec (x ((k : ℤ) - d).toNat) := by
      change (∑' j : ℕ,
        ((lp.single 1 d b : WienerLoop (Matrix (Fin p.size) (Fin p.size) A))
          ((k : ℤ) - j)).mulVec (x j)) = _
      have heq : (k : ℤ) - ((k : ℤ) - d).toNat = d := by omega
      rw [tsum_eq_single ((k : ℤ) - d).toNat]
      · simp only [lp.coeFn_single, Pi.single_apply]
        rw [ite_eq_left heq]
      · intro j hj
        have hne : (k : ℤ) - j ≠ d := by omega
        simp only [lp.coeFn_single, Pi.single_apply, hne, ite_false, Matrix.zero_mulVec]
    let P : X →ₗ[Aᵐᵒᵖ] X := RightWiener.toeplitz (lp.single 1 0 p.matrix)
    let Q : X →ₗ[Aᵐᵒᵖ] X := RightWiener.toeplitz (lp.single 1 0 (1 - p.matrix))
    let H : X →ₗ[Aᵐᵒᵖ] X :=
      RightWiener.toeplitz (lp.single 1 (-1) (1 : Matrix (Fin p.size) (Fin p.size) A))
    have hP (x : X) (k : ℕ) : P x k = p.matrix.mulVec (x k) := by
      rw [hsingle _ _ _ _ (by omega)]
      simp
    have hQ (x : X) (k : ℕ) : Q x k = (1 - p.matrix).mulVec (x k) := by
      rw [hsingle _ _ _ _ (by omega)]
      simp
    have hH (x : X) (k : ℕ) : H x k = x (k + 1) := by
      rw [hsingle _ _ _ _ (by omega), Matrix.one_mulVec]
      apply congrArg (fun r : ℕ ↦ x r)
      omega
    have hpp : p.matrix * p.matrix = p.matrix := p.mul_self
    have hpq : p.matrix * (1 - p.matrix) = 0 := by
      rw [mul_sub, mul_one, hpp, sub_self]
    have hqp : (1 - p.matrix) * p.matrix = 0 := by
      rw [sub_mul, one_mul, hpp, sub_self]
    have hqq : (1 - p.matrix) * (1 - p.matrix) = 1 - p.matrix := by
      rw [sub_mul, one_mul, hpq, sub_zero]
    -- This actual constant-coefficient map takes values in the original image of p.
    let F : X →ₗ[Aᵐᵒᵖ] p.image :=
      { toFun x := ⟨p.matrix.mulVec (x 0), ⟨x 0, rfl⟩⟩
        map_add' x y := by
          apply Subtype.ext
          change p.matrix.mulVec (x 0 + y 0) =
            p.matrix.mulVec (x 0) + p.matrix.mulVec (y 0)
          exact Matrix.mulVec_add _ _ _
        map_smul' a x := by
          apply Subtype.ext
          change p.matrix.mulVec (a • x 0) = a • p.matrix.mulVec (x 0)
          exact Matrix.mulVec_smul _ _ _ }
    have hker : LinearMap.range T = LinearMap.ker F := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        apply Subtype.ext
        change p.matrix.mulVec (T y 0) = 0
        rw [hTzero, Matrix.mulVec_mulVec, hpq, Matrix.zero_mulVec]
      · intro x hx
        have hx0 : p.matrix.mulVec (x 0) = 0 := congrArg Subtype.val hx
        let y : X := P (H x) + Q x
        have hy (j : ℕ) : y j =
            p.matrix.mulVec (x (j + 1)) + (1 - p.matrix).mulVec (x j) := by
          change P (H x) j + Q x j = _
          rw [hP, hH, hQ]
        refine ⟨y, ?_⟩
        apply lp.ext
        funext j
        cases j with
        | zero =>
          rw [hTzero, hy, Matrix.mulVec_add, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec, hqp, hqq, Matrix.zero_mulVec, zero_add,
            Matrix.sub_mulVec, Matrix.one_mulVec, hx0, sub_zero]
        | succ j =>
          rw [hTsucc, hy, hy]
          simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hqp, hqq, hpp, hpq,
            Matrix.zero_mulVec, zero_add, add_zero]
          rw [← Matrix.add_mulVec, sub_add_cancel, Matrix.one_mulVec]
    have hsurj : Function.Surjective F := by
      rintro ⟨v, hv⟩
      obtain ⟨w, hw⟩ := hv
      refine ⟨lp.single 1 0 w, ?_⟩
      apply Subtype.ext
      change p.matrix.mulVec ((lp.single (E := fun _ : ℕ ↦ Fin p.size → A) 1 0 w) 0) = v
      simpa using hw
    -- The first isomorphism theorem preserves the specified value on every representative.
    let e := (Submodule.quotEquivOfEq (LinearMap.range T) (LinearMap.ker F) hker).trans
      (F.quotKerEquivOfSurjective hsurj)
    refine ⟨hp, e, ?_⟩
    intro x
    rfl

end AtiyahSinger.RightKTheory
