/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PolynomialCokernel
public import AtiyahSinger.Topology.BottSurjectivity

/-!
# Cokernels of polynomial shifts of Laurent matrix loops

Public module ID: M1928.

Karoubi III.1.18–1.20, pp.118–120: the actual positive Wiener multiplier of
z^k σ has a finite projective cokernel, and increasing k by l adds a free module
of rank n*l. For the specified Bott loop p*z + (1-p), the unshifted cokernel
is the image of exactly the same idempotent p.

The finite-projective assertion uses the repaired finite-bandwidth projection
argument from `AtiyahSinger.Analysis.PolynomialCokernel`, rather than the
unsupported one-sided factorization in the printed proof of Lemma 1.18. Thus
every nonnegative shift that makes the Laurent polynomial nonnegative is allowed;
no additional inverse-truncation condition on k is needed.

Coefficients are commutative complex Banach algebras to match the current K₀
model. The original book allows noncommutative coefficients. Matrix coefficients
retain their multiplication order, and the inverse loop need not be a polynomial.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

namespace LaurentMatrixLoop

/-- KA III.1.18: the actual quotient by multiplication by the polynomial z^k σ.
The supplied certificate ensures that this multiplier preserves positive powers. -/
abbrev ShiftedCokernel (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) : Type u :=
  PolynomialCokernel (p.shift (k : ℤ)).polynomial hk

/-- The repaired polynomial-cokernel theorem applies to the specified shift. -/
theorem shiftedCokernel_finite (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) : Module.Finite A (p.ShiftedCokernel k hk) := by
  /- Unfold the actual shifted quotient. Apply polynomialCokernel_finite to
  the polynomial (p.shift k).polynomial, the given nonnegative-support certificate
  hk, and the circle-invertibility certificate of that same shifted loop. -/
  exact polynomialCokernel_finite (p.shift (k : ℤ)).polynomial hk
    (p.shift (k : ℤ)).invertible

/-- The specified quotient is projective, without replacing it by an arbitrary module. -/
theorem shiftedCokernel_projective (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    Module.Projective A (p.ShiftedCokernel k hk) := by
  /- Unfold the same quotient as in the finite-generation statement. Apply
  polynomialCokernel_projective with exactly its polynomial, hk and the shifted
  loop's invertibility certificate; no replacement projective carrier is chosen. -/
  exact polynomialCokernel_projective (p.shift (k : ℤ)).polynomial hk
    (p.shift (k : ℤ)).invertible

/-- KA III.1.18: a further positive shift adds exactly n*l free generators.
The positivity certificate and linear equivalence refer to the same shifted polynomial. -/
theorem nonempty_shiftedCokernel_add_equiv (p : LaurentMatrixLoop A) (k l : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    ∃ hkl : (p.shift ((k + l : ℕ) : ℤ)).IsPolynomial,
      Nonempty (p.ShiftedCokernel (k + l) hkl ≃ₗ[A]
        p.ShiftedCokernel k hk × (Fin (p.size * l) → A)) := by
  /- Stage 1: shifting by l ≥ 0 preserves the original polynomial's nonnegative
  support. Positive and negative monomial Toeplitz maps give the forward shift Z
  and backward shift H on the same positive Wiener module, with HZ = id.
  Stage 2: let C take the first l vector coefficients and J include those finite
  coefficients as a series. Then ZH + JC = id, CZ = 0, CJ = id and HJ = 0.
  The shifted multiplier U is ZT for the original multiplier T.
  Stage 3: x ↦ ([Hx], Cx) is surjective onto coker(T) × A^(n*l), with kernel
  exactly range(U). Apply the quotient first-isomorphism theorem and reindex
  the same low coefficients by Fin(size*l). This includes l=0 and size=0. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let : CompleteSpace (Matrix (Fin p.size) (Fin p.size) A) :=
      inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → A))
    have monomial_coeff {n : ℕ} (d : ℤ) (x : PositiveWienerModule A n) (k : ℕ) :
        positiveWienerToeplitz
            (lp.single 1 d (1 : Matrix (Fin n) (Fin n) A)) x k =
          if 0 ≤ (k : ℤ) - d then x ((k : ℤ) - d).toNat else 0 := by
      classical
      change (∑' j : ℕ,
        ((lp.single 1 d (1 : Matrix (Fin n) (Fin n) A) :
          WienerLoop (Matrix (Fin n) (Fin n) A)) ((k : ℤ) - j)).mulVec (x j)) = _
      by_cases h : 0 ≤ (k : ℤ) - d
      · rw [ite_eq_left h]
        have heq : d = (k : ℤ) - ((k : ℤ) - d).toNat := by omega
        rw [tsum_eq_single ((k : ℤ) - d).toNat]
        · simp only [lp.coeFn_single, Pi.single_apply]
          rw [ite_eq_left heq.symm, Matrix.one_mulVec]
        · intro j hj
          have hne : d ≠ (k : ℤ) - j := by omega
          simp only [lp.coeFn_single, Pi.single_apply, Ne.symm hne, ite_false, Matrix.zero_mulVec]
      · rw [ite_eq_right h]
        calc
          _ = ∑' j : ℕ, (0 : Fin n → A) := by
            congr 1
            funext j
            have hne : d ≠ (k : ℤ) - j := by omega
            simp only [lp.coeFn_single, Pi.single_apply, Ne.symm hne, ite_false, Matrix.zero_mulVec]
          _ = 0 := by simp
    -- Identify the same shifted polynomial, coefficient by coefficient.
    let f : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      (p.shift (k : ℤ)).polynomial
    let f' : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      (p.shift ((k + l : ℕ) : ℤ)).polynomial
    have hpositive (j : ℤ) (hj : j < 0) : f.coeff j = 0 := hk j hj
    have hcoeff (j : ℤ) :
        f'.coeff j = f.coeff (j - l) := by
      change (LaurentPolynomial.T ((k + l : ℕ) : ℤ) * p.polynomial).coeff j =
        (LaurentPolynomial.T (k : ℤ) * p.polynomial).coeff (j - l)
      simp only [LaurentPolynomial.T,
        AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      congr 1
      omega
    have hkl : (p.shift ((k + l : ℕ) : ℤ)).IsPolynomial := by
      intro j hj
      change f'.coeff j = 0
      rw [hcoeff]
      exact hpositive _ (by omega)
    refine ⟨hkl, ?_⟩
    let X := PositiveWienerModule A p.size
    let T : X →ₗ[A] X :=
      polynomialMultiplier f hk
    let U : X →ₗ[A] X :=
      polynomialMultiplier f' hkl
    let Z : X →ₗ[A] X :=
      positiveWienerToeplitz (lp.single 1 (l : ℤ) (1 : Matrix (Fin p.size) (Fin p.size) A))
    let H : X →ₗ[A] X :=
      positiveWienerToeplitz (lp.single 1 (-(l : ℤ)) (1 : Matrix (Fin p.size) (Fin p.size) A))
    have hZ (x : X) (j : ℕ) : Z x j = if l ≤ j then x (j - l) else 0 := by
      rw [monomial_coeff]
      have hcast : ((j : ℤ) - (l : ℤ)).toNat = j - l := by omega
      have hle : (0 ≤ (j : ℤ) - l) ↔ l ≤ j := by omega
      simp only [hle, hcast]
    have hH (x : X) (j : ℕ) : H x j = x (j + l) := by
      rw [monomial_coeff, ite_eq_left (show 0 ≤ (j : ℤ) - -(l : ℤ) by omega)]
      apply congrArg (fun r : ℕ ↦ x r)
      omega
    -- Positive and negative monomials give genuine maps of the original ℓ¹ carrier.
    have hHZ (x : X) : H (Z x) = x := by
      apply lp.ext
      funext j
      rw [hH, hZ, ite_eq_left (by omega)]
      apply congrArg (fun r : ℕ ↦ x r)
      omega
    have hU (x : X) : U x = Z (T x) := by
      apply lp.ext
      funext i
      change (∑' j : ℕ,
        (laurentPolynomialWiener f' ((i : ℤ) - j)).mulVec (x j)) = Z (T x) i
      rw [hZ]
      split_ifs with hli
      · change _ = ∑' j : ℕ,
          (laurentPolynomialWiener f (((i - l : ℕ) : ℤ) - j)).mulVec (x j)
        apply tsum_congr
        intro j
        rw [laurentPolynomialWiener_coeff, hcoeff, laurentPolynomialWiener_coeff]
        have heq : (i : ℤ) - j - l = ((i - l : ℕ) : ℤ) - j := by omega
        rw [heq]
      · calc
          _ = ∑' j : ℕ, (0 : Fin p.size → A) := by
            apply tsum_congr
            intro j
            rw [laurentPolynomialWiener_coeff, hcoeff, hpositive _ (by omega),
              Matrix.zero_mulVec]
          _ = 0 := by simp
    let C : X →ₗ[A] (Fin l → Fin p.size → A) :=
      LinearMap.pi fun j : Fin l ↦ lp.evalₗ (fun _ : ℕ ↦ Fin p.size → A) 1 (j : ℕ)
    let J : (Fin l → Fin p.size → A) →ₗ[A] X :=
      { toFun v := ∑ j : Fin l,
          lp.single (E := fun _ : ℕ ↦ Fin p.size → A) 1 (j : ℕ) (v j)
        map_add' v w := by
          simp only [Pi.add_apply, lp.single_add, Finset.sum_add_distrib]
        map_smul' a v := by
          simp only [Pi.smul_apply, lp.single_smul, Finset.smul_sum, RingHom.id_apply] }
    have hJapply (v : Fin l → Fin p.size → A) :
        J v = ∑ i : Fin l, lp.single (E := fun _ : ℕ ↦ Fin p.size → A) 1 (i : ℕ) (v i) := by
      rfl
    have hJlow (v : Fin l → Fin p.size → A) (j : Fin l) : J v j = v j := by
      rw [hJapply]
      rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i hi hne
        apply lp.single_apply_ne
        intro heq
        exact hne (Fin.ext heq.symm)
      · simp
    have hJhigh (v : Fin l → Fin p.size → A) (j : ℕ) (hj : l ≤ j) : J v j = 0 := by
      rw [hJapply]
      rw [lp.coeFn_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      apply lp.single_apply_ne
      have hil := i.isLt
      omega
    have hCZ (x : X) : C (Z x) = 0 := by
      funext j
      change Z x (j : ℕ) = 0
      rw [hZ, ite_eq_right (by have hj := j.isLt; omega)]
    have hCJ (v : Fin l → Fin p.size → A) : C (J v) = v := by
      funext j
      exact hJlow v j
    have hHJ (v : Fin l → Fin p.size → A) : H (J v) = 0 := by
      apply lp.ext
      funext j
      rw [hH, hJhigh v _ (by omega)]
      rfl
    have hdecomp (x : X) : Z (H x) + J (C x) = x := by
      apply lp.ext
      funext j
      change Z (H x) j + J (C x) j = x j
      rw [hZ]
      split_ifs with hlj
      · rw [hH, hJhigh _ _ hlj, add_zero]
        apply congrArg (fun r : ℕ ↦ x r)
        omega
      · rw [zero_add]
        exact hJlow (C x) ⟨j, by omega⟩
    -- The low-coefficient section splits the original cokernel exact sequence.
    let Q : X →ₗ[A] p.ShiftedCokernel k hk :=
      polynomialCokernelMk f hk
    let F : X →ₗ[A]
        p.ShiftedCokernel k hk × (Fin l → Fin p.size → A) := (Q.comp H).prod C
    have hQT (x : X) : Q (T x) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨x, rfl⟩
    have hker : LinearMap.range U = LinearMap.ker F := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        change (Q (H (U y)), C (U y)) = 0
        rw [hU, hHZ, hQT, hCZ]
        rfl
      · intro x hx
        have hx₁ : Q (H x) = 0 := congrArg Prod.fst hx
        have hx₂ : C x = 0 := congrArg Prod.snd hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx₁
        refine ⟨y, ?_⟩
        rw [hU, show T y = H x from hy]
        simpa only [hx₂, map_zero, add_zero] using hdecomp x
    have hsurj : Function.Surjective F := by
      rintro ⟨q, v⟩
      obtain ⟨x, rfl⟩ := (LinearMap.range T).mkQ_surjective q
      refine ⟨Z x + J v, ?_⟩
      change (Q (H (Z x + J v)), C (Z x + J v)) = (Q x, v)
      rw [map_add, hHZ, hHJ, add_zero, map_add, hCZ, hCJ, zero_add]
    let e := (Submodule.quotEquivOfEq (LinearMap.range U) (LinearMap.ker F) hker).trans
      (F.quotKerEquivOfSurjective hsurj)
    -- Reindex the same first-l vectors to exactly size*l scalar coordinates.
    let efin : (Fin l → Fin p.size → A) ≃ₗ[A] (Fin (p.size * l) → A) :=
      { toFun v i := v (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm i).1
        invFun v j i := v (finProdFinEquiv (i, j))
        left_inv v := by funext j i; simp
        right_inv v := by
          funext i
          change v (finProdFinEquiv (finProdFinEquiv.symm i)) = v i
          rw [Equiv.apply_symm_apply]
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    exact ⟨e.trans ((LinearEquiv.refl _ _).prodCongr efin)⟩

end LaurentMatrixLoop

/-- The polynomial representative of the existing Bott loop of this idempotent. -/
def bottLaurentLoop (p : IdempotentMatrix A) : LaurentMatrixLoop A :=
  LaurentMatrixLoop.affine (1 - p.matrix) p.matrix (sub_add_cancel 1 p.matrix)
    (fun z ↦ by
      have h : IsUnit ((z : ℂ) • p.matrix + (1 - p.matrix)) :=
        (bottMatrixUnit p z).isUnit
      simpa only [add_comm] using h)

/-- The Laurent representative and the previously specified Bott map use the same loop. -/
theorem bottLaurentLoop_stableClass (p : IdempotentMatrix A) :
    (bottLaurentLoop p).stableClass = bottMatrixLoopClass p := by
  /- Stage 1: evaluate the two coefficients of the affine polynomial. Its matrix
  at z is (1-p)+z*p, equal by addition commutativity to the value of bottMatrixUnit.
  Equality of underlying matrices gives equality of units, regardless of the
  invertibility proof used in LaurentMatrixLoop.toCircleMap.
  Stage 2: both paths use Circle.exp (2πt), with the same identity base point and
  matrix size. Their finite loop representatives and hence their stable classes
  coincide. No hemisphere choice, reversed orientation, or geometric Bott-line
  comparison is involved in this identification. -/
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

/-- KA III.1.20: the cokernel of p*z+(1-p) is the image of the same p.
On an actual positive series representative, the equivalence takes its constant
coefficient and applies p; it is not an unspecified isomorphic projective module. -/
theorem exists_bottLaurentLoop_cokernel_equiv (p : IdempotentMatrix A) :
    ∃ hp : ((bottLaurentLoop p).shift (0 : ℤ)).IsPolynomial,
      ∃ e : (bottLaurentLoop p).ShiftedCokernel 0 hp ≃ₗ[A] p.image,
        ∀ x : PositiveWienerModule A p.size,
          ((e (polynomialCokernelMk
            ((bottLaurentLoop p).shift (0 : ℤ)).polynomial hp x)) : Fin p.size → A) =
              p.matrix.mulVec (x 0) := by
  /- Stage 1: the only coefficients are 1-p in degree zero and p in degree one;
  a shift by zero does not change them. Split A^n into im(p) and im(1-p), and
  apply these bounded matrix projections coefficientwise to positive ℓ¹ series.
  Stage 2: the specified multiplier acts as z on im(p)-valued series and as the
  identity on im(1-p)-valued series. The A-linear map x ↦ p*x₀ is surjective
  onto im(p), using the constant-series inclusion as a section.
  Stage 3: its kernel is exactly the multiplier range. For a series in this
  kernel, shift its im(p) coefficients down by one and leave its complementary
  coefficients unchanged; both operations preserve absolute summability. This
  constructs an actual preimage under p*z+(1-p). The quotient first-isomorphism
  theorem supplies e with the displayed representative formula. Its target is
  the image of the original p, not the image of a separately chosen idempotent. -/
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
    let T : X →ₗ[A] X := polynomialMultiplier f hp
    have hTzero (x : X) : T x 0 = (1 - p.matrix).mulVec (x 0) := by
      change polynomialMultiplier f hp x 0 = _
      rw [polynomialMultiplier_coeff]
      simp [hcoeff]
    have hTsucc (x : X) (k : ℕ) : T x (k + 1) =
        (1 - p.matrix).mulVec (x (k + 1)) + p.matrix.mulVec (x k) := by
      change polynomialMultiplier f hp x (k + 1) = _
      rw [polynomialMultiplier_coeff]
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
        positiveWienerToeplitz (lp.single 1 d b) x k =
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
    let P : X →ₗ[A] X := positiveWienerToeplitz (lp.single 1 0 p.matrix)
    let Q : X →ₗ[A] X := positiveWienerToeplitz (lp.single 1 0 (1 - p.matrix))
    let H : X →ₗ[A] X :=
      positiveWienerToeplitz (lp.single 1 (-1) (1 : Matrix (Fin p.size) (Fin p.size) A))
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
    let F : X →ₗ[A] p.image :=
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

end AtiyahSinger
