/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LaurentWiener
public import AtiyahSinger.Analysis.WienerFactorization
public import AtiyahSinger.Topology.BottLoop
public import AtiyahSinger.Topology.PolynomialLoop
public import Mathlib.Analysis.Matrix.Normed

/-!
# Polynomial reduction and surjectivity of the specified Bott loop map

Public module ID: M1569.

Karoubi III.1.21 and Theorem 1.25, pp.120–122. Laurent approximation, polynomial
linearization and the one-sided factorization are composed using the same finite
matrix loops. The affine idempotent is precisely 1-a₀b₀ for the specified Wiener
inverse b. It is not assumed self-adjoint.

The final map is the existing kZeroBottLoop. Its current K₀ carrier requires
commutative coefficients, although Laurent reduction and the analytic factorization
do not. Surjectivity alone is not Bott periodicity: the cokernel inverse and its
left-inverse identity, and the geometric clutching comparison, remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Matrix.Norms.Operator

universe u

section PolynomialDifference

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Multiplication by a scalar Laurent monomial preserves the based invertible condition. -/
theorem LaurentMatrixLoop.shift_properties (p : LaurentMatrixLoop A) (k : ℤ) :
    laurentPolynomialCircleValue (LaurentPolynomial.T k * p.polynomial) 1 = 1 ∧
      ∀ z : Circle,
        IsUnit (laurentPolynomialCircleValue (LaurentPolynomial.T k * p.polynomial) z) := by
  -- Finite Laurent evaluation commutes with the specified scalar shift.
  have shift_value {n : ℕ} (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A)) (k : ℤ) (z : Circle) :
      laurentPolynomialCircleValue (LaurentPolynomial.T k * f) z =
        (z : ℂ) ^ k • laurentPolynomialCircleValue f z := by
    classical
    have hadd (a b : LaurentPolynomial (Matrix (Fin n) (Fin n) A)) :
        laurentPolynomialCircleValue (a + b) z =
          laurentPolynomialCircleValue a z + laurentPolynomialCircleValue b z := by
      simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index, smul_add]
    have hterm (a : Matrix (Fin n) (Fin n) A) (j : ℤ) :
        laurentPolynomialCircleValue (LaurentPolynomial.C a * LaurentPolynomial.T j) z =
          (z : ℂ) ^ j • a := by
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, smul_zero]
    refine f.induction_on' ?_ ?_
    · intro a b ha hb
      rw [mul_add, hadd, ha, hb, hadd, smul_add]
    · intro j a
      rw [← mul_assoc, LaurentPolynomial.T_mul, mul_assoc, ← LaurentPolynomial.T_add]
      rw [hterm, hterm, zpow_add₀ z.coe_ne_zero, mul_smul]
  -- The scalar is one at the base point and a unit everywhere on the circle.
  constructor
  · rw [shift_value, p.normalized]
    simp
  · intro z
    rw [shift_value, Algebra.smul_def]
    have hz : IsUnit ((z : ℂ) ^ k) :=
      isUnit_iff_ne_zero.mpr (zpow_ne_zero k z.coe_ne_zero)
    exact (hz.map (algebraMap ℂ (Matrix (Fin p.size) (Fin p.size) A))).mul
      (p.invertible z)

/-- The scalar shift z^kσ(z), retaining the original finite matrix size. -/
def LaurentMatrixLoop.shift (p : LaurentMatrixLoop A) (k : ℤ) : LaurentMatrixLoop A where
  size := p.size
  polynomial := LaurentPolynomial.T k * p.polynomial
  normalized := (p.shift_properties k).1
  invertible := (p.shift_properties k).2

/-- The scalar monomial loop z^kI in a specified matrix size. -/
def LaurentMatrixLoop.monomial (n : ℕ) (k : ℤ) : LaurentMatrixLoop A :=
  (LaurentMatrixLoop.affine (1 : Matrix (Fin n) (Fin n) A) 0
    (by simp) (by intro z; simp)).shift k

/-- KA III.1.21: the actual shifted polynomial classes give the Laurent class. -/
theorem LaurentMatrixLoop.exists_polynomial_difference (p : LaurentMatrixLoop A) :
    ∃ k : ℕ, (p.shift (k : ℤ)).IsPolynomial ∧
      (LaurentMatrixLoop.monomial (A := A) p.size (k : ℤ)).IsPolynomial ∧
      p.stableClass = (p.shift (k : ℤ)).stableClass -
        (LaurentMatrixLoop.monomial (A := A) p.size (k : ℤ)).stableClass := by
  -- Compare the actual block-sum representative with the pointwise product.
  have block_sum_homotopic_pointwise {n : ℕ}
      (p q r : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
      (hr : ∀ t, r t = p t * q t) :
      (((⟨n, p⟩ : FiniteMatrixLoop A).blockSum ⟨n, q⟩).loop).Homotopic
        (((⟨n, r⟩ : FiniteMatrixLoop A).stabilize n).loop) := by
    classical
    let B := Matrix (Fin n) (Fin n) A
    let M := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A
    -- Each elementary shear has the opposite shear as its actual inverse.
    let upper (b : B) : Mˣ :=
      { val := Matrix.fromBlocks 1 b 0 1
        inv := Matrix.fromBlocks 1 (-b) 0 1
        val_inv := by simp [B, M, Matrix.fromBlocks_multiply]
        inv_val := by simp [B, M, Matrix.fromBlocks_multiply] }
    let lower (b : B) : Mˣ :=
      { val := Matrix.fromBlocks 1 0 b 1
        inv := Matrix.fromBlocks 1 0 (-b) 1
        val_inv := by simp [B, M, Matrix.fromBlocks_multiply]
        inv_val := by simp [B, M, Matrix.fromBlocks_multiply] }
    have hup : Continuous upper := by
      apply Units.continuous_iff.mpr
      constructor
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) b 0 1)
        fun_prop
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) (-b) 0 1)
        fun_prop
    have hlo : Continuous lower := by
      apply Units.continuous_iff.mpr
      constructor
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) 0 b 1)
        fun_prop
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) 0 (-b) 1)
        fun_prop
    let T (t : unitInterval) : ℂ := ((t : ℝ) : ℂ)
    let W (v : Bˣ) (t : unitInterval) : Mˣ :=
      upper (T t • (v : B)) * lower (-T t • (↑(v⁻¹) : B)) * upper (T t • (v : B))
    have hW (v : Bˣ) : Continuous (W v) := by
      exact ((hup.comp (by fun_prop)).mul (hlo.comp (by fun_prop))).mul
        (hup.comp (by fun_prop))
    have hWzero (v : Bˣ) : W v 0 = 1 := by
      apply Units.ext
      simp [W, T, upper, lower, B, M]
    have hWone (v : Bˣ) : (W v 1 : M) =
        Matrix.fromBlocks 0 (v : B) (-(↑(v⁻¹) : B)) 0 := by
      simp [W, T, upper, lower, B, M, Matrix.fromBlocks_multiply]
    let e := (Matrix.reindexRingEquiv A (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)))
    let U (t : unitInterval) := Units.map e.toMonoidHom (W (-1) t)
    have hU : Continuous U := by
      apply Units.continuous_iff.mpr
      constructor
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_val (M := M)).comp (hW (-1))))
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_coe_inv (M := M)).comp (hW (-1))))
    have hUzero : U 0 = 1 := by simp only [U, hWzero, map_one]
    have hswap (b : Bˣ) :
        U 1 * matrixUnitBlockSum (1 : Bˣ) b * (U 1)⁻¹ = matrixUnitBlockSum b (1 : Bˣ) := by
      apply (mul_inv_eq_iff_eq_mul).mpr
      apply Units.ext
      change e (W (-1) 1 : M) * e (Matrix.fromBlocks (1 : B) 0 0 (b : B)) =
        e (Matrix.fromBlocks (b : B) 0 0 (1 : B)) * e (W (-1) 1 : M)
      rw [← map_mul, ← map_mul, hWone]
      simp [B, Matrix.fromBlocks_multiply]
    have hblock (a b c d : Bˣ) :
        matrixUnitBlockSum a b * matrixUnitBlockSum c d =
          matrixUnitBlockSum (a*c) (b*d) := by
      apply Units.ext
      simp [matrixUnitBlockSum, Matrix.fromBlocks_multiply]
    have hb : matrixUnitBlockSum (1 : Bˣ) (1 : Bˣ) = 1 := by
      apply Units.ext
      simp [matrixUnitBlockSum]
    refine ⟨{ toFun := fun st ↦ matrixUnitBlockSum (p st.2) (1 : Bˣ) *
        (U st.1 * matrixUnitBlockSum (1 : Bˣ) (q st.2) * (U st.1)⁻¹)
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · have hp : Continuous (fun st : unitInterval × unitInterval ↦
          matrixUnitBlockSum (p st.2) (1 : Bˣ)) := (continuous_matrixUnitBlockSum n n).comp
        ((p.continuous.comp continuous_snd).prodMk continuous_const)
      have hq : Continuous (fun st : unitInterval × unitInterval ↦
          matrixUnitBlockSum (1 : Bˣ) (q st.2)) := (continuous_matrixUnitBlockSum n n).comp
        (continuous_const.prodMk (q.continuous.comp continuous_snd))
      exact hp.mul (((hU.comp continuous_fst).mul hq).mul (hU.comp continuous_fst).inv)
    · intro t
      change matrixUnitBlockSum (p t) (1 : Bˣ) *
        (U 0 * matrixUnitBlockSum (1 : Bˣ) (q t) * (U 0)⁻¹) =
          matrixUnitBlockSum (p t) (q t)
      rw [hUzero, inv_one, one_mul, mul_one, hblock, mul_one, one_mul]
    · intro t
      change matrixUnitBlockSum (p t) (1 : Bˣ) *
        (U 1 * matrixUnitBlockSum (1 : Bˣ) (q t) * (U 1)⁻¹) =
          matrixUnitBlockSum (r t) (1 : Bˣ)
      rw [hswap, hblock, mul_one, hr]
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        change matrixUnitBlockSum (p 0) (1 : Bˣ) *
          (U s * matrixUnitBlockSum (1 : Bˣ) (q 0) * (U s)⁻¹) =
            matrixUnitBlockSum (p 0) (q 0)
        rw [p.source, q.source, hb, mul_one, mul_inv_cancel, one_mul]
      · have ht' : t = 1 := ht
        subst t
        change matrixUnitBlockSum (p 1) (1 : Bˣ) *
          (U s * matrixUnitBlockSum (1 : Bˣ) (q 1) * (U s)⁻¹) =
            matrixUnitBlockSum (p 1) (q 1)
        rw [p.target, q.target, hb, mul_one, mul_inv_cancel, one_mul]
  -- Descend that based homotopy through the existing stabilization quotient.
  have pointwise_class {n : ℕ}
      (p q r : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
      (hr : ∀ t, r t = p t * q t) :
      stableMatrixLoopClass (⟨n, r⟩ : FiniteMatrixLoop A) =
        stableMatrixLoopClass (⟨n, p⟩ : FiniteMatrixLoop A) +
          stableMatrixLoopClass (⟨n, q⟩ : FiniteMatrixLoop A) := by
    have hzero (v : FiniteMatrixLoop A) : (v.stabilize 0).loop = v.loop := by
      apply Path.ext
      funext t
      apply Units.ext
      ext i j
      change (matrixUnitBlockSum (v.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
        Matrix (Fin (v.size + 0)) (Fin (v.size + 0)) A) i j =
        (v.loop t : Matrix (Fin v.size) (Fin v.size) A) i j
      refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
      refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
      change Matrix.fromBlocks (v.loop t : Matrix (Fin v.size) (Fin v.size) A)
        (0 : Matrix (Fin v.size) (Fin 0) A) 0 1
          (finSumFinEquiv.symm (Fin.castAdd 0 i))
          (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
      rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
      rfl
    have hrel : ((⟨n, p⟩ : FiniteMatrixLoop A).blockSum ⟨n, q⟩).StablyHomotopic
        ((⟨n, r⟩ : FiniteMatrixLoop A).stabilize n) := by
      refine ⟨0, 0, rfl, ?_⟩
      change Path.Homotopic
        (((⟨n, p⟩ : FiniteMatrixLoop A).blockSum ⟨n, q⟩).stabilize 0).loop
        (((⟨n, r⟩ : FiniteMatrixLoop A).stabilize n).stabilize 0).loop
      rw [hzero, hzero]
      exact block_sum_homotopic_pointwise p q r hr
    calc
      stableMatrixLoopClass (⟨n, r⟩ : FiniteMatrixLoop A) =
          stableMatrixLoopClass ((⟨n, r⟩ : FiniteMatrixLoop A).stabilize n) :=
        (stableMatrixLoopClass_stabilize _ _).symm
      _ = stableMatrixLoopClass ((⟨n, p⟩ : FiniteMatrixLoop A).blockSum ⟨n, q⟩) :=
        ((stableMatrixLoopClass_eq_iff _ _).mpr hrel).symm
      _ = _ := stableMatrixLoopClass_blockSum _ _
  -- Scalar shifting can be computed directly from the finite Laurent support.
  have shift_value {n : ℕ} (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A)) (k : ℤ) (z : Circle) :
      laurentPolynomialCircleValue (LaurentPolynomial.T k * f) z =
        (z : ℂ) ^ k • laurentPolynomialCircleValue f z := by
    classical
    have hadd (a b : LaurentPolynomial (Matrix (Fin n) (Fin n) A)) :
        laurentPolynomialCircleValue (a + b) z =
          laurentPolynomialCircleValue a z + laurentPolynomialCircleValue b z := by
      simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index, smul_add]
    have hterm (a : Matrix (Fin n) (Fin n) A) (j : ℤ) :
        laurentPolynomialCircleValue (LaurentPolynomial.C a * LaurentPolynomial.T j) z =
          (z : ℂ) ^ j • a := by
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, smul_zero]
    refine f.induction_on' ?_ ?_
    · intro a b ha hb
      rw [mul_add, hadd, ha, hb, hadd, smul_add]
    · intro j a
      rw [← mul_assoc, LaurentPolynomial.T_mul, mul_assoc, ← LaurentPolynomial.T_add]
      rw [hterm, hterm, zpow_add₀ z.coe_ne_zero, mul_smul]
  -- A single shift removes all negative exponents from both prescribed loops.
  have exists_nonnegative_shift (f : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A)) :
      ∃ k : ℕ, (∀ j : ℤ, j < 0 → (LaurentPolynomial.T (k : ℤ) * f).coeff j = 0) ∧
        (∀ j : ℤ, j < 0 →
          (LaurentPolynomial.T (k : ℤ) :
            LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A)).coeff j = 0) := by
    classical
    obtain ⟨k, q, hq⟩ := f.exists_T_pow
    refine ⟨k, ?_, ?_⟩
    · intro j hj
      rw [LaurentPolynomial.T_mul, ← hq]
      apply Finsupp.notMem_support_iff.mp
      rw [LaurentPolynomial.support_coeff_toLaurent]
      intro hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hmem
      change (i : ℤ) = j at hi
      omega
    · intro j hj
      have hne : (k : ℤ) ≠ j := by omega
      simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne (Ne.symm hne)]
  -- Keep these exact representatives when taking their difference in the stable group.
  obtain ⟨k, hk, hmono⟩ := exists_nonnegative_shift p.polynomial
  refine ⟨k, hk, ?_, ?_⟩
  · change ∀ j : ℤ, j < 0 →
      (LaurentPolynomial.T (k : ℤ) *
        (LaurentPolynomial.C (1 : Matrix (Fin p.size) (Fin p.size) A) +
          LaurentPolynomial.C 0 * LaurentPolynomial.T 1)).coeff j = 0
    simpa only [map_zero, zero_mul, add_zero, map_one, mul_one] using hmono
  · let r := p.shift (k : ℤ)
    let s := LaurentMatrixLoop.monomial (A := A) p.size (k : ℤ)
    let rp : Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 :=
      r.toFiniteMatrixLoop.loop
    let sp : Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 :=
      s.toFiniteMatrixLoop.loop
    let pp : Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 :=
      p.toFiniteMatrixLoop.loop
    have hvalues : ∀ t, rp t = sp t * pp t := by
      intro t
      apply Units.ext
      let z : Circle := Circle.exp (2 * Real.pi * (t : ℝ))
      change laurentPolynomialCircleValue (LaurentPolynomial.T (k : ℤ) * p.polynomial) z =
        laurentPolynomialCircleValue (LaurentPolynomial.T (k : ℤ) *
          (LaurentPolynomial.C (1 : Matrix (Fin p.size) (Fin p.size) A) +
            LaurentPolynomial.C 0 * LaurentPolynomial.T 1)) z *
          laurentPolynomialCircleValue p.polynomial z
      have hone : laurentPolynomialCircleValue
          (LaurentPolynomial.C (1 : Matrix (Fin p.size) (Fin p.size) A) +
            LaurentPolynomial.C 0 * LaurentPolynomial.T 1) z = 1 := by
        simp only [map_zero, zero_mul, add_zero, ← LaurentPolynomial.single_eq_C,
          laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single]
        simp
      have hmonoValue : laurentPolynomialCircleValue
          (LaurentPolynomial.T (k : ℤ) *
            (LaurentPolynomial.C (1 : Matrix (Fin p.size) (Fin p.size) A) +
              LaurentPolynomial.C 0 * LaurentPolynomial.T 1)) z = (z : ℂ) ^ (k : ℤ) • 1 :=
        (shift_value _ _ _).trans (congrArg (fun x ↦ (z : ℂ) ^ (k : ℤ) • x) hone)
      refine (shift_value _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg
        (fun x : Matrix (Fin p.size) (Fin p.size) A ↦
          x * laurentPolynomialCircleValue p.polynomial z) hmonoValue.symm)
      simp only [Algebra.smul_def, mul_one]
    have hclass := pointwise_class (n := p.size)
      sp pp rp hvalues
    change r.stableClass = s.stableClass + p.stableClass at hclass
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using hclass.symm

end PolynomialDifference

section Surjectivity

variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

local instance matrixCompleteSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- The finite idempotent extracted from the specified affine Wiener inverse. -/
def affineBottIdempotentMatrix {n : ℕ} (a₀ a₁ : Matrix (Fin n) (Fin n) A)
    (hbase : a₀ + a₁ = 1) (b : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hleft : WienerLoop.affine a₀ a₁ * b = 1)
    (hright : b * WienerLoop.affine a₀ a₁ = 1) : IdempotentMatrix A where
  size := n
  matrix := WienerLoop.affineBottIdempotent a₀ b
  mul_self := WienerLoop.affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright

/-- The affine factorization gives the Bott loop of this exact complementary projector. -/
theorem affine_stableClass_eq_bott {n : ℕ} (a₀ a₁ : Matrix (Fin n) (Fin n) A)
    (hbase : a₀ + a₁ = 1)
    (hunit : ∀ z : Circle, IsUnit (a₀ + (z : ℂ) • a₁))
    (b : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hleft : WienerLoop.affine a₀ a₁ * b = 1)
    (hright : b * WienerLoop.affine a₀ a₁ = 1) :
    (LaurentMatrixLoop.affine a₀ a₁ hbase hunit).stableClass =
      bottMatrixLoopClass (affineBottIdempotentMatrix a₀ a₁ hbase b hleft hright) := by
  let B := Matrix (Fin n) (Fin n) A
  let P : B := WienerLoop.affineBottIdempotent a₀ b
  let p := affineBottIdempotentMatrix a₀ a₁ hbase b hleft hright
  let q := LaurentMatrixLoop.affine a₀ a₁ hbase hunit
  let H := WienerLoop.affineBottHomotopy a₀ a₁ hbase b hleft hright
  -- Identify the two given affine evaluations, retaining their exact projector and parameter.
  have heval (x y : B) (z : Circle) : (WienerLoop.affine x y).eval z =
      x + (z : ℂ) • y := by
    classical
    change (∑' k : ℤ, (z : ℂ) ^ k •
      ((lp.single 1 0 x + lp.single 1 1 y : WienerLoop B) k)) = _
    simp only [lp.coeFn_add, lp.coeFn_single, Pi.add_apply]
    rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ))]
    · simp [Pi.single_apply]
    · intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
      simp [hk'.1, hk'.2]
  let value (st : unitInterval × unitInterval) : B :=
    H (st.1, Circle.exp (2 * Real.pi * (st.2 : ℝ)))
  have hvalue : Continuous value := H.continuous.comp
    (continuous_fst.prodMk (by fun_prop))
  have hvalueUnit (st : unitInterval × unitInterval) : IsUnit (value st) :=
    (H.prop' st.1).2 _
  -- Lift the very same normalized family to units, including its continuous inverse.
  have hcontinuous : Continuous (fun st ↦ (hvalueUnit st).unit) := by
    apply Units.continuous_iff.mpr
    constructor
    · simp only [Function.comp_def, IsUnit.unit_spec]
      exact hvalue
    · simp only [← Ring.inverse_unit, IsUnit.unit_spec]
      apply continuous_iff_continuousAt.mpr
      intro st
      have hi := NormedRing.inverse_continuousAt (hvalueUnit st).unit
      simp only [IsUnit.unit_spec] at hi
      exact hi.comp hvalue.continuousAt
  have hpath : (bottMatrixPath p).Homotopic q.toFiniteMatrixLoop.loop := by
    refine ⟨{ toFun := fun st ↦ (hvalueUnit st).unit
              continuous_toFun := hcontinuous
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      apply Units.ext
      simp only [IsUnit.unit_spec]
      change H (0, Circle.exp (2 * Real.pi * (t : ℝ))) =
        (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) • P + (1 - P)
      refine (H.map_zero_left _).trans ?_
      change (WienerLoop.affine (1 - P) P).eval _ = _
      rw [heval, add_comm]
    · intro t
      apply Units.ext
      simp only [IsUnit.unit_spec]
      change H (1, Circle.exp (2 * Real.pi * (t : ℝ))) =
        laurentPolynomialCircleValue
          (LaurentPolynomial.C a₀ + LaurentPolynomial.C a₁ * LaurentPolynomial.T 1) _
      refine (H.map_one_left _).trans ?_
      change (WienerLoop.affine a₀ a₁).eval _ =
        laurentPolynomialCircleValue
          (LaurentPolynomial.C a₀ + LaurentPolynomial.C a₁ * LaurentPolynomial.T 1) _
      rw [heval]
      rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C]
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_single]
      simp [Finsupp.sum_add_index, smul_add]
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        erw [(bottMatrixPath p).source]
        apply Units.ext
        change H (s, Circle.exp (2 * Real.pi * (0 : ℝ))) = 1
        simp only [mul_zero, Circle.exp_zero]
        exact (H.prop' s).1
      · have ht' : t = 1 := ht
        subst t
        erw [(bottMatrixPath p).target]
        apply Units.ext
        change H (s, Circle.exp (2 * Real.pi * (1 : ℝ))) = 1
        simp only [mul_one, Circle.exp_two_pi]
        exact (H.prop' s).1
  -- Append empty identity blocks only to express this unstabilized based homotopy.
  have hzero (r : FiniteMatrixLoop A) : (r.stabilize 0).loop = r.loop := by
    apply Path.ext
    funext t
    apply Units.ext
    ext i j
    change (matrixUnitBlockSum (r.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
      Matrix (Fin (r.size + 0)) (Fin (r.size + 0)) A) i j =
      (r.loop t : Matrix (Fin r.size) (Fin r.size) A) i j
    refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
    refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
    change Matrix.fromBlocks (r.loop t : Matrix (Fin r.size) (Fin r.size) A)
      (0 : Matrix (Fin r.size) (Fin 0) A) 0 1
        (finSumFinEquiv.symm (Fin.castAdd 0 i))
        (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  apply Eq.symm
  apply (stableMatrixLoopClass_eq_iff _ _).mpr
  refine ⟨0, 0, rfl, ?_⟩
  change Path.Homotopic ((bottMatrixLoop p).stabilize 0).loop
    (q.toFiniteMatrixLoop.stabilize 0).loop
  rw [hzero, hzero]
  exact hpath

/-- KA III.1.25 for the project's commutative Banach-algebra K₀ model. -/
theorem kZeroBottLoop_surjective : Function.Surjective (kZeroBottLoop A) := by
  /- Choose an original finite loop representative and use
  exists_laurent_representative to obtain a Laurent loop with the same class.
  exists_polynomial_difference expresses it as the difference of two
  polynomial classes; exists_affine_representative reduces each to an affine one.
  Finite support and pointwise invertibility give a two-sided Wiener inverse.
  affine_stableClass_eq_bott identifies the normalized affine class with the
  Bott loop of the exact projector 1-a₀b₀ from that inverse.
  Take the difference of those two finite-projective K₀ classes. Additivity
  and kZeroBottLoop_class give the required image of every original class. -/
  classical
  -- Each polynomial class is the Bott image of its actual affine Wiener projector.
  have polynomial_preimage (p : LaurentMatrixLoop A) (hp : p.IsPolynomial) :
      ∃ x : KZero A, kZeroBottLoop A x = p.stableClass := by
    obtain ⟨n, a₀, a₁, hbase, hunit, hclass⟩ := p.exists_affine_representative hp
    let f : WienerLoop (Matrix (Fin n) (Fin n) A) := WienerLoop.affine a₀ a₁
    have hfinite : (Function.support (fun k : ℤ ↦ f k)).Finite := by
      refine ((Set.finite_singleton (0 : ℤ)).union (Set.finite_singleton 1)).subset ?_
      intro k hk
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      by_cases hk1 : k = 1
      · exact Or.inr hk1
      exact False.elim (hk (by
        change (lp.single 1 0 a₀ : WienerLoop _) k +
          (lp.single 1 1 a₁ : WienerLoop _) k = 0
        have hzero : (lp.single 1 0 a₀ : WienerLoop _) k = 0 :=
          lp.single_apply_ne (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 0 a₀ hk0
        have hone : (lp.single 1 1 a₁ : WienerLoop _) k = 0 :=
          lp.single_apply_ne (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 1 a₁ hk1
        exact (congrArg₂ (· + ·) hzero hone).trans (zero_add 0)))
    have heval (z : Circle) : f.eval z = a₀ + (z : ℂ) • a₁ := by
      change (∑' k : ℤ, (z : ℂ) ^ k •
        ((lp.single 1 0 a₀ + lp.single 1 1 a₁ : WienerLoop _) k)) = _
      simp only [lp.coeFn_add, lp.coeFn_single, Pi.add_apply]
      rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ))]
      · simp [Pi.single_apply]
      · intro k hk
        have hk' : k ≠ 0 ∧ k ≠ 1 := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
        simp [hk'.1, hk'.2]
    have hfunit : IsUnit f := WienerLoop.isUnit_of_finiteSupport f hfinite (by
      intro z
      rw [heval]
      exact hunit z)
    -- Use one unit witness for both ordered inverse equations and the exact projector.
    let b : WienerLoop (Matrix (Fin n) (Fin n) A) := ↑(hfunit.unit⁻¹)
    have hleft : WienerLoop.affine a₀ a₁ * b = 1 := by
      change f * ↑(hfunit.unit⁻¹) = 1
      simpa only [IsUnit.unit_spec] using (Units.mul_inv hfunit.unit)
    have hright : b * WienerLoop.affine a₀ a₁ = 1 := by
      change ↑(hfunit.unit⁻¹) * f = 1
      simpa only [IsUnit.unit_spec] using (Units.inv_mul hfunit.unit)
    let q := affineBottIdempotentMatrix a₀ a₁ hbase b hleft hright
    refine ⟨kZeroClass A q, ?_⟩
    rw [kZeroBottLoop_class]
    exact (affine_stableClass_eq_bott a₀ a₁ hbase hunit b hleft hright).symm.trans
      hclass.symm
  -- Preserve the actual Laurent representative and the two prescribed scalar shifts.
  intro x
  obtain ⟨v, rfl⟩ := Quotient.exists_rep x
  obtain ⟨p, hp⟩ := v.exists_laurent_representative
  obtain ⟨k, hk, hmonomial, hdifference⟩ := p.exists_polynomial_difference
  obtain ⟨y, hy⟩ := polynomial_preimage (p.shift (k : ℤ)) hk
  obtain ⟨z, hz⟩ := polynomial_preimage (LaurentMatrixLoop.monomial p.size (k : ℤ))
    hmonomial
  -- Subtract the two genuine finite-projective classes using the original homomorphism.
  refine ⟨y - z, ?_⟩
  rw [map_sub, hy, hz, ← hdifference]
  exact hp

end Surjectivity

end AtiyahSinger
