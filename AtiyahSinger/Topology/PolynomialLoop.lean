/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LaurentLoop

/-!
# Polynomial matrix loops and stable affine reduction

Public module ID: M1992.

Karoubi III.1.12 and Lemma III.1.22, pp.116 and 120: a polynomial loop is a finite
Laurent loop with no negative coefficients. Every such loop represents the same
stable based homotopy class as an actual affine loop with two matrix coefficients.

The reduction uses invertible elementary block matrices and right normalization
at the base point. It works over noncommutative complex Banach algebras. Only
pointwise invertibility on the circle is required, not invertibility in a polynomial
ring or in the one-sided Wiener algebra. In particular, the loop z times the identity
is allowed even though its inverse has a negative power.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

namespace LaurentMatrixLoop

/-- KA III.1.12: a Laurent loop is polynomial when all negative coefficients vanish. -/
def IsPolynomial (p : LaurentMatrixLoop A) : Prop :=
  ∀ k : ℤ, k < 0 → p.polynomial.coeff k = 0

/-- The actual normalized affine loop with the specified two matrix coefficients. -/
def affine {n : ℕ} (a₀ a₁ : Matrix (Fin n) (Fin n) A) (hnorm : a₀ + a₁ = 1)
    (hunit : ∀ z : Circle, IsUnit (a₀ + (z : ℂ) • a₁)) : LaurentMatrixLoop A := by
  let p : LaurentPolynomial (Matrix (Fin n) (Fin n) A) :=
    LaurentPolynomial.C a₀ + LaurentPolynomial.C a₁ * LaurentPolynomial.T 1
  have heval (z : Circle) : laurentPolynomialCircleValue p z = a₀ + (z : ℂ) • a₁ := by
    classical
    dsimp only [p]
    rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C]
    simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
      AddMonoidAlgebra.coeff_single]
    simp [Finsupp.sum_add_index, smul_add]
  exact
    { size := n
      polynomial := p
      normalized := by simpa [heval] using hnorm
      invertible := fun z ↦ (heval z).symm ▸ hunit z }

variable [CompleteSpace A]

/-- KA III.1.22: every polynomial matrix loop has an affine representative after
finite stabilization and based homotopy. The affine coefficients and their normalization
and invertibility certificates belong to the same representative. -/
theorem exists_affine_representative (p : LaurentMatrixLoop A) (hp : p.IsPolynomial) :
    ∃ (n : ℕ) (a₀ a₁ : Matrix (Fin n) (Fin n) A)
      (hnorm : a₀ + a₁ = 1) (hunit : ∀ z : Circle, IsUnit (a₀ + (z : ℂ) • a₁)),
      p.stableClass = (affine a₀ a₁ hnorm hunit).stableClass := by
  /- Follow the book's degree reduction: elementary block shears remove one leading
  coefficient, and right normalization keeps the original base point fixed. The
  finite coefficient construction below certifies that the same endpoint is still
  polynomial, so induction reaches an actual affine representative. -/
  have exists_degree_bound {R : Type u} [Semiring R] (p : LaurentPolynomial R) :
      ∃ d : ℕ, ∀ j : ℤ, (d : ℤ) < j → p.coeff j = 0 := by
    classical
    refine ⟨p.coeff.support.sup Int.toNat, ?_⟩
    intro j hj
    by_contra hne
    have hmem : j ∈ p.coeff.support := Finsupp.mem_support_iff.mpr hne
    have hle : j.toNat ≤ p.coeff.support.sup Int.toNat := Finset.le_sup hmem
    omega
  have eq_affine_of_degree_le_one {R : Type u} [Semiring R] (p : LaurentPolynomial R)
      (hnegative : ∀ j : ℤ, j < 0 → p.coeff j = 0)
      (hupper : ∀ j : ℤ, 1 < j → p.coeff j = 0) :
      p = LaurentPolynomial.C (p.coeff 0) +
        LaurentPolynomial.C (p.coeff 1) * LaurentPolynomial.T 1 := by
    rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C_mul_T]
    ext j
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single]
    by_cases hzero : j = 0
    · subst j
      simp
    by_cases hone : j = 1
    · subst j
      simp
    have hp : p.coeff j = 0 := by
      by_cases hj : j < 0
      · exact hnegative j hj
      · exact hupper j (by omega)
    simp [hzero, hone, hp]
  have value_affine_of_degree_le_one {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
      (p : LaurentPolynomial A) (hnegative : ∀ j : ℤ, j < 0 → p.coeff j = 0)
      (hupper : ∀ j : ℤ, 1 < j → p.coeff j = 0) (z : Circle) :
      laurentPolynomialCircleValue p z = p.coeff 0 + (z : ℂ) • p.coeff 1 := by
    classical
    have h := eq_affine_of_degree_le_one p hnegative hupper
    conv_lhs => rw [h]
    rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
      AddMonoidAlgebra.coeff_single]
    simp [Finsupp.sum_add_index, smul_add]
  have reduce_degree (p : LaurentMatrixLoop A) (hp : p.IsPolynomial) (d : ℕ)
      (hd : 2 ≤ d) (hbound : ∀ j : ℤ, (d : ℤ) < j → p.polynomial.coeff j = 0) :
      ∃ q : LaurentMatrixLoop A, q.IsPolynomial ∧
        (∀ j : ℤ, ((d - 1 : ℕ) : ℤ) < j → q.polynomial.coeff j = 0) ∧
        p.stableClass = q.stableClass := by
    classical
    -- Work in the original ordered doubled matrix coordinates.
    let n := p.size
    let B := Matrix (Fin n) (Fin n) A
    let M := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A
    let C := Matrix (Fin (n + n)) (Fin (n + n)) A
    let a : B := p.polynomial.coeff (d : ℤ)
    let e := Matrix.reindexRingEquiv A (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
    let emb : B →ₗ[ℂ] C :=
      { toFun := fun b ↦ e (Matrix.fromBlocks b 0 0 0)
        map_add' := by
          intro b c
          rw [← map_add]
          congr 1
          ext i j
          cases i <;> cases j <;> simp [B]
        map_smul' := by
          intro c b
          ext i j
          change Matrix.fromBlocks (c • b) 0 0 0
              (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
            (c • Matrix.fromBlocks b 0 0 0) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
          cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp [B] }
    -- Each elementary shear retains its explicit opposite shear as inverse.
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
    -- Continuously perform both degree-lowering shears on the given unit loop.
    let T (t : unitInterval) : ℂ := ((t : ℝ) : ℂ)
    let U (tz : unitInterval × Circle) : Cˣ :=
      Units.map e.toMonoidHom (upper (-(T tz.1 * (tz.2 : ℂ) ^ (d - 1)) • (1 : B)))
    let L (tz : unitInterval × Circle) : Cˣ :=
      Units.map e.toMonoidHom (lower ((T tz.1 * (tz.2 : ℂ)) • a))
    have hU : Continuous U := by
      apply Units.continuous_iff.mpr
      constructor
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_val (M := M)).comp (hup.comp (by fun_prop))))
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_coe_inv (M := M)).comp (hup.comp (by fun_prop))))
    have hL : Continuous L := by
      apply Units.continuous_iff.mpr
      constructor
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_val (M := M)).comp (hlo.comp (by fun_prop))))
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_coe_inv (M := M)).comp (hlo.comp (by fun_prop))))
    let D (z : Circle) : Cˣ :=
      matrixUnitBlockSum ((p.invertible z).unit) (1 : Bˣ)
    have hD : Continuous D :=
      (continuous_matrixUnitBlockSum n n).comp
        (p.continuous_unitValue.prodMk continuous_const)
    let H (tz : unitInterval × Circle) : Cˣ := U tz * D tz.2 * L tz
    have hH : Continuous H := (hU.mul (hD.comp continuous_snd)).mul hL
    -- Normalize on the right at the same base point for every homotopy parameter.
    let G (tz : unitInterval × Circle) : Cˣ := H tz * (H (tz.1, 1))⁻¹
    have hG : Continuous G := hH.mul (hH.comp (continuous_fst.prodMk continuous_const)).inv
    have hbase (t : unitInterval) : G (t, 1) = 1 := by simp only [G, mul_inv_cancel]
    have hzero (z : Circle) : H (0, z) = D z := by
      have hUzero : U (0, z) = 1 := by
        apply Units.ext
        simp [U, T, upper, e, B, M, C]
      have hLzero : L (0, z) = 1 := by
        apply Units.ext
        simp [L, T, lower, e, B, M, C]
      simp only [H, hUzero, hLzero, one_mul, mul_one]
    have hDone : D 1 = 1 := by
      apply Units.ext
      simp [D, matrixUnitBlockSum, p.normalized]
    have hGzero (z : Circle) : G (0, z) = D z := by
      simp only [G, hzero, hDone, inv_one, mul_one]
    -- Identify the actual endpoint before the right basepoint normalization.
    have hHone (z : Circle) : (H (1, z) : C) =
        e (Matrix.fromBlocks
          (laurentPolynomialCircleValue p.polynomial z - (z : ℂ) ^ d • a)
          (-((z : ℂ) ^ (d - 1)) • (1 : B)) ((z : ℂ) • a) (1 : B)) := by
      change e (Matrix.fromBlocks 1 (-(T 1 * (z : ℂ) ^ (d - 1)) • (1 : B)) 0 1) *
          e (Matrix.fromBlocks (laurentPolynomialCircleValue p.polynomial z) 0 0 (1 : B)) *
            e (Matrix.fromBlocks 1 0 ((T 1 * (z : ℂ)) • a) 1) = _
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [T, Set.Icc.coe_one, Complex.ofReal_one, one_mul]
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      have hexp : d - 1 + 1 = d := by omega
      simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
        smul_mul_smul_comm, neg_mul, ← pow_succ, hexp, neg_smul, sub_eq_add_neg]
    -- Assemble a finite coefficient map for the endpoint, with the top degree removed.
    let topRight : C := e (Matrix.fromBlocks (0 : B) (-1) 0 0)
    let bottomLeft : C := e (Matrix.fromBlocks (0 : B) 0 a 0)
    let bottomRight : C := e (Matrix.fromBlocks (0 : B) 0 0 1)
    let raw : LaurentPolynomial C :=
      ⟨p.polynomial.coeff.mapRange emb (map_zero emb)⟩ -
        .single (d : ℤ) (emb a) + .single ((d - 1 : ℕ) : ℤ) topRight +
        .single 1 bottomLeft + .single 0 bottomRight
    have hevalMap {R S : Type u} [NormedRing R] [NormedAlgebra ℂ R]
        [NormedRing S] [NormedAlgebra ℂ S]
        (f : LaurentPolynomial R) (J : R →ₗ[ℂ] S) (z : Circle) :
        laurentPolynomialCircleValue
            (⟨f.coeff.mapRange J (map_zero J)⟩ : LaurentPolynomial S) z =
          J (laurentPolynomialCircleValue f z) := by
      change (f.coeff.mapRange J (map_zero J)).sum (fun k a ↦ (z : ℂ) ^ k • a) =
        J (f.coeff.sum (fun k a ↦ (z : ℂ) ^ k • a))
      rw [Finsupp.sum_mapRange_index (by intro k; exact smul_zero _)]
      simp only [Finsupp.sum, map_sum, map_smul]
    have hevalAdd (f g : LaurentPolynomial C) (z : Circle) :
        laurentPolynomialCircleValue (f + g) z =
          laurentPolynomialCircleValue f z + laurentPolynomialCircleValue g z := by
      simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index, smul_add]
    have hevalSub (f g : LaurentPolynomial C) (z : Circle) :
        laurentPolynomialCircleValue (f - g) z =
          laurentPolynomialCircleValue f z - laurentPolynomialCircleValue g z := by
      simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_sub,
        Finsupp.sum_sub_index, smul_sub]
    have hevalSingle (k : ℤ) (b : C) (z : Circle) :
        laurentPolynomialCircleValue (.single k b) z = (z : ℂ) ^ k • b := by
      simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, smul_zero]
    have hraw (z : Circle) : laurentPolynomialCircleValue raw z = (H (1, z) : C) := by
      dsimp only [raw]
      rw [hevalAdd, hevalAdd, hevalAdd, hevalSub, hevalMap,
        hevalSingle, hevalSingle, hevalSingle, hevalSingle, hHone]
      simp only [zpow_natCast, zpow_one, zpow_zero, one_smul]
      have hesmul (c : ℂ) (b : M) : e (c • b) = c • e b := rfl
      change e (Matrix.fromBlocks (laurentPolynomialCircleValue p.polynomial z) 0 0 0) -
        (z : ℂ) ^ d • e (Matrix.fromBlocks a 0 0 0) +
          (z : ℂ) ^ (d - 1) • e (Matrix.fromBlocks (0 : B) (-1) 0 0) +
            (z : ℂ) • e (Matrix.fromBlocks (0 : B) 0 a 0) +
              e (Matrix.fromBlocks (0 : B) 0 0 1) = _
      rw [← hesmul, ← hesmul, ← hesmul, ← map_sub, ← map_add, ← map_add, ← map_add]
      congr 1
      ext i j
      cases i <;> cases j <;> simp [B, M]
    have hrawCoeff (j : ℤ) : raw.coeff j =
        emb (p.polynomial.coeff j) - (if (d : ℤ) = j then emb a else 0) +
          (if ((d - 1 : ℕ) : ℤ) = j then topRight else 0) +
            (if (1 : ℤ) = j then bottomLeft else 0) +
              (if (0 : ℤ) = j then bottomRight else 0) := by
      simp only [raw, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
        AddMonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.sub_apply,
        Finsupp.mapRange_apply, Finsupp.single_apply]
    -- The actual endpoint has no negative coefficients and a strictly smaller degree bound.
    have hrawNeg (j : ℤ) (hj : j < 0) : raw.coeff j = 0 := by
      have hdj : (d : ℤ) ≠ j := by omega
      have hpred : ((d - 1 : ℕ) : ℤ) ≠ j := by omega
      have hone : (1 : ℤ) ≠ j := by omega
      have hzero : (0 : ℤ) ≠ j := by omega
      rw [hrawCoeff, hp j hj]
      simp only [hdj, hpred, hone, hzero, ite_false, map_zero, sub_zero, add_zero]
    have hrawBound (j : ℤ) (hj : ((d - 1 : ℕ) : ℤ) < j) : raw.coeff j = 0 := by
      have hpred : ((d - 1 : ℕ) : ℤ) ≠ j := by omega
      have hone : (1 : ℤ) ≠ j := by omega
      have hzero : (0 : ℤ) ≠ j := by omega
      rw [hrawCoeff]
      simp only [hpred, hone, hzero, ite_false, add_zero]
      by_cases heq : (d : ℤ) = j
      · subst j
        simp [a]
      · have hlt : (d : ℤ) < j := by omega
        rw [ite_eq_right heq, hbound j hlt, map_zero, sub_zero]
    -- Right multiplication uses the exact basepoint inverse, constant in the circle parameter.
    let R : C →ₗ[ℂ] C :=
      { toFun := fun b ↦ b * (↑((H (1, 1))⁻¹) : C)
        map_add' := fun b c ↦ add_mul b c _
        map_smul' := fun c b ↦ smul_mul_assoc c b _ }
    let qpoly : LaurentPolynomial C := ⟨raw.coeff.mapRange R (map_zero R)⟩
    have hqeval (z : Circle) : laurentPolynomialCircleValue qpoly z = (G (1, z) : C) := by
      exact (hevalMap raw R z).trans (congrArg R (hraw z))
    let q : LaurentMatrixLoop A :=
      { size := n + n
        polynomial := qpoly
        normalized := by
          exact (hqeval 1).trans (congrArg (fun u : Cˣ ↦ (u : C)) (hbase 1))
        invertible := fun z ↦ (hqeval z).symm ▸ (G (1, z)).isUnit }
    have hqNeg : q.IsPolynomial := by
      intro j hj
      change R (raw.coeff j) = 0
      rw [hrawNeg j hj, map_zero]
    have hqBound (j : ℤ) (hj : ((d - 1 : ℕ) : ℤ) < j) : q.polynomial.coeff j = 0 := by
      change R (raw.coeff j) = 0
      rw [hrawBound j hj, map_zero]
    -- The same normalized unit family is a based path homotopy on the fixed doubled size.
    have hpath : ((p.toFiniteMatrixLoop.stabilize n).loop).Homotopic
        q.toFiniteMatrixLoop.loop := by
      refine ⟨{ toFun := fun st ↦ G (st.1, Circle.exp (2 * Real.pi * (st.2 : ℝ)))
                continuous_toFun := hG.comp (continuous_fst.prodMk (by fun_prop))
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        exact hGzero _
      · intro t
        apply Units.ext
        exact (hqeval _).symm
      · intro s t ht
        rcases ht with ht | ht
        · subst t
          change G (s, Circle.exp (2 * Real.pi * (0 : ℝ))) =
            matrixUnitBlockSum ((p.invertible (Circle.exp (2 * Real.pi * (0 : ℝ)))).unit)
              (1 : Bˣ)
          simpa only [mul_zero, Circle.exp_zero] using (hbase s).trans hDone.symm
        · have ht' : t = 1 := ht
          subst t
          change G (s, Circle.exp (2 * Real.pi * (1 : ℝ))) =
            matrixUnitBlockSum ((p.invertible (Circle.exp (2 * Real.pi * (1 : ℝ)))).unit)
              (1 : Bˣ)
          simpa only [mul_one, Circle.exp_two_pi] using (hbase s).trans hDone.symm
    -- Descend this based homotopy using precisely the existing identity stabilization.
    have hstabZero (v : FiniteMatrixLoop A) : (v.stabilize 0).loop = v.loop := by
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
    refine ⟨q, hqNeg, hqBound, ?_⟩
    change stableMatrixLoopClass p.toFiniteMatrixLoop = stableMatrixLoopClass q.toFiniteMatrixLoop
    rw [← stableMatrixLoopClass_stabilize p.toFiniteMatrixLoop n]
    apply (stableMatrixLoopClass_eq_iff _ _).mpr
    refine ⟨0, 0, rfl, ?_⟩
    change Path.Homotopic ((p.toFiniteMatrixLoop.stabilize n).stabilize 0).loop
      (q.toFiniteMatrixLoop.stabilize 0).loop
    rw [hstabZero, hstabZero]
    exact hpath
  -- Strong induction lowers the degree while allowing the certified matrix size to grow.
  have induction_step : ∀ d : ℕ, ∀ p : LaurentMatrixLoop A, p.IsPolynomial →
      (∀ j : ℤ, (d : ℤ) < j → p.polynomial.coeff j = 0) →
      ∃ (n : ℕ) (a₀ a₁ : Matrix (Fin n) (Fin n) A)
        (hnorm : a₀ + a₁ = 1) (hunit : ∀ z : Circle, IsUnit (a₀ + (z : ℂ) • a₁)),
        p.stableClass = (LaurentMatrixLoop.affine a₀ a₁ hnorm hunit).stableClass := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hp hbound
      by_cases hd : d ≤ 1
      · -- Degrees zero and one give the original two coefficients as the affine witness.
        have hupper (j : ℤ) (hj : 1 < j) : p.polynomial.coeff j = 0 :=
          hbound j (by omega)
        have hpoly := eq_affine_of_degree_le_one p.polynomial hp hupper
        have heval := value_affine_of_degree_le_one p.polynomial hp hupper
        have hnorm : p.polynomial.coeff 0 + p.polynomial.coeff 1 = 1 := by
          simpa using (heval 1).symm.trans p.normalized
        have hunit (z : Circle) : IsUnit
            (p.polynomial.coeff 0 + (z : ℂ) • p.polynomial.coeff 1) :=
          (heval z) ▸ p.invertible z
        refine ⟨p.size, p.polynomial.coeff 0, p.polynomial.coeff 1, hnorm, hunit, ?_⟩
        apply congrArg LaurentMatrixLoop.stableClass
        cases p with
        | mk size polynomial normalized invertible =>
          change LaurentMatrixLoop.mk size polynomial normalized invertible =
            LaurentMatrixLoop.mk size _ _ _
          congr 1
      · -- The exact normalized endpoint supplies the next polynomial loop.
        obtain ⟨q, hq, hqbound, hclass⟩ :=
          reduce_degree p hp d (by omega) hbound
        obtain ⟨n, a₀, a₁, hnorm, hunit, hqclass⟩ := ih (d - 1) (by omega) q hq hqbound
        exact ⟨n, a₀, a₁, hnorm, hunit, hclass.trans hqclass⟩
  obtain ⟨d, hbound⟩ := exists_degree_bound p.polynomial
  exact induction_step d p hp hbound

end LaurentMatrixLoop

end AtiyahSinger
