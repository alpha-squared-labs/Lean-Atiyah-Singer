/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KZero
public import AtiyahSinger.Topology.StableMatrixLoop
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Bott loop of a finite projective module

Public module ID: M1568.

KR03: a finite idempotent p gives the concrete based invertible loop
z ↦ z • p + (1 - p). Its inverse is z⁻¹ • p + (1 - p). The stable homotopy
class depends only on the image module and is additive for direct sums, so the
existing Grothendieck universal property gives a specified homomorphism from K₀.

Source: Karoubi, K-Theory, III.1.9 and Proposition 1.10, pp.114–115. We use
the positively oriented parameter z=exp(2πit) on the unit circle. The source
allows noncommutative unital complex Banach algebras; the current K₀ model
requires commutativity. Completeness is unnecessary for this construction.
Neither Bott periodicity nor the comparison with the relative clutching class
is asserted here. In particular, no sign comparison with bottLineClass is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

universe u

variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- The two complementary summands give the explicit inverse of the Bott matrix. -/
theorem bottMatrix_inverse (p : IdempotentMatrix A) (z : Circle) :
    ((z : ℂ) • p.matrix + (1 - p.matrix)) *
        ((↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix)) = 1 ∧
      ((↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix)) *
        ((z : ℂ) • p.matrix + (1 - p.matrix)) = 1 := by
  /- Stage 1: p²=p implies that p and 1-p are orthogonal idempotents whose
  sum is the identity. Complex scalars commute with both projections.
  Stage 2: expand each matrix product; the mixed terms vanish and the two
  remaining diagonal summands are p and 1-p, since z is a unit of the circle.
  This argument includes the empty matrix and does not use an operator norm. -/
  -- Separate the two complementary summands without commuting general coefficients.
  let q : Matrix (Fin p.size) (Fin p.size) A := 1 - p.matrix
  have hpp : p.matrix * p.matrix = p.matrix := p.mul_self
  have hqq : q * q = q := by
    dsimp only [q]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpp, sub_self, sub_zero]
  have hpq : p.matrix * q = 0 := by
    dsimp only [q]
    rw [mul_sub, mul_one, hpp, sub_self]
  have hqp : q * p.matrix = 0 := by
    dsimp only [q]
    rw [sub_mul, one_mul, hpp, sub_self]
  have hsum : p.matrix + q = 1 := by dsimp only [q]; abel
  -- The scalar inverse equations give both ordered matrix products, including size zero.
  have hprod (c d : ℂ) (hcd : c * d = 1) :
      (c • p.matrix + q) * (d • p.matrix + q) = 1 := by
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, hcd, one_smul, hpp,
      smul_mul_assoc, hpq, smul_zero, mul_smul_comm, hqp, smul_zero, hqq,
      add_zero, zero_add, hsum]
  constructor
  · exact hprod _ _ (by simp)
  · exact hprod _ _ (by simp)

/-- The actual Bott matrix unit, with its explicit complementary-projection inverse. -/
def bottMatrixUnit (p : IdempotentMatrix A) (z : Circle) :
    (Matrix (Fin p.size) (Fin p.size) A)ˣ where
  val := (z : ℂ) • p.matrix + (1 - p.matrix)
  inv := (↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix)
  val_inv := (bottMatrix_inverse p z).1
  inv_val := (bottMatrix_inverse p z).2

/-- The explicit matrix and inverse vary continuously on the unit circle. -/
theorem continuous_bottMatrixUnit (p : IdempotentMatrix A) :
    Continuous (bottMatrixUnit p) := by
  /- Stage 1: multiplication of a fixed matrix by a complex scalar is continuous,
  as are addition and the unit-circle inclusion and inversion.
  Stage 2: use the topology of matrix units, which records both the matrix and
  its inverse. The displayed inverse varies continuously by the same formula. -/
  -- The topology of units retains both the value and its displayed inverse.
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun z : Circle ↦ (z : ℂ) • p.matrix + (1 - p.matrix))
    fun_prop
  · change Continuous (fun z : Circle ↦ (↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix))
    fun_prop

/-- The circle base point acts as the identity on both complementary summands. -/
theorem bottMatrixUnit_one (p : IdempotentMatrix A) : bottMatrixUnit p 1 = 1 := by
  /- At z=1 the two complementary projections sum to the identity. Equality
  of units follows from equality of their underlying matrices. -/
  -- The same two complementary summands add to one; unit equality uses their values.
  apply Units.ext
  change (↑(1 : Circle) : ℂ) • p.matrix + (1 - p.matrix) = 1
  simp

/-- The positively oriented Bott path, based at the identity at both endpoints. -/
def bottMatrixPath (p : IdempotentMatrix A) :
    Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 where
  toFun t := bottMatrixUnit p (Circle.exp (2 * Real.pi * (t : ℝ)))
  continuous_toFun := (continuous_bottMatrixUnit p).comp (by fun_prop)
  source' := by simpa using bottMatrixUnit_one p
  target' := by simpa using bottMatrixUnit_one p

/-- The finite matrix loop of the displayed idempotent, with its actual ambient size. -/
def bottMatrixLoop (p : IdempotentMatrix A) : FiniteMatrixLoop A where
  size := p.size
  loop := bottMatrixPath p

/-- The stable based-homotopy class of the specified Bott loop. -/
def bottMatrixLoopClass (p : IdempotentMatrix A) : StableMatrixLoopClass A :=
  stableMatrixLoopClass (bottMatrixLoop p)

/-- Karoubi III.1.10: the loop class depends only on the presented projective module. -/
theorem bottMatrixLoopClass_eq_of_isEquivalent (p q : IdempotentMatrix A)
    (h : p.IsEquivalent q) : bottMatrixLoopClass p = bottMatrixLoopClass q := by
  obtain ⟨a, b, hab, hba, hpa, hqb⟩ := h
  -- The original rectangular witnesses give a concrete involution exchanging the projections.
  have haq : a * q.matrix = a := by rw [← hba, ← Matrix.mul_assoc, hab, hpa]
  have hbp : b * p.matrix = b := by rw [← hab, ← Matrix.mul_assoc, hba, hqb]
  let S := Matrix.fromBlocks (1 - p.matrix) a b (1 - q.matrix)
  let P : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) A :=
    Matrix.fromBlocks p.matrix 0 0 0
  let Q : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) A :=
    Matrix.fromBlocks 0 0 0 q.matrix
  have hSS : S * S = 1 := by
    dsimp only [S]
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        p.mul_self, hab]
      abel
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hpa, haq]
      abel
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hbp, hqb]
      abel
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        q.mul_self, hba]
      abel
  have hconj : S * P * S = Q := by
    dsimp only [S, P, Q]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, p.mul_self,
      hbp, hba, sub_self]
  -- A single conjugation carries every value of the original scalar loop to the other loop.
  have hparam (z : ℂ) : S * (z • P + (1 - P)) * S = z • Q + (1 - Q) := by
    simp only [mul_add, mul_smul_comm, mul_sub, mul_one, add_mul, smul_mul_assoc,
      sub_mul, hSS, hconj]
  have hleft (z : ℂ) :
      Matrix.fromBlocks (z • p.matrix + (1 - p.matrix)) 0 0
        (1 : Matrix (Fin q.size) (Fin q.size) A) = z • P + (1 - P) := by
    ext i j
    cases i <;> cases j <;> simp [P, Matrix.one_apply]
  have hright (z : ℂ) :
      Matrix.fromBlocks (1 : Matrix (Fin p.size) (Fin p.size) A) 0 0
        (z • q.matrix + (1 - q.matrix)) = z • Q + (1 - Q) := by
    ext i j
    cases i <;> cases j <;> simp [Q, Matrix.one_apply]
  let E := Matrix.reindexRingEquiv A (finSumFinEquiv (m := p.size) (n := q.size))
  let U₀ : (Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) A)ˣ :=
    ⟨S, S, hSS, hSS⟩
  let U : (Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) A)ˣ :=
    Units.map E.toMonoidHom U₀
  have hU : ∀ t, matrixUnitBlockSum (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ)
        (bottMatrixPath q t) =
      U * matrixUnitBlockSum (bottMatrixPath p t)
        (1 : (Matrix (Fin q.size) (Fin q.size) A)ˣ) * U⁻¹ := by
    intro t
    apply Units.ext
    let z : ℂ := Circle.exp (2 * Real.pi * (t : ℝ))
    change E (Matrix.fromBlocks 1 0 0 (z • q.matrix + (1 - q.matrix))) =
      E S * E (Matrix.fromBlocks (z • p.matrix + (1 - p.matrix)) 0 0 1) * E S
    rw [← map_mul, ← map_mul, hleft, hright, hparam]
  -- Identity loops in arbitrary ambient size represent the original zero-size class.
  have hzero (n : ℕ) :
      stableMatrixLoopClass (FiniteMatrixLoop.constant (A := A) n) = 0 := by
    change stableMatrixLoopClass (FiniteMatrixLoop.constant (A := A) n) =
      stableMatrixLoopClass (FiniteMatrixLoop.constant 0)
    apply (stableMatrixLoopClass_eq_iff _ _).mpr
    have hc (n k : ℕ) : ((FiniteMatrixLoop.constant (A := A) n).stabilize k).loop =
        Path.refl 1 := by
      apply Path.ext
      funext t
      apply Units.ext
      change (matrixUnitBlockSum (1 : (Matrix (Fin n) (Fin n) A)ˣ)
        (1 : (Matrix (Fin k) (Fin k) A)ˣ) : Matrix (Fin (n + k)) (Fin (n + k)) A) = 1
      simp [matrixUnitBlockSum]
    refine ⟨0, n, show n + 0 = 0 + n by omega, ?_⟩
    rw [hc, hc]
    have hcast {n m : ℕ} (e : n = m) :
        cast (congrArg (fun d : ℕ ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) e)
          (Path.refl 1) = Path.refl 1 := by subst m; rfl
    erw [hcast (show n + 0 = 0 + n by omega)]
    exact Path.Homotopic.refl _
  -- Use the proved stable conjugacy, then descend the same representatives.
  have hrel : ((bottMatrixLoop p).stabilize q.size).StablyHomotopic
      ((FiniteMatrixLoop.constant p.size).blockSum (bottMatrixLoop q)) :=
    FiniteMatrixLoop.stablyHomotopic_of_conjugate _ _ U hU
  change stableMatrixLoopClass (bottMatrixLoop p) =
    stableMatrixLoopClass (bottMatrixLoop q)
  calc
    stableMatrixLoopClass (bottMatrixLoop p) =
        stableMatrixLoopClass ((bottMatrixLoop p).stabilize q.size) :=
      (stableMatrixLoopClass_stabilize _ _).symm
    _ = stableMatrixLoopClass
        ((FiniteMatrixLoop.constant p.size).blockSum (bottMatrixLoop q)) :=
      (stableMatrixLoopClass_eq_iff _ _).mpr hrel
    _ = stableMatrixLoopClass (FiniteMatrixLoop.constant p.size) +
        stableMatrixLoopClass (bottMatrixLoop q) := stableMatrixLoopClass_blockSum _ _
    _ = stableMatrixLoopClass (bottMatrixLoop q) := by rw [hzero, zero_add]

/-- Karoubi III.1.10: direct sum of projective modules becomes stable loop addition. -/
theorem bottMatrixLoopClass_blockSum (p q : IdempotentMatrix A) :
    bottMatrixLoopClass (p.blockSum q) = bottMatrixLoopClass p + bottMatrixLoopClass q := by
  -- Identify the original finite loop, using the common ordered block coordinates.
  change stableMatrixLoopClass (bottMatrixLoop (p.blockSum q)) =
    stableMatrixLoopClass (bottMatrixLoop p) + stableMatrixLoopClass (bottMatrixLoop q)
  rw [← stableMatrixLoopClass_blockSum]
  apply congrArg stableMatrixLoopClass
  change FiniteMatrixLoop.mk (p.size + q.size) _ = FiniteMatrixLoop.mk (p.size + q.size) _
  congr 1
  apply Path.ext
  funext t
  apply Units.ext
  let z : ℂ := Circle.exp (2 * Real.pi * (t : ℝ))
  change z • Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks p.matrix 0 0 q.matrix) +
      ((1 : Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) A) -
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks p.matrix 0 0 q.matrix)) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (z • p.matrix + (1 - p.matrix)) 0 0
        (z • q.matrix + (1 - q.matrix)))
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [Matrix.reindex_apply, Matrix.one_apply]
  -- The two off-diagonal identity entries vanish because their finite blocks are disjoint.
  all_goals
    intro h
    have he := congrArg Fin.val h
    simp at he
    omega

/-- The Bott homomorphism, specified on every finite-projective generator. -/
def kZeroBottLoop (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] :
    KZero A →+ StableMatrixLoopClass A :=
  Classical.choose (kZero_universal_property bottMatrixLoopClass
    bottMatrixLoopClass_eq_of_isEquivalent bottMatrixLoopClass_blockSum).exists

/-- The Bott homomorphism sends a projective class to its concrete scalar loop. -/
theorem kZeroBottLoop_class (p : IdempotentMatrix A) :
    kZeroBottLoop A (kZeroClass A p) = bottMatrixLoopClass p := by
  -- Evaluate the generator specification of the same chosen universal map.
  exact Classical.choose_spec (kZero_universal_property bottMatrixLoopClass
    bottMatrixLoopClass_eq_of_isEquivalent bottMatrixLoopClass_blockSum).exists p

end AtiyahSinger
