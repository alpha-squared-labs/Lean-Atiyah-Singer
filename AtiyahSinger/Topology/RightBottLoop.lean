/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BottLoop
public import AtiyahSinger.Topology.RightKZeroComparison

/-!
# The Bott loop map for finite projective right modules

Public module ID: M2107.

A finite idempotent p over a possibly noncommutative complex normed
algebra defines the actual loop z*p+(1-p). Matrix multiplication acts on
columns from the left; the image is a right module, expressed as a left
module over the opposite algebra. The matrices and their products are not
transposed. Their explicit inverses use z inverse and the same p.

The original FiniteMatrixLoop and StableMatrixLoopClass are reused, with
their positive Circle.exp(2*pi*t) parameter and identity-block stabilization.
The right-projective Grothendieck universal property supplies the specified
homomorphism, without assuming a Bott inverse or surjectivity. Completeness
is unnecessary. For commutative coefficients the same-matrix comparison
intertwines this map with the existing map; this retains the geometric
comparison for C(X, complex) without choosing a different Bott generator.

Sources: Karoubi, K-Theory, III.1.9--1.10, pp.114--115; I.7.7 for the
stabilized conjugacy argument used in projective-presentation independence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RightKTheory

open scoped unitInterval

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

/-- The original complementary idempotents give both ordered matrix inverse equations. -/
theorem bottMatrix_inverse (p : IdempotentMatrix A) (z : Circle) :
    ((z : ℂ) • p.matrix + (1 - p.matrix)) *
        ((↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix)) = 1 ∧
      ((↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix)) *
        ((z : ℂ) • p.matrix + (1 - p.matrix)) = 1 := by
  /- Stage 1: p²=p gives the complementary idempotent 1-p and both
  equations p(1-p)=0 and (1-p)p=0. Complex scalars act centrally in A.
  Stage 2: distribute each product in its original order. The mixed terms
  vanish; the remaining terms are p and 1-p because z is invertible on
  the circle. No two general coefficients of A are interchanged. The
  calculation also includes the zero ring and the empty matrix algebra. -/
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

/-- The explicit Bott unit of the original idempotent, with the specified inverse. -/
def bottMatrixUnit (p : IdempotentMatrix A) (z : Circle) :
    (Matrix (Fin p.size) (Fin p.size) A)ˣ where
  val := (z : ℂ) • p.matrix + (1 - p.matrix)
  inv := (↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix)
  val_inv := (bottMatrix_inverse p z).1
  inv_val := (bottMatrix_inverse p z).2

/-- Both the actual Bott matrix and its explicit inverse depend continuously on z. -/
theorem continuous_bottMatrixUnit (p : IdempotentMatrix A) :
    Continuous (bottMatrixUnit p) := by
  /- Scalar multiplication, addition, the circle inclusion and inversion
  on the circle are continuous. Apply these facts to the two displayed
  formulas and use the matrix-unit topology, which records both values
  and inverses. No Banach-algebra inversion theorem or completeness is used. -/
  -- The topology of units retains both the value and its displayed inverse.
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun z : Circle ↦ (z : ℂ) • p.matrix + (1 - p.matrix))
    fun_prop
  · change Continuous (fun z : Circle ↦ (↑(z⁻¹) : ℂ) • p.matrix + (1 - p.matrix))
    fun_prop

/-- The specified Bott unit is the identity at the circle base point. -/
theorem bottMatrixUnit_one (p : IdempotentMatrix A) : bottMatrixUnit p 1 = 1 := by
  /- At z=1 the displayed matrix is p+(1-p)=1. Equality of the values
  gives equality of units, retaining the same inverse and matrix size. -/
  -- The same two complementary summands add to one; unit equality uses their values.
  apply Units.ext
  change (↑(1 : Circle) : ℂ) • p.matrix + (1 - p.matrix) = 1
  simp

/-- The original positive circle parameter gives a based path of these same units. -/
def bottMatrixPath (p : IdempotentMatrix A) :
    Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 where
  toFun t := bottMatrixUnit p (Circle.exp (2 * Real.pi * (t : ℝ)))
  continuous_toFun := (continuous_bottMatrixUnit p).comp (by fun_prop)
  source' := by simpa using bottMatrixUnit_one p
  target' := by simpa using bottMatrixUnit_one p

/-- The Bott path as an existing finite matrix loop, with its original ambient size. -/
def bottMatrixLoop (p : IdempotentMatrix A) : FiniteMatrixLoop A where
  size := p.size
  loop := bottMatrixPath p

/-- The class of the actual loop in the existing stable based-homotopy quotient. -/
def bottMatrixLoopClass (p : IdempotentMatrix A) : StableMatrixLoopClass A :=
  stableMatrixLoopClass (bottMatrixLoop p)

/-- KA III.1.10: isomorphic finite projective right modules give the same Bott loop class. -/
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

/-- Direct sum of the original right projective presentations becomes loop addition. -/
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

/-- The Bott homomorphism on the actual Grothendieck group of finite projective right modules. -/
def kZeroBottLoop (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] :
    KZero A →+ StableMatrixLoopClass A :=
  Classical.choose (kZero_universal_property bottMatrixLoopClass
    bottMatrixLoopClass_eq_of_isEquivalent bottMatrixLoopClass_blockSum).exists

/-- This homomorphism takes each original idempotent class to its specified positive loop. -/
theorem kZeroBottLoop_class (p : IdempotentMatrix A) :
    kZeroBottLoop A (kZeroClass A p) = bottMatrixLoopClass p := by
  -- Evaluate the generator specification of the same chosen universal map.
  exact Classical.choose_spec (kZero_universal_property bottMatrixLoopClass
    bottMatrixLoopClass_eq_of_isEquivalent bottMatrixLoopClass_blockSum).exists p

section CommutativeComparison

variable {R : Type u} [NormedCommRing R] [NormedAlgebra ℂ R]

/-- The same-matrix commutative comparison retains the original finite Bott loop class. -/
theorem bottMatrixLoopClass_toComm (p : IdempotentMatrix R) :
    bottMatrixLoopClass p = AtiyahSinger.bottMatrixLoopClass p.toComm := by
  -- Both constructions retain the identical size, entries, inverses and circle parameter.
  rfl

/-- The right-projective Bott homomorphism equals the commutative map after its comparison. -/
theorem kZeroBottLoop_eq_comm :
    kZeroBottLoop R = (AtiyahSinger.kZeroBottLoop R).comp
      (commKZeroEquiv R).toAddMonoidHom := by
  -- The two homomorphisms agree on the original finite idempotent generators.
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro p
  change kZeroBottLoop R (kZeroClass R p) =
    AtiyahSinger.kZeroBottLoop R (commKZeroEquiv R (kZeroClass R p))
  rw [kZeroBottLoop_class, commKZeroEquiv_class, AtiyahSinger.kZeroBottLoop_class]
  exact bottMatrixLoopClass_toComm p

end CommutativeComparison

end AtiyahSinger.RightKTheory
