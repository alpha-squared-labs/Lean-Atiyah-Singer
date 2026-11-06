/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Matrix.Block
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# K₀ of finitely generated projective right modules over a ring

Public module ID: M2109.

Finite idempotent matrices present right modules through their actual
left action on columns. The scalar action on those columns is right multiplication,
expressed as a left module over Rᵐᵒᵖ. Matrix multiplication retains its original
order. No commutativity, norm, topology, involution or self-adjointness is assumed.

The group is the free abelian group on these finite presentations modulo the
rectangular-isomorphism and block-sum relations. Arbitrary finite projective
right modules admit such a presentation, including modules in an independent
universe. This small presentation avoids forming a quotient of all module types.
The comparison with commutative KZero uses the same finite matrices.

Sources: Karoubi, K-Theory, I.6.16 and III.1.5, 1.9--1.10, for the finite-projective
K₀ presentation and the domain of the Bott loop homomorphism; II.3.10, p.74,
for the right-module convention. These definitions impose no Bott or index identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RightKTheory

open scoped BigOperators Matrix

universe u v

variable (R : Type u) [Ring R]

/-- A finite idempotent matrix presenting its actual right image module. -/
structure IdempotentMatrix where
  /-- The dimension of the ambient free module, not the rank of the image. -/
  size : ℕ
  /-- The original matrix, acting on column vectors from the left. -/
  matrix : Matrix (Fin size) (Fin size) R
  /-- Its algebraic projection identity. -/
  mul_self : matrix * matrix = matrix

namespace IdempotentMatrix

variable {R}

/-- The actual image of left matrix multiplication, with its right scalar action. -/
def image (p : IdempotentMatrix R) : Submodule Rᵐᵒᵖ (Fin p.size → R) :=
  (Matrix.mulVecBilin R Rᵐᵒᵖ p.matrix).range

/-- Rectangular equivalence of finite projective presentations over the original ring. -/
def IsEquivalent (p q : IdempotentMatrix R) : Prop :=
  ∃ a : Matrix (Fin p.size) (Fin q.size) R,
    ∃ b : Matrix (Fin q.size) (Fin p.size) R,
      a * b = p.matrix ∧ b * a = q.matrix ∧ p.matrix * a = a ∧ q.matrix * b = b

/-- The original block-diagonal matrix with the standard finite-index reindexing. -/
def blockMatrix (p q : IdempotentMatrix R) :
    Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.matrix 0 0 q.matrix)

/-- The block matrix is idempotent without commuting any coefficients. -/
theorem blockMatrix_mul_self (p q : IdempotentMatrix R) :
    blockMatrix p q * blockMatrix p q = blockMatrix p q := by
  /- Multiply the four blocks in their original order. The diagonal blocks
  are p squared and q squared, and the off-diagonal blocks are zero.
  Substitute the two given idempotent identities and reindex by the same
  finSumFinEquiv. This certificate supplies the blockSum construction. -/
  simp [blockMatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, p.mul_self, q.mul_self]

/-- Direct sum of two right projective presentations. -/
def blockSum (p q : IdempotentMatrix R) : IdempotentMatrix R where
  size := p.size + q.size
  matrix := blockMatrix p q
  mul_self := blockMatrix_mul_self p q

/-- The identity matrix presents the free right module of the specified dimension. -/
def identity (R : Type u) [Ring R] (n : ℕ) : IdempotentMatrix R where
  size := n
  matrix := 1
  mul_self := one_mul 1

/-- A finite idempotent image is finitely generated for the actual right action. -/
theorem finite_image (p : IdempotentMatrix R) : Module.Finite Rᵐᵒᵖ p.image := by
  /- Every vector is the sum of its standard basis columns multiplied by
  their coefficients on the right. Applying p gives the same finite set
  of projected columns as right generators of its image. The regular
  right module R is the regular left Rᵐᵒᵖ module through op; no basis
  cardinality theorem or nontriviality of R is needed. -/
  -- Unop identifies the regular left opposite-ring module with the original right module.
  let e : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R := {
    toFun := MulOpposite.unop
    invFun := MulOpposite.op
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  let : Module.Finite Rᵐᵒᵖ R := Module.Finite.equiv e
  exact Module.Finite.range (Matrix.mulVecBilin R Rᵐᵒᵖ p.matrix)

/-- A finite idempotent image is a projective right module. -/
theorem projective_image (p : IdempotentMatrix R) : Module.Projective Rᵐᵒᵖ p.image := by
  /- The original matrix gives a right-linear retraction from the finite
  free column module onto its image, with inclusion as section. Its
  restriction to the image is identity by p squared equals p. Apply
  projectivity of a retract of a free module over Rᵐᵒᵖ, using the actual
  right scalar action on every coefficient. -/
  -- Unop identifies the regular left opposite-ring module with the original right module.
  let e : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R := {
    toFun := MulOpposite.unop
    invFun := MulOpposite.op
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  let : Module.Free Rᵐᵒᵖ R := Module.Free.of_equiv e
  -- The projection retracts the actual free right column module onto its image.
  let L := Matrix.mulVecBilin R Rᵐᵒᵖ p.matrix
  apply Module.Projective.of_split p.image.subtype L.rangeRestrict
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change p.matrix *ᵥ (x : Fin p.size → R) = x
  rw [← hy]
  change p.matrix *ᵥ (p.matrix *ᵥ y) = p.matrix *ᵥ y
  rw [Matrix.mulVec_mulVec, p.mul_self]

/-- Rectangular equivalence is exactly isomorphism of the specified right image modules. -/
theorem isEquivalent_iff_nonempty_linearEquiv (p q : IdempotentMatrix R) :
    p.IsEquivalent q ↔ Nonempty (p.image ≃ₗ[Rᵐᵒᵖ] q.image) := by
  /- Stage 1: rectangular witnesses a and b act on the left, and hence
  are right-linear. The four identities restrict them to inverse maps
  between the original image modules; use b from p's image to q's image.
  Stage 2: extend an image isomorphism and its inverse by the two original
  projections. Reading these right-linear maps on standard columns gives
  matrices b and a with the same multiplication order and all four
  identities. No transpose or coefficient commutation is required. -/
  let L {m n : ℕ} (a : Matrix (Fin m) (Fin n) R) :
      (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin m → R) := Matrix.mulVecBilin R Rᵐᵒᵖ a
  have hmul {l m n : ℕ} (a : Matrix (Fin l) (Fin m) R)
      (b : Matrix (Fin m) (Fin n) R) : L (a * b) = (L a).comp (L b) :=
    LinearMap.ext fun x ↦ (Matrix.mulVec_mulVec x a b).symm
  have hinj {m n : ℕ} : Function.Injective (L (m := m) (n := n)) := by
    intro a b h
    apply Matrix.mulVec_injective
    exact congrArg (fun f : (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin m → R) ↦ (f : _ → _)) h
  -- Right-linearity reads a map from its standard columns without transposing coefficients.
  let M {m n : ℕ} (f : (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin m → R)) :
      Matrix (Fin m) (Fin n) R := fun i j ↦ f (Pi.single j 1) i
  have hread {m n : ℕ} (f : (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin m → R)) : L (M f) = f := by
    have hcol (x : Fin n → R) :
        x = ∑ j : Fin n, MulOpposite.op (x j) • Pi.single j (1 : R) := by
      ext i
      simp [Pi.smul_apply, Pi.single_apply]
    apply LinearMap.ext
    intro x
    ext i
    change (∑ j, f (Pi.single j 1) i * x j) = f x i
    conv_rhs => rw [hcol x]
    simp [map_sum]
  have hfix (r : IdempotentMatrix R) (x : r.image) : L r.matrix x = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    change (L r.matrix).comp (L r.matrix) y = L r.matrix y
    rw [← hmul, r.mul_self]
  have hrestrict (r : IdempotentMatrix R) (x : r.image) :
      (L r.matrix).rangeRestrict (x : Fin r.size → R) = x := Subtype.ext (hfix r x)
  constructor
  · rintro ⟨a, b, hab, hba, hpa, hqb⟩
    -- The original rectangular matrices restrict to the same two image modules.
    let f : p.image →ₗ[Rᵐᵒᵖ] q.image :=
      ((L b).comp p.image.subtype).codRestrict q.image fun x ↦
        ⟨L b x, by
          change (L q.matrix).comp (L b) x = L b x
          rw [← hmul, hqb]⟩
    let g : q.image →ₗ[Rᵐᵒᵖ] p.image :=
      ((L a).comp q.image.subtype).codRestrict p.image fun x ↦
        ⟨L a x, by
          change (L p.matrix).comp (L a) x = L a x
          rw [← hmul, hpa]⟩
    refine ⟨{ f with invFun := g, left_inv := ?_, right_inv := ?_ }⟩
    · intro x
      apply Subtype.ext
      change (L a).comp (L b) x = x
      rw [← hmul, hab]
      exact hfix p x
    · intro x
      apply Subtype.ext
      change (L b).comp (L a) x = x
      rw [← hmul, hba]
      exact hfix q x
  · rintro ⟨e⟩
    -- Extend the given right-linear isomorphism using the two actual projections.
    let a : (Fin q.size → R) →ₗ[Rᵐᵒᵖ] (Fin p.size → R) :=
      p.image.subtype.comp (e.symm.toLinearMap.comp (L q.matrix).rangeRestrict)
    let b : (Fin p.size → R) →ₗ[Rᵐᵒᵖ] (Fin q.size → R) :=
      q.image.subtype.comp (e.toLinearMap.comp (L p.matrix).rangeRestrict)
    refine ⟨M a, M b, ?_, ?_, ?_, ?_⟩
    · apply hinj
      rw [hmul, hread, hread]
      apply LinearMap.ext
      intro x
      change (e.symm ((L q.matrix).rangeRestrict (e
        ((L p.matrix).rangeRestrict x)))).val = L p.matrix x
      rw [hrestrict]
      exact congrArg Subtype.val (e.symm_apply_apply _)
    · apply hinj
      rw [hmul, hread, hread]
      apply LinearMap.ext
      intro x
      change (e ((L p.matrix).rangeRestrict (e.symm
        ((L q.matrix).rangeRestrict x)))).val = L q.matrix x
      rw [hrestrict]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    · apply hinj
      rw [hmul, hread]
      apply LinearMap.ext
      intro x
      exact hfix p (e.symm ((L q.matrix).rangeRestrict x))
    · apply hinj
      rw [hmul, hread]
      apply LinearMap.ext
      intro x
      exact hfix q (e ((L p.matrix).rangeRestrict x))

end IdempotentMatrix

/-- Every finite projective right module has an actual finite idempotent presentation. -/
theorem exists_idempotentMatrix_of_finite_projective (P : Type v) [AddCommGroup P]
    [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    ∃ p : IdempotentMatrix R, Nonempty (p.image ≃ₗ[Rᵐᵒᵖ] P) := by
  /- Stage 1: finite generation and projectivity supply a split surjection
  from a finite free left Rᵐᵒᵖ module onto P. Identify that free module
  with the original right column module by coefficientwise unop.
  Stage 2: compose the section with the surjection. Read this idempotent
  right-linear endomorphism on the standard columns to obtain a matrix
  over R acting on the left. Its actual image is isomorphic to P through
  the same splitting. The finite presentation lives in R's universe even
  when P has an independent larger universe. -/
  -- Start with a finite free split cover of P over Rᵐᵒᵖ, retaining P's independent universe.
  obtain ⟨n, f₀, g₀, _, _, hfg₀⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective Rᵐᵒᵖ P
  let c : (Fin n → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) := {
    toFun := fun x i ↦ MulOpposite.unop (x i)
    invFun := fun x i ↦ MulOpposite.op (x i)
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  let f : (Fin n → R) →ₗ[Rᵐᵒᵖ] P := f₀.comp c.symm.toLinearMap
  let g : P →ₗ[Rᵐᵒᵖ] (Fin n → R) := c.toLinearMap.comp g₀
  have hfg (x : P) : f (g x) = x := DFunLike.congr_fun hfg₀ x
  let H : (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin n → R) := g.comp f
  have hH : H.comp H = H := by
    apply LinearMap.ext
    intro x
    change g (f (g (f x))) = g (f x)
    rw [hfg]
  -- Read the right-linear split projection on standard columns in the original ring.
  let L (a : Matrix (Fin n) (Fin n) R) :
      (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin n → R) := Matrix.mulVecBilin R Rᵐᵒᵖ a
  let M (h : (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin n → R)) :
      Matrix (Fin n) (Fin n) R := fun i j ↦ h (Pi.single j 1) i
  have hread (h : (Fin n → R) →ₗ[Rᵐᵒᵖ] (Fin n → R)) : L (M h) = h := by
    have hcol (x : Fin n → R) :
        x = ∑ j : Fin n, MulOpposite.op (x j) • Pi.single j (1 : R) := by
      ext i
      simp [Pi.smul_apply, Pi.single_apply]
    apply LinearMap.ext
    intro x
    ext i
    change (∑ j, h (Pi.single j 1) i * x j) = h x i
    conv_rhs => rw [hcol x]
    simp [map_sum]
  let p : IdempotentMatrix R := {
    size := n
    matrix := M H
    mul_self := by
      apply Matrix.mulVec_injective
      funext x
      rw [← Matrix.mulVec_mulVec]
      change L (M H) (L (M H) x) = L (M H) x
      rw [hread]
      exact DFunLike.congr_fun hH x }
  have hp : L p.matrix = H := hread H
  have hfix (x : p.image) : g (f (x : Fin n → R)) = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    change g (f (L p.matrix y)) = L p.matrix y
    rw [hp]
    change g (f (g (f y))) = g (f y)
    rw [hfg]
  -- The same cover and section identify the actual matrix image with P.
  refine ⟨p, ⟨LinearEquiv.ofBijective (f.comp p.image.subtype) ⟨?_, ?_⟩⟩⟩
  · intro x y hxy
    apply Subtype.ext
    calc
      (x : Fin n → R) = g (f (x : Fin n → R)) := (hfix x).symm
      _ = g (f (y : Fin n → R)) := congrArg g hxy
      _ = y := hfix y
  · intro x
    refine ⟨(L p.matrix).rangeRestrict (g x), ?_⟩
    change f (L p.matrix (g x)) = x
    rw [hp]
    change f (g (f (g x))) = x
    rw [hfg, hfg]

/-- The isomorphism and direct-sum relations for finite right-projective presentations. -/
def kZeroRelations : AddSubgroup (FreeAbelianGroup (IdempotentMatrix R)) :=
  AddSubgroup.closure
    ({x | ∃ p q : IdempotentMatrix R,
      p.IsEquivalent q ∧ x = FreeAbelianGroup.of p - FreeAbelianGroup.of q} ∪
    {x | ∃ p q : IdempotentMatrix R,
      x = FreeAbelianGroup.of (p.blockSum q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q})

/-- The ordinary algebraic K₀ group of finite projective right modules over R. -/
abbrev KZero : Type u :=
  FreeAbelianGroup (IdempotentMatrix R) ⧸ kZeroRelations R

/-- The K₀ class of the actual finite right-projective presentation. -/
def kZeroClass (p : IdempotentMatrix R) : KZero R :=
  QuotientAddGroup.mk' (kZeroRelations R) (FreeAbelianGroup.of p)

variable {R}

/-- Isomorphic right image modules have the same K₀ class. -/
theorem kZeroClass_eq_of_isEquivalent (p q : IdempotentMatrix R) (h : p.IsEquivalent q) :
    kZeroClass R p = kZeroClass R q := by
  /- The difference of these two generators belongs to the defining
  isomorphism relations. Its image in the actual quotient is zero. -/
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.subset_closure
  exact Or.inl ⟨p, q, h, rfl⟩

/-- The block direct sum gives addition in the actual Grothendieck group. -/
theorem kZeroClass_blockSum (p q : IdempotentMatrix R) :
    kZeroClass R (p.blockSum q) = kZeroClass R p + kZeroClass R q := by
  /- The displayed block-sum difference is a generator of the relation
  subgroup. Apply the quotient map and rearrange in its additive group. -/
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' (kZeroRelations R)) _ -
    ((QuotientAddGroup.mk' (kZeroRelations R)) _ +
      (QuotientAddGroup.mk' (kZeroRelations R)) _) = 0
  rw [← map_add, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  right
  exact ⟨p, q, by abel⟩

/-- The defining universal property of K₀ for finite projective right modules. -/
theorem kZero_universal_property {B : Type*} [AddCommGroup B]
    (v : IdempotentMatrix R → B)
    (hiso : ∀ p q, p.IsEquivalent q → v p = v q)
    (hadd : ∀ p q, v (p.blockSum q) = v p + v q) :
    ∃! φ : KZero R →+ B, ∀ p, φ (kZeroClass R p) = v p := by
  /- Stage 1: extend v to the free abelian group on the same finite
  matrices. The two hypotheses send every defining relation to zero,
  and hence kill the subgroup they generate.
  Stage 2: descend this homomorphism to the displayed quotient. Its
  values on the original generators determine it uniquely, since those
  generators generate the free group and its quotient. -/
  -- Extend the assignment to the free group and kill each original relation.
  let f : FreeAbelianGroup (IdempotentMatrix R) →+ B := FreeAbelianGroup.lift v
  have hrelations : kZeroRelations R ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x (⟨p, q, hpq, rfl⟩ | ⟨p, q, rfl⟩)
    · change f (_ - _) = 0
      simp [f, hiso p q hpq]
    · change f (_ - _ - _) = 0
      simp [f, hadd p q]
  -- Descend the same homomorphism through the stated quotient.
  let φ : KZero R →+ B := QuotientAddGroup.lift (kZeroRelations R) f hrelations
  have hφ : ∀ p, φ (kZeroClass R p) = v p := by
    intro p
    exact FreeAbelianGroup.lift_apply_of v p
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  -- The quotient is generated by the images of the original free generators.
  have hcomp : ψ.comp (QuotientAddGroup.mk' (kZeroRelations R)) =
      φ.comp (QuotientAddGroup.mk' (kZeroRelations R)) := by
    apply FreeAbelianGroup.lift_ext
    intro p
    exact (hψ p).trans (hφ p).symm
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (kZeroRelations R) x
  exact DFunLike.congr_fun hcomp y

end AtiyahSinger.RightKTheory
