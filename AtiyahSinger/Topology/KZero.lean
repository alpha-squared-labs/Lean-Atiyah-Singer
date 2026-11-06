/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# K₀ in the finite projective module model

Public module ID: M1920.

K₀(R) is presented by finite idempotent matrices,
modulo isomorphism of their image modules and the direct-sum relation. This is the
standard Grothendieck group of finite projective modules. No Bott isomorphism or index
identity is included in its definition. The comparison with topological vector bundles
over compact Hausdorff X is a separate topological Serre-Swan result.
Relative K-groups, compact supports, products and equivariance are not supplied here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable (R : Type u) [CommRing R]

/-- A finite idempotent matrix presents a finitely generated projective module. -/
structure IdempotentMatrix where
  /-- Dimension of the ambient finite free module, not the rank of the image. -/
  size : ℕ
  /-- The projection matrix; it need not be self-adjoint. -/
  matrix : Matrix (Fin size) (Fin size) R
  /-- The algebraic projection identity. -/
  mul_self : matrix * matrix = matrix

namespace IdempotentMatrix

variable {R}

/-- The image module of the specified idempotent. -/
def image (p : IdempotentMatrix R) : Submodule R (Fin p.size → R) :=
  p.matrix.mulVecLin.range

/-- The standard rectangular-matrix equivalence of finite idempotents. -/
def IsEquivalent (p q : IdempotentMatrix R) : Prop :=
  ∃ a : Matrix (Fin p.size) (Fin q.size) R,
    ∃ b : Matrix (Fin q.size) (Fin p.size) R,
      a * b = p.matrix ∧ b * a = q.matrix ∧ p.matrix * a = a ∧ q.matrix * b = b

/-- The concrete block-diagonal matrix, reindexed by Fin(size(p)+size(q)). -/
def blockMatrix (p q : IdempotentMatrix R) :
    Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.matrix 0 0 q.matrix)

/-- The block matrix is idempotent. -/
theorem blockMatrix_mul_self (p q : IdempotentMatrix R) :
    blockMatrix p q * blockMatrix p q = blockMatrix p q := by
  /- Block multiplication has diagonal entries p² and q² and zero off-diagonal entries.
  Substitute their idempotent identities and transport through the finite-index equivalence. -/
  simp [blockMatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, p.mul_self, q.mul_self]

/-- Direct sum of finite projective presentations. -/
def blockSum (p q : IdempotentMatrix R) : IdempotentMatrix R where
  size := p.size + q.size
  matrix := blockMatrix p q
  mul_self := blockMatrix_mul_self p q

/-- The image of an idempotent finite matrix is a finite module. -/
theorem finite_image (p : IdempotentMatrix R) : Module.Finite R p.image := by
  /- The images of the finitely many standard basis vectors generate the image. -/
  exact Module.Finite.range p.matrix.mulVecLin

/-- The image of an idempotent finite matrix is projective. -/
theorem projective_image (p : IdempotentMatrix R) : Module.Projective R p.image := by
  /- The idempotent retracts the finite free module onto its original image.
  A retract of a projective free module is projective. -/
  -- The original matrix retracts its ambient free module onto its actual range.
  apply Module.Projective.of_split p.image.subtype p.matrix.mulVecLin.rangeRestrict
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change p.matrix.mulVecLin (x : Fin p.size → R) = x
  rw [← hy, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, p.mul_self]

/-- Rectangular equivalence means exactly isomorphism of the presented modules. -/
theorem isEquivalent_iff_nonempty_linearEquiv (p q : IdempotentMatrix R) :
    p.IsEquivalent q ↔ Nonempty (p.image ≃ₗ[R] q.image) := by
  /- The rectangular matrices restrict to mutually inverse maps of the images.
  Conversely, extend a module isomorphism and its inverse by the two projections.
  The resulting matrices satisfy all four displayed identities. -/
  -- Each specified projection fixes every element of its original image.
  have hfix (r : IdempotentMatrix R) (x : r.image) :
      r.matrix.mulVecLin (x : Fin r.size → R) = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, r.mul_self]
  have hrestrict (r : IdempotentMatrix R) (x : r.image) :
      r.matrix.mulVecLin.rangeRestrict (x : Fin r.size → R) = x :=
    Subtype.ext (hfix r x)
  constructor
  · rintro ⟨a, b, hab, hba, hpa, hqb⟩
    -- Left multiplication by b and a restricts to the two specified images.
    let f : p.image →ₗ[R] q.image :=
      (b.mulVecLin.comp p.image.subtype).codRestrict q.image fun x ↦
        ⟨b.mulVecLin x, by
          change q.matrix.mulVecLin (b.mulVecLin x) = b.mulVecLin x
          rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hqb]⟩
    let g : q.image →ₗ[R] p.image :=
      (a.mulVecLin.comp q.image.subtype).codRestrict p.image fun x ↦
        ⟨a.mulVecLin x, by
          change p.matrix.mulVecLin (a.mulVecLin x) = a.mulVecLin x
          rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hpa]⟩
    refine ⟨{ f with invFun := g, left_inv := ?_, right_inv := ?_ }⟩
    · intro x
      apply Subtype.ext
      change a.mulVecLin (b.mulVecLin x) = x
      rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hab]
      exact hfix p x
    · intro x
      apply Subtype.ext
      change b.mulVecLin (a.mulVecLin x) = x
      rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hba]
      exact hfix q x
  · rintro ⟨e⟩
    -- Extend the given isomorphism and its inverse using the original projections.
    let a : (Fin q.size → R) →ₗ[R] (Fin p.size → R) :=
      p.image.subtype.comp (e.symm.toLinearMap.comp q.matrix.mulVecLin.rangeRestrict)
    let b : (Fin p.size → R) →ₗ[R] (Fin q.size → R) :=
      q.image.subtype.comp (e.toLinearMap.comp p.matrix.mulVecLin.rangeRestrict)
    refine ⟨LinearMap.toMatrix' a, LinearMap.toMatrix' b, ?_, ?_, ?_, ?_⟩
    · apply Matrix.toLin'.injective
      simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      apply LinearMap.ext
      intro x
      change (e.symm (q.matrix.mulVecLin.rangeRestrict (e
        (p.matrix.mulVecLin.rangeRestrict x)))).val = p.matrix.mulVecLin x
      rw [hrestrict]
      exact congrArg Subtype.val (e.symm_apply_apply _)
    · apply Matrix.toLin'.injective
      simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      apply LinearMap.ext
      intro x
      change (e (p.matrix.mulVecLin.rangeRestrict (e.symm
        (q.matrix.mulVecLin.rangeRestrict x)))).val = q.matrix.mulVecLin x
      rw [hrestrict]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    · apply Matrix.toLin'.injective
      simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      apply LinearMap.ext
      intro x
      exact hfix p (e.symm (q.matrix.mulVecLin.rangeRestrict x))
    · apply Matrix.toLin'.injective
      simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      apply LinearMap.ext
      intro x
      exact hfix q (e (p.matrix.mulVecLin.rangeRestrict x))

end IdempotentMatrix

/-- every finite projective module is the image of a finite idempotent matrix. -/
theorem exists_idempotentMatrix_of_finite_projective (P : Type*) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] :
    ∃ p : IdempotentMatrix R, Nonempty (p.image ≃ₗ[R] P) := by
  /- Choose a surjection from a finite free module onto P using finite generation.
  Projectivity splits it. The composite of the splitting and the surjection is an
  idempotent endomorphism of the finite free module; its matrix has image isomorphic to P. -/
  -- Finite generation gives a finite free cover; projectivity splits that same cover.
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  have hfg_apply (x : P) : f (g x) = x := DFunLike.congr_fun hfg x
  let L : (Fin n → R) →ₗ[R] (Fin n → R) := g.comp f
  have hL : L.comp L = L := by
    apply LinearMap.ext
    intro x
    change g (f (g (f x))) = g (f x)
    rw [hfg_apply]
  -- Read the split projection in the original standard coordinates.
  let p : IdempotentMatrix R := {
    size := n
    matrix := LinearMap.toMatrix' L
    mul_self := by rw [← LinearMap.toMatrix'_comp, hL] }
  have hp : p.matrix.mulVecLin = L := Matrix.toLin'_toMatrix' L
  have hfix (x : p.image) : g (f (x : Fin n → R)) = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy, hp]
    change g (f (g (f y))) = g (f y)
    rw [hfg_apply]
  -- Restrict the original cover to the image, where its section is a two-sided inverse.
  refine ⟨p, ⟨LinearEquiv.ofBijective (f.comp p.image.subtype) ⟨?_, ?_⟩⟩⟩
  · intro x y hxy
    apply Subtype.ext
    calc
      (x : Fin n → R) = g (f (x : Fin n → R)) := (hfix x).symm
      _ = g (f (y : Fin n → R)) := congrArg g hxy
      _ = y := hfix y
  · intro x
    refine ⟨p.matrix.mulVecLin.rangeRestrict (g x), ?_⟩
    change f (p.matrix.mulVecLin (g x)) = x
    rw [hp]
    change f (g (f (g x))) = x
    rw [hfg_apply, hfg_apply]

/-- The isomorphism and direct-sum relations in the free group of projective presentations. -/
def kZeroRelations : AddSubgroup (FreeAbelianGroup (IdempotentMatrix R)) :=
  AddSubgroup.closure
    ({x | ∃ p q : IdempotentMatrix R,
      p.IsEquivalent q ∧ x = FreeAbelianGroup.of p - FreeAbelianGroup.of q} ∪
    {x | ∃ p q : IdempotentMatrix R,
      x = FreeAbelianGroup.of (p.blockSum q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q})

/-- The ordinary algebraic K₀ group of a commutative ring in the idempotent model. -/
abbrev KZero : Type u :=
  FreeAbelianGroup (IdempotentMatrix R) ⧸ kZeroRelations R

/-- The K₀ class of a finite projective presentation. -/
def kZeroClass (p : IdempotentMatrix R) : KZero R :=
  QuotientAddGroup.mk' (kZeroRelations R) (FreeAbelianGroup.of p)

variable {R}

/-- Isomorphic image modules give the same K₀ class. -/
theorem kZeroClass_eq_of_isEquivalent (p q : IdempotentMatrix R) (h : p.IsEquivalent q) :
    kZeroClass R p = kZeroClass R q := by
  /- Their difference is a generator of the relation subgroup and hence vanishes in the quotient. -/
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.subset_closure
  exact Or.inl ⟨p, q, h, rfl⟩

/-- Direct sum becomes addition in K₀. -/
theorem kZeroClass_blockSum (p q : IdempotentMatrix R) :
    kZeroClass R (p.blockSum q) = kZeroClass R p + kZeroClass R q := by
  /- The difference between the two sides is one of the defining direct-sum relations. -/
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' (kZeroRelations R)) _ -
    ((QuotientAddGroup.mk' (kZeroRelations R)) _ +
      (QuotientAddGroup.mk' (kZeroRelations R)) _) = 0
  rw [← map_add, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  right
  exact ⟨p, q, by abel⟩

/-- the defining universal property of the Grothendieck group. -/
theorem kZero_universal_property {A : Type*} [AddCommGroup A]
    (v : IdempotentMatrix R → A)
    (hiso : ∀ p q, p.IsEquivalent q → v p = v q)
    (hadd : ∀ p q, v (p.blockSum q) = v p + v q) :
    ∃! φ : KZero R →+ A, ∀ p, φ (kZeroClass R p) = v p := by
  /- Extend v to the free abelian group. The two assumptions kill each relation
  generator, hence the generated subgroup. Descend through the quotient.
  Uniqueness follows because the classes of finite idempotents generate K₀. -/
  -- Extend the assignment to the free group and kill each original relation.
  let f : FreeAbelianGroup (IdempotentMatrix R) →+ A := FreeAbelianGroup.lift v
  have hrelations : kZeroRelations R ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x (⟨p, q, hpq, rfl⟩ | ⟨p, q, rfl⟩)
    · change f (_ - _) = 0
      simp [f, hiso p q hpq]
    · change f (_ - _ - _) = 0
      simp [f, hadd p q]
  -- Descend the same homomorphism through the stated quotient.
  let φ : KZero R →+ A := QuotientAddGroup.lift (kZeroRelations R) f hrelations
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

/-- The standard finite-projective model for absolute complex K⁰ of a compact Hausdorff space.
Its equivalence to the geometric bundle definition is not asserted by this abbreviation. -/
abbrev ComplexKZero (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] : Type _ :=
  KZero C(X, ℂ)

end AtiyahSinger
