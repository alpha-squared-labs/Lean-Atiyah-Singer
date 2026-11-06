/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RealOrthogonalNormalForm
public import AtiyahSinger.Algebra.RepresentationCharacter
public import AtiyahSinger.Analysis.LowSphereHodgeIndex
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

import AtiyahSinger.Geometry.OrthogonalGroupManifold

/-!
# Orthogonal block subgroups detect virtual representations

Public module ID: M0044.

AR04: the representation-theoretic argument in Atiyah--Singer I,
Proposition (4.4), printed p.505. The standard subgroup is the actual block
matrix inclusion of `O(1)^a × SO(2)^b` into `O(a + b * 2)`. The first `a`
coordinates carry the real one-dimensional blocks; the remaining coordinates
are ordered by the pair `(j, k)`, with position `a + 2 * j + k`.

Every real orthogonal matrix is orthogonally conjugate to such a block matrix.
The normal-form statement explicitly transports the original matrix indices
by `Fin.cast` along the supplied dimension equality. Consequently restriction
along these very inclusions detects equality in the original representation
Grothendieck ring, by the character theorem for compact groups. Taking the
second class to be one gives the final representation-theoretic step of (4.4).

This does not construct the point Bott index or derive its restrictions from
excision, Bott multiplicativity, or the low-dimensional index computations.
Those remain additional AR04 obligations. The normal form is the standard
real spectral theorem expansion of the source's assertion that these block
subgroups, up to conjugacy, contain every cyclic subgroup. Zero dimension
and empty products of either block type are included. The block construction
and the real spectral normal form and character detection are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The standard ordered block matrix with real line blocks followed by rotation-plane blocks. -/
def orthogonalBlockMatrix (a b : ℕ)
    (g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
      (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) :
    Matrix (Fin (a + b * 2)) (Fin (a + b * 2)) ℝ :=
  let e : Fin (a + b * 2) ≃ Fin a ⊕ (Fin b × Fin 2) :=
    finSumFinEquiv.symm.trans ((Equiv.refl (Fin a)).sumCongr finProdFinEquiv.symm)
  fun i j ↦
    match e i, e j with
    | .inl k, .inl l => if k = l then (g.1 k).val 0 0 else 0
    | .inr (k, s), .inr (l, t) => if k = l then (g.2 k).val s t else 0
    | _, _ => 0

/-- Orthogonality, multiplication, and continuity certify this specified block construction. -/
theorem orthogonalBlockMatrix_properties (a b : ℕ) :
    (∀ g, orthogonalBlockMatrix a b g ∈ Matrix.orthogonalGroup (Fin (a + b * 2)) ℝ) ∧
      orthogonalBlockMatrix a b 1 = 1 ∧
      (∀ g h, orthogonalBlockMatrix a b (g * h) =
        orthogonalBlockMatrix a b g * orthogonalBlockMatrix a b h) ∧
      Continuous (orthogonalBlockMatrix a b) := by
  /- Stage 1: use the explicit ordered coordinate equivalence to separate
  the real line blocks from the ordered pairs of rotation-plane coordinates.
  In the product with the transpose, every mixed block is zero. Each diagonal
  block is the identity by its original O(1) or SO(2) membership, proving
  orthogonality of the same matrix, without selecting an abstract embedding.
  Stage 2: multiplication has the identical block calculation, with no
  interaction between different blocks. Identity input gives identity blocks,
  including when either finite index type is empty.
  Stage 3: each displayed matrix entry is either zero or an evaluation of
  one original matrix coordinate in one of the finite product factors.
  Those evaluations are continuous in the native subgroup and product
  topologies. Finite coordinatewise continuity gives the stated continuity. -/
  let e : Fin (a + b * 2) ≃ Fin a ⊕ (Fin b × Fin 2) :=
    finSumFinEquiv.symm.trans ((Equiv.refl (Fin a)).sumCongr finProdFinEquiv.symm)
  let L (g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
      (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) : Matrix (Fin a) (Fin a) ℝ :=
    Matrix.diagonal (fun k ↦ (g.1 k).val 0 0)
  let P (g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
      (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) :
      Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℝ :=
    (Matrix.blockDiagonal (fun k ↦ (g.2 k).val)).submatrix
      (Equiv.prodComm (Fin b) (Fin 2)) (Equiv.prodComm (Fin b) (Fin 2))
  have hformula (g) : orthogonalBlockMatrix a b g =
      (Matrix.fromBlocks (L g) 0 0 (P g)).submatrix e e := by
    ext i j
    change (match e i, e j with
      | .inl k, .inl l => if k = l then (g.1 k).val 0 0 else 0
      | .inr (k, s), .inr (l, t) => if k = l then (g.2 k).val s t else 0
      | _, _ => 0) = Matrix.fromBlocks (L g) 0 0 (P g) (e i) (e j)
    cases e i <;> cases e j <;> rfl
  -- In these exact coordinates, each original line and plane is orthogonal.
  have hL (g) : L g * (L g).transpose = 1 := by
    have hline (k : Fin a) : (g.1 k).val 0 0 * (g.1 k).val 0 0 = 1 := by
      have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ ↦ A 0 0)
        ((Matrix.mem_orthogonalGroup_iff (Fin 1) ℝ).mp (g.1 k).property)
      simpa [Matrix.mul_apply] using h
    simp [L, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, hline]
  have hP (g) : P g * (P g).transpose = 1 := by
    have hplane (k : Fin b) : (g.2 k).val * (g.2 k).val.transpose = 1 :=
      (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp (g.2 k).property.1
    simp only [P, Matrix.transpose_submatrix, Matrix.blockDiagonal_transpose,
      Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul, hplane]
    change (Matrix.blockDiagonal (1 : Fin b → Matrix (Fin 2) (Fin 2) ℝ)).submatrix
      (Equiv.prodComm (Fin b) (Fin 2)) (Equiv.prodComm (Fin b) (Fin 2)) = 1
    rw [Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rw [hformula]
    apply (Matrix.submatrix_equiv_mem_unitary (e₁ := e) (e₂ := e)).mpr
    apply (Matrix.mem_orthogonalGroup_iff _ ℝ).mpr
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      hL, hP]
  · rw [hformula]
    have hLone : L 1 = 1 := by simp [L]
    have hPone : P 1 = 1 := by
      change (Matrix.blockDiagonal (1 : Fin b → Matrix (Fin 2) (Fin 2) ℝ)).submatrix
        (Equiv.prodComm (Fin b) (Fin 2)) (Equiv.prodComm (Fin b) (Fin 2)) = 1
      rw [Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
    simp [hLone, hPone]
  · intro g h
    have hLmul : L (g * h) = L g * L h := by
      simp only [L, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      change (g.1 k * h.1 k).val 0 0 = (g.1 k).val 0 0 * (h.1 k).val 0 0
      simp [Matrix.mul_apply]
    have hPmul : P (g * h) = P g * P h := by
      change (Matrix.blockDiagonal (fun k ↦ (g.2 k).val * (h.2 k).val)).submatrix _ _ = _
      rw [Matrix.submatrix_mul_equiv, Matrix.blockDiagonal_mul]
    rw [hformula, hformula, hformula, Matrix.submatrix_mul_equiv]
    simp [Matrix.fromBlocks_multiply, hLmul, hPmul]
  · -- Only fixed matrix-coordinate evaluations occur, with the displayed block order.
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
        (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ) ↦ match e i, e j with
      | .inl k, .inl l => if k = l then (g.1 k).val 0 0 else 0
      | .inr (k, s), .inr (l, t) => if k = l then (g.2 k).val s t else 0
      | _, _ => 0)
    cases e i <;> cases e j
    · dsimp only
      split_ifs
      · have hval : Continuous (fun A : Matrix.orthogonalGroup (Fin 1) ℝ ↦
            (A.val : Matrix (Fin 1) (Fin 1) ℝ)) := continuous_subtype_val
        exact ((continuous_apply 0).comp ((continuous_apply 0).comp hval)).comp
          ((continuous_apply _).comp continuous_fst)
      · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · dsimp only
      split_ifs
      · have hval : Continuous (fun A : Matrix.specialOrthogonalGroup (Fin 2) ℝ ↦
            (A.val : Matrix (Fin 2) (Fin 2) ℝ)) := continuous_subtype_val
        exact ((continuous_apply _).comp ((continuous_apply _).comp hval)).comp
          ((continuous_apply _).comp continuous_snd)
      · exact continuous_const

/-- The actual standard continuous block inclusion `O(1)^a × SO(2)^b → O(a + 2b)`. -/
def orthogonalBlockInclusion (a b : ℕ) :
    ((Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
      (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) →ₜ*
        Matrix.orthogonalGroup (Fin (a + b * 2)) ℝ where
  toFun g := ⟨orthogonalBlockMatrix a b g, (orthogonalBlockMatrix_properties a b).1 g⟩
  map_one' := Subtype.ext (orthogonalBlockMatrix_properties a b).2.1
  map_mul' g h := Subtype.ext ((orthogonalBlockMatrix_properties a b).2.2.1 g h)
  continuous_toFun := (orthogonalBlockMatrix_properties a b).2.2.2.subtype_mk _

/-- Real orthogonal normal form uses these exact line and rotation blocks, up to conjugacy. -/
theorem exists_orthogonalBlock_conjugate (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    ∃ a b : ℕ, ∃ hDim : a + b * 2 = r,
      ∃ g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
        (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ),
      ∃ Q : Matrix.orthogonalGroup (Fin r) ℝ,
        A.val = Q.val *
          (orthogonalBlockMatrix a b g).submatrix (Fin.cast hDim.symm) (Fin.cast hDim.symm) *
            (Q⁻¹).val := by
  /- The real orthogonal spectral decomposition uses the symmetric part
  U + U⁻¹ and induction on invariant orthogonal complements. Its basis is
  already ordered with lines first. Transport that same basis along the
  supplied dimension equality, then use its actual change-of-basis matrix. -/
  classical
  let U := orthogonalEuclideanIsometry r A
  obtain ⟨a, b, B, l, p, hl, hp⟩ := exists_orthonormalBasis_orthogonal_blocks U
  have hDim : a + b * 2 = r := by
    have h := Module.finrank_eq_card_basis B.toBasis
    simpa using h.symm
  let e : Fin (a + b * 2) ≃ Fin a ⊕ (Fin b × Fin 2) :=
    finSumFinEquiv.symm.trans ((Equiv.refl (Fin a)).sumCongr finProdFinEquiv.symm)
  let e' : Fin r ≃ Fin a ⊕ (Fin b × Fin 2) := (finCongr hDim.symm).trans e
  let C : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)) := B.reindex e'.symm
  let S := EuclideanSpace.basisFun (Fin r) ℝ
  let Q : Matrix.orthogonalGroup (Fin r) ℝ :=
    ⟨S.toBasis.toMatrix C, S.toMatrix_orthonormalBasis_mem_orthogonal C⟩
  have hA : LinearMap.toMatrix S.toBasis S.toBasis U.toLinearMap = A.val := by
    change LinearMap.toMatrix S.toBasis S.toBasis (Matrix.toEuclideanLin A.val) = _
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  -- The block entries are computed in the exact original Fin.cast order.
  have hmatrix : LinearMap.toMatrix C.toBasis C.toBasis U.toLinearMap =
      (orthogonalBlockMatrix a b (l, p)).submatrix
        (Fin.cast hDim.symm) (Fin.cast hDim.symm) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
      C, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    change inner ℝ (B (e' i)) (U (B (e' j))) =
      match e' i, e' j with
      | .inl k, .inl z => if k = z then (l k).val 0 0 else 0
      | .inr (k, s), .inr (z, t) => if k = z then (p k).val s t else 0
      | _, _ => 0
    rcases e' i with k | ⟨k, s⟩ <;> rcases e' j with z | ⟨z, t⟩
    · by_cases h : k = z
      · subst z
        simp [hl, inner_smul_right]
      · simp [hl, inner_smul_right, B.inner_eq_ite, h]
    · rw [hp, inner_sum]
      simp [inner_smul_right, B.inner_eq_ite]
    · simp [hl, inner_smul_right, B.inner_eq_ite]
    · by_cases h : k = z
      · subst z
        rw [hp, inner_sum]
        fin_cases s <;> simp [inner_smul_right, B.inner_eq_ite]
      · rw [hp, inner_sum]
        simp [inner_smul_right, B.inner_eq_ite, h]
  have hQinv : (Q⁻¹).val = C.toBasis.toMatrix S := by
    have hQR : Q.val * C.toBasis.toMatrix S = 1 :=
      S.toBasis.toMatrix_mul_toMatrix_flip C.toBasis
    have hQQ : (Q⁻¹).val * Q.val = 1 := congrArg Subtype.val (inv_mul_cancel Q)
    calc
      (Q⁻¹).val = (Q⁻¹).val * (Q.val * C.toBasis.toMatrix S) := by
        rw [hQR, mul_one]
      _ = C.toBasis.toMatrix S := by rw [← Matrix.mul_assoc, hQQ, one_mul]
  refine ⟨a, b, hDim, (l, p), Q, ?_⟩
  rw [hQinv, ← hmatrix]
  change A.val = S.toBasis.toMatrix C.toBasis *
    LinearMap.toMatrix C.toBasis C.toBasis U.toLinearMap * C.toBasis.toMatrix S.toBasis
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  exact hA.symm

/-- Restriction to the actual line-and-rotation block subgroups detects virtual representations. -/
theorem eq_of_orthogonalBlock_restrictions (r : ℕ)
    (x y : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ))
    (hres : ∀ (a b : ℕ) (hDim : a + b * 2 = r),
      representationRestrictionRingHom (hDim ▸ orthogonalBlockInclusion a b) x =
        representationRestrictionRingHom (hDim ▸ orthogonalBlockInclusion a b) y) :
    x = y := by
  /- Evaluate the given restriction identity on the block form of each actual
  A. Transporting the original inclusion along hDim uses exactly its Fin.cast
  matrix. Conjugacy invariance transfers this equality back to A, and compact
  character injectivity then identifies the original virtual classes. -/
  classical
  let : CompactSpace (Matrix.orthogonalGroup (Fin r) ℝ) := compactSpace_orthogonalGroup r
  apply representationCharacter_injective
  funext A
  obtain ⟨a, b, hDim, g, Q, hA⟩ := exists_orthogonalBlock_conjugate r A
  let φ := hDim ▸ orthogonalBlockInclusion a b
  have hφ : (φ g).val = (orthogonalBlockMatrix a b g).submatrix
      (Fin.cast hDim.symm) (Fin.cast hDim.symm) := by
    subst r
    rfl
  have hconj : A = Q * φ g * Q⁻¹ := by
    apply Subtype.ext
    change A.val = Q.val * (φ g).val * (Q⁻¹).val
    rw [hφ]
    exact hA
  have hchar : representationCharacter _ x (φ g) = representationCharacter _ y (φ g) := by
    have h := congrArg (fun z ↦ representationCharacter _ z g) (hres a b hDim)
    simpa only [representationCharacter_restrict] using h
  rw [hconj, representationCharacter_conj, representationCharacter_conj]
  exact hchar

end AtiyahSinger
