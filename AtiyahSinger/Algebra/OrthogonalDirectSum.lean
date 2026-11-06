/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalBlockRestriction
public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Geometry.OrthogonalGroupManifold

/-!
# The actual ordered orthogonal direct-sum inclusion

Public module ID: M0046.

AR04, Atiyah--Singer I, Proposition (4.4), printed pp.504--505. The binary
homomorphism below is the literal diagonal block matrix, with the first factor
occupying the first p coordinates. Its coordinate equivalence is exactly
`finSumFinEquiv.symm`, hence exactly the order used by
`EuclideanSpace.finAddEquivProd`. The complexified action and the original Cayley
Lie atlases are retained. No conjugate copy of either group is selected.

The final two formulas identify the existing line/rotation block inclusion
with actual repeated binary inclusions. They remove the first real line or
the last rotation plane, preserving the source's order of all lines followed
by all planes. These are reusable subgroup decomposition statements used by
representation restriction, not definitions of a new family of block groups.
Dimension zero and empty families are included. The matrix and coordinate statements,
together with smoothness for the original Cayley atlases, are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 30

/-- The ordered diagonal block matrix, expressed on the original `Fin (p + q)` indices. -/
def orthogonalDirectSumMatrix (p q : ℕ)
    (g : Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) :
    Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  (Matrix.fromBlocks g.1.val 0 0 g.2.val).submatrix e e

/-- Orthogonality and the group/topological laws certify this specified binary block matrix. -/
theorem orthogonalDirectSumMatrix_properties (p q : ℕ) :
    (∀ g, orthogonalDirectSumMatrix p q g ∈ Matrix.orthogonalGroup (Fin (p + q)) ℝ) ∧
      orthogonalDirectSumMatrix p q 1 = 1 ∧
      (∀ g h, orthogonalDirectSumMatrix p q (g * h) =
        orthogonalDirectSumMatrix p q g * orthogonalDirectSumMatrix p q h) ∧
      Continuous (orthogonalDirectSumMatrix p q) := by
  /- Stage 1: expand Matrix.fromBlocks and use each original factor's
  transpose-multiplication identity. The off-diagonal blocks vanish and
  the two diagonal products are the corresponding identities. Reindexing
  by the specified finite equivalence preserves multiplication and transpose.
  Stage 2: the same block multiplication proves preservation of one and
  multiplication. This calculation includes empty blocks and does not
  assume p or q positive.
  Stage 3: each output entry is zero or an original matrix-coordinate
  evaluation on one factor. These are continuous in the native subgroup
  and product topologies, so the specified whole matrix map is continuous. -/
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  -- Reindex the original diagonal blocks by the specified coordinate equivalence.
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    apply (Matrix.submatrix_equiv_mem_unitary (e₁ := e) (e₂ := e)).mpr
    apply (Matrix.mem_orthogonalGroup_iff _ ℝ).mpr
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      (Matrix.mem_orthogonalGroup_iff (Fin p) ℝ).mp g.1.property,
      (Matrix.mem_orthogonalGroup_iff (Fin q) ℝ).mp g.2.property]
  · simp [orthogonalDirectSumMatrix]
  · intro g h
    change (Matrix.fromBlocks (g.1.val * h.1.val) 0 0 (g.2.val * h.2.val)).submatrix e e =
      (Matrix.fromBlocks g.1.val 0 0 g.2.val).submatrix e e *
        (Matrix.fromBlocks h.1.val 0 0 h.2.val).submatrix e e
    rw [Matrix.submatrix_mul_equiv]
    simp [Matrix.fromBlocks_multiply]
  · -- Each entry is one of the original continuous matrix coordinates, or zero.
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : Matrix.orthogonalGroup (Fin p) ℝ ×
        Matrix.orthogonalGroup (Fin q) ℝ ↦
      Matrix.fromBlocks g.1.val 0 0 g.2.val (e i) (e j))
    cases e i <;> cases e j <;>
      dsimp only [Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    · have hval : Continuous (fun A : Matrix.orthogonalGroup (Fin p) ℝ ↦
          (A.val : Matrix (Fin p) (Fin p) ℝ)) := continuous_subtype_val
      exact ((continuous_apply _).comp ((continuous_apply _).comp hval)).comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · have hval : Continuous (fun A : Matrix.orthogonalGroup (Fin q) ℝ ↦
          (A.val : Matrix (Fin q) (Fin q) ℝ)) := continuous_subtype_val
      exact ((continuous_apply _).comp ((continuous_apply _).comp hval)).comp continuous_snd

/-- The standard continuous inclusion of two orthogonal groups by ordered direct sum. -/
def orthogonalDirectSumInclusion (p q : ℕ) :
    (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) →ₜ*
      Matrix.orthogonalGroup (Fin (p + q)) ℝ where
  toFun g := ⟨orthogonalDirectSumMatrix p q g,
    (orthogonalDirectSumMatrix_properties p q).1 g⟩
  map_one' := Subtype.ext (orthogonalDirectSumMatrix_properties p q).2.1
  map_mul' g h := Subtype.ext ((orthogonalDirectSumMatrix_properties p q).2.2.1 g h)
  continuous_toFun := (orthogonalDirectSumMatrix_properties p q).2.2.2.subtype_mk _

/-- The binary block inclusion is smooth for the original Cayley atlases. -/
theorem orthogonalDirectSumInclusion_smooth (p q : ℕ) :
    ContMDiff (𝓘(ℝ, OrthogonalGroupModel p).prod 𝓘(ℝ, OrthogonalGroupModel q))
      𝓘(ℝ, OrthogonalGroupModel (p + q)) ∞ (orthogonalDirectSumInclusion p q) := by
  -- Use the original Cayley criterion on the exact ordered block matrix.
  apply (contMDiff_orthogonalGroup_iff
    (𝓘(ℝ, OrthogonalGroupModel p).prod 𝓘(ℝ, OrthogonalGroupModel q)) (p + q) ∞ _).mpr
  intro i j
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  change ContMDiff _ 𝓘(ℝ) ∞
    (fun g : Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ ↦
      Matrix.fromBlocks g.1.val 0 0 g.2.val (e i) (e j))
  -- The original finite reindexing selects either an unchanged entry or a zero mixed block.
  cases e i with
  | inl a =>
    cases e j with
    | inl b =>
      exact ((contMDiff_orthogonalGroup_iff 𝓘(ℝ, OrthogonalGroupModel p) p ∞ id).mp
        contMDiff_id a b).comp contMDiff_fst
    | inr b => exact contMDiff_const
  | inr a =>
    cases e j with
    | inl b => exact contMDiff_const
    | inr b =>
      exact ((contMDiff_orthogonalGroup_iff 𝓘(ℝ, OrthogonalGroupModel q) q ∞ id).mp
        contMDiff_id a b).comp contMDiff_snd

/-- The original complexification action is the ordered direct sum in the specified coordinates. -/
theorem orthogonalDirectSumInclusion_complexification (p q : ℕ)
    (g : Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
    (z : EuclideanSpace ℂ (Fin p) × EuclideanSpace ℂ (Fin q)) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)).symm
        (g.1 • z.1, g.2 • z.2) =
      orthogonalDirectSumInclusion p q g •
        (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)).symm z := by
  /- Stage 1: both finAddEquivProd and the specified block matrix use
  finSumFinEquiv.symm. Split the output index into its first or second
  summand. The mixed matrix blocks are zero, so each complex matrix-vector
  sum is precisely the original action of the corresponding factor.
  Stage 2: entrywise inclusion of real coefficients into the complex
  numbers commutes with this block calculation. The two displayed vectors
  therefore agree in every original coordinate. There is no permutation
  of the factors, complex conjugation, or change of the Hermitian metrics. -/
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  let C := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)
  -- These are the exact ordered coordinates of the already specified equivalence.
  have hcoords (w : EuclideanSpace ℂ (Fin p) × EuclideanSpace ℂ (Fin q))
      (i : Fin (p + q)) : C.symm w i = Sum.elim (fun j ↦ w.1 j) (fun j ↦ w.2 j) (e i) := by
    simp [C, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      LinearIsometryEquiv.piLpCongrLeft, PiLp.sumPiLpEquivProdLpPiLp,
      LinearIsometryEquiv.symm, LinearEquiv.piCongrLeft', Equiv.piCongrLeft',
      LinearEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, e]
    cases finSumFinEquiv.symm i <;> rfl
  have hvec : (fun j ↦ C.symm z (e.symm j)) =
      Sum.elim (fun j ↦ z.1 j) (fun j ↦ z.2 j) := by
    funext j
    rw [hcoords, e.apply_symm_apply]
  have hmatrix : (orthogonalDirectSumMatrix p q g).map Complex.ofReal =
      (Matrix.fromBlocks (g.1.val.map Complex.ofReal) 0 0
        (g.2.val.map Complex.ofReal)).submatrix e e := by
    ext i j
    change Complex.ofReal (Matrix.fromBlocks g.1.val 0 0 g.2.val (e i) (e j)) =
      Matrix.fromBlocks (g.1.val.map Complex.ofReal) 0 0 (g.2.val.map Complex.ofReal) (e i) (e j)
    cases e i <;> cases e j <;> rfl
  -- The original block matrix-vector product has no mixed terms.
  ext i
  change C.symm (g.1 • z.1, g.2 • z.2) i =
    ((orthogonalDirectSumMatrix p q g).map Complex.ofReal *ᵥ (fun j ↦ C.symm z j)) i
  rw [hmatrix, Matrix.submatrix_mulVec_equiv]
  change C.symm (g.1 • z.1, g.2 • z.2) i =
    ((Matrix.fromBlocks (g.1.val.map Complex.ofReal) 0 0 (g.2.val.map Complex.ofReal)) *ᵥ
      (fun j ↦ C.symm z (e.symm j))) (e i)
  rw [hvec, Matrix.fromBlocks_mulVec, hcoords]
  cases e i <;> simp [Function.comp_def] <;> rfl

/-- Removing the first real line factors the existing ordered block subgroup through binary sum. -/
theorem orthogonalBlockInclusion_line_succ (a b : ℕ)
    (g : (Fin (a + 1) → Matrix.orthogonalGroup (Fin 1) ℝ) ×
      (Fin b → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) :
    let hDim : 1 + (a + b * 2) = (a + 1) + b * 2 := by omega
    (orthogonalBlockInclusion (a + 1) b g).val =
      (orthogonalDirectSumInclusion 1 (a + b * 2)
        (g.1 0, orthogonalBlockInclusion a b (fun i ↦ g.1 i.succ, g.2))).val.submatrix
          (Fin.cast hDim.symm) (Fin.cast hDim.symm) := by
  /- Stage 1: the first coordinate is the original real line indexed by
  zero. The next a coordinates are exactly its successor-indexed real
  lines, followed by the original b ordered pairs of rotation coordinates.
  Stage 2: expand both actual block matrices in these coordinates. Their
  diagonal entries come from the same original factor matrices and every
  mixed entry is zero. The displayed Fin.cast accounts only for equality
  of the two dimension expressions; it is not a change of the block order.
  This equality of the actual matrices identifies the corresponding
  continuous homomorphisms pointwise for subsequent restriction arguments. -/
  let hDim : 1 + (a + b * 2) = (a + 1) + b * 2 := by omega
  -- The dimension cast only moves the first line out of the original ordered coordinates.
  have hzero : finSumFinEquiv.symm
      (Fin.cast hDim.symm (Fin.castAdd (b * 2) (0 : Fin (a + 1)))) =
      (Sum.inl 0 : Fin 1 ⊕ Fin (a + b * 2)) := by
    apply finSumFinEquiv.injective
    simp
    rfl
  have hline (k : Fin a) : finSumFinEquiv.symm
      (Fin.cast hDim.symm (Fin.castAdd (b * 2) k.succ)) =
      (Sum.inr (Fin.castAdd (b * 2) k) : Fin 1 ⊕ Fin (a + b * 2)) := by
    apply finSumFinEquiv.injective
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
    apply Fin.ext
    simp
    omega
  have hplane (k : Fin (b * 2)) : finSumFinEquiv.symm
      (Fin.cast hDim.symm (Fin.natAdd (a + 1) k)) =
      (Sum.inr (Fin.natAdd a k) : Fin 1 ⊕ Fin (a + b * 2)) := by
    apply finSumFinEquiv.injective
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
    apply Fin.ext
    simp
    omega
  have hblock : (orthogonalBlockInclusion a b (fun i ↦ g.1 i.succ, g.2)).val =
      orthogonalBlockMatrix a b (fun i ↦ g.1 i.succ, g.2) := rfl
  have hzero_succ (k : Fin a) : (0 : Fin (a + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
  change orthogonalBlockMatrix (a + 1) b g =
    (orthogonalDirectSumMatrix 1 (a + b * 2)
      (g.1 0, orthogonalBlockInclusion a b (fun i ↦ g.1 i.succ, g.2))).submatrix
        (Fin.cast hDim.symm) (Fin.cast hDim.symm)
  -- Compare first line, remaining lines, and rotation-plane entries without permuting them.
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := a + 1) (n := b * 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := a + 1) (n := b * 2)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock, hzero_succ,
        Matrix.submatrix, Matrix.fromBlocks, hzero, hline]
  · induction i using Fin.cases <;>
      simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock,
        Matrix.submatrix, Matrix.fromBlocks, hzero, hline, hplane]
  · induction j using Fin.cases <;>
      simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock,
        Matrix.submatrix, Matrix.fromBlocks, hzero, hline, hplane]
  · simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock,
      Matrix.submatrix, Matrix.fromBlocks, hplane]

/-- Removing the last rotation plane factors the original ordered block subgroup by binary sum. -/
theorem orthogonalBlockInclusion_plane_succ (a b : ℕ)
    (g : (Fin a → Matrix.orthogonalGroup (Fin 1) ℝ) ×
      (Fin (b + 1) → Matrix.specialOrthogonalGroup (Fin 2) ℝ)) :
    let hDim : (a + b * 2) + 2 = a + (b + 1) * 2 := by omega
    (orthogonalBlockInclusion a (b + 1) g).val =
      (orthogonalDirectSumInclusion (a + b * 2) 2
        (orthogonalBlockInclusion a b (g.1, fun j ↦ g.2 j.castSucc),
          specialOrthogonalGroupInclusion 2 (g.2 (Fin.last b)))).val.submatrix
            (Fin.cast hDim.symm) (Fin.cast hDim.symm) := by
  /- Stage 1: retain all a line blocks and the first b rotation blocks in
  their original order. The final two coordinates are the original last
  rotation plane, included by the already specified SO(2) -> O(2) map.
  Stage 2: the coordinate ordering in finProdFinEquiv places these two
  entries after the first a+2b coordinates. Expanding the actual binary
  block matrix gives precisely orthogonalBlockMatrix a (b+1), entry by
  entry, after the displayed dimension cast. No conjugacy representative
  or arbitrary isomorphic product group replaces the original subgroup. -/
  let hDim : (a + b * 2) + 2 = a + (b + 1) * 2 := by omega
  -- Under the given dimension cast, only the last ordered rotation plane moves right.
  have hline (k : Fin a) : finSumFinEquiv.symm
      (Fin.cast hDim.symm (Fin.castAdd ((b + 1) * 2) k)) =
      (Sum.inl (Fin.castAdd (b * 2) k) : Fin (a + b * 2) ⊕ Fin 2) := by
    apply finSumFinEquiv.injective
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
    apply Fin.ext
    rfl
  have hplane (k : Fin b) (t : Fin 2) : finSumFinEquiv.symm
      (Fin.cast hDim.symm (Fin.natAdd a (finProdFinEquiv (k.castSucc, t)))) =
      (Sum.inl (Fin.natAdd a (finProdFinEquiv (k, t))) : Fin (a + b * 2) ⊕ Fin 2) := by
    apply finSumFinEquiv.injective
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
    apply Fin.ext
    rfl
  have hlast (t : Fin 2) : finSumFinEquiv.symm
      (Fin.cast hDim.symm (Fin.natAdd a (finProdFinEquiv (Fin.last b, t)))) =
      (Sum.inr t : Fin (a + b * 2) ⊕ Fin 2) := by
    apply finSumFinEquiv.injective
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  have hblock : (orthogonalBlockInclusion a b (g.1, fun j ↦ g.2 j.castSucc)).val =
      orthogonalBlockMatrix a b (g.1, fun j ↦ g.2 j.castSucc) := rfl
  have hlastval : (specialOrthogonalGroupInclusion 2 (g.2 (Fin.last b))).val =
      (g.2 (Fin.last b)).val := rfl
  have hne (k : Fin b) : (Fin.last b) ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
  change orthogonalBlockMatrix a (b + 1) g =
    (orthogonalDirectSumMatrix (a + b * 2) 2
      (orthogonalBlockInclusion a b (g.1, fun j ↦ g.2 j.castSucc),
        specialOrthogonalGroupInclusion 2 (g.2 (Fin.last b)))).submatrix
          (Fin.cast hDim.symm) (Fin.cast hDim.symm)
  -- Each entry is a retained line, an earlier plane, or the same last SO(2) matrix.
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := a) (n := (b + 1) * 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := a) (n := (b + 1) * 2)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock, Matrix.submatrix,
      Matrix.fromBlocks, hline]
  · obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective j
    induction k using Fin.lastCases <;>
      simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock, hlastval,
        Matrix.submatrix, Matrix.fromBlocks, hline, hplane, hlast]
  · obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective i
    induction k using Fin.lastCases <;>
      simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock, hlastval,
        Matrix.submatrix, Matrix.fromBlocks, hline, hplane, hlast]
  · obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨l, s⟩, rfl⟩ := finProdFinEquiv.surjective j
    induction k using Fin.lastCases <;> induction l using Fin.lastCases <;>
      simp [orthogonalBlockMatrix, orthogonalDirectSumMatrix, hblock, hlastval, hne,
        Matrix.submatrix, Matrix.fromBlocks, hplane, hlast]

end AtiyahSinger
