/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RightKZero
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# K₀ classes of finite projective right modules

Public module ID: M2112.

The right-module K₀ presentation assigns a class to an arbitrary finite projective
right module by choosing its finite idempotent presentation. This construction
uses only its actual Rᵐᵒᵖ action, permits independent module universes, and imposes
no commutativity, basis, constant-rank or nontriviality assumption.

The finite free comparison explicitly identifies the regular left Rᵐᵒᵖ module
with the original right columns by coefficientwise unop. Its finite/projective
certificates are transported through that same map, without extra hypotheses.

Sources: Karoubi, K-Theory, I.6.16 and III.1.5, for finite-projective K₀;
III.1.19--1.20 for its use in the polynomial-cokernel Bott inverse. Only the
specified right scalar action is used; comparison with another module action
requires compatibility data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RightKTheory

open scoped Matrix

universe u v w

variable (R : Type u) [Ring R]

/-- Coefficientwise unop identifies regular left opposite columns with actual right columns. -/
def finiteFreeRightModuleEquiv (n : ℕ) :
    (Fin n → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) where
  toFun f := fun i ↦ MulOpposite.unop (f i)
  invFun f := fun i ↦ MulOpposite.op (f i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Finite free right columns are finitely generated and projective. -/
theorem finiteFreeRightModule_finite_projective (n : ℕ) :
    Module.Finite Rᵐᵒᵖ (Fin n → R) ∧ Module.Projective Rᵐᵒᵖ (Fin n → R) := by
  -- Transport both properties from standard free opposite columns through the same unop map.
  exact ⟨Module.Finite.equiv (finiteFreeRightModuleEquiv R n),
    Module.Projective.of_equiv' (finiteFreeRightModuleEquiv R n)⟩

/-- The K₀ class of a finite projective right module, using an actual idempotent presentation. -/
def projectiveModuleKZeroClass (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] : KZero R :=
  kZeroClass R (exists_idempotentMatrix_of_finite_projective R P).choose

variable {R}

/-- Isomorphic finite projective right modules have the same class, independent of presentation. -/
theorem projectiveModuleKZeroClass_eq_of_linearEquiv
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    [AddCommGroup Q] [Module Rᵐᵒᵖ Q] [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]
    (e : P ≃ₗ[Rᵐᵒᵖ] Q) :
    projectiveModuleKZeroClass R P = projectiveModuleKZeroClass R Q := by
  /- Stage 1: the chosen presentations supply right-linear equivalences from their actual
  images to P and Q. Compose those equivalences through e, retaining the specified actions.
  Stage 2: the rectangular-matrix equivalence criterion identifies the presentations in
  the defining K₀ quotient. This also proves independence of the choice of presentation. -/
  -- Compare the images of the two chosen presentations through the given module equivalence.
  obtain ⟨eP⟩ := (exists_idempotentMatrix_of_finite_projective R P).choose_spec
  obtain ⟨eQ⟩ := (exists_idempotentMatrix_of_finite_projective R Q).choose_spec
  apply kZeroClass_eq_of_isEquivalent
  apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
  exact ⟨eP.trans (e.trans eQ.symm)⟩

/-- The right module class of the specified idempotent image is its original K₀ generator. -/
theorem projectiveModuleKZeroClass_image (p : IdempotentMatrix R) :
    letI : Module.Finite Rᵐᵒᵖ p.image := p.finite_image
    letI : Module.Projective Rᵐᵒᵖ p.image := p.projective_image
    projectiveModuleKZeroClass R p.image = kZeroClass R p := by
  /- Stage 1: compose the chosen presentation equivalence with the identity on this same
  right image module. Its scalar action and its inclusion in the original columns agree.
  Stage 2: use the image-equivalence criterion and the K₀ isomorphism relation to compare
  the chosen generator with p. The displayed certificates concern this particular p. -/
  let : Module.Finite Rᵐᵒᵖ p.image := p.finite_image
  let : Module.Projective Rᵐᵒᵖ p.image := p.projective_image
  -- The chosen image presentation is equivalent to the same specified image p.image.
  apply kZeroClass_eq_of_isEquivalent
  apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
  exact (exists_idempotentMatrix_of_finite_projective R p.image).choose_spec

set_option backward.isDefEq.respectTransparency.types false in
/-- A direct sum of finite projective right modules gives the sum of their K₀ classes. -/
theorem projectiveModuleKZeroClass_prod
    (P : Type v) (Q : Type w) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    [AddCommGroup Q] [Module Rᵐᵒᵖ Q] [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q] :
    projectiveModuleKZeroClass R (P × Q) =
      projectiveModuleKZeroClass R P + projectiveModuleKZeroClass R Q := by
  /- Stage 1: splitting the standard coordinates identifies the block-sum image of the
  two chosen idempotents with the product of their images, and hence with P × Q. These
  maps are right-linear, without commuting any coefficients or reversing matrix products.
  Stage 2: compare that block presentation with the chosen presentation of P × Q, then
  apply the defining block-sum relation. Finite direct sums are the displayed products. -/
  have hblock (p q : IdempotentMatrix R) :
      Nonempty ((p.blockSum q).image ≃ₗ[Rᵐᵒᵖ] p.image × q.image) := by
    -- Split the original columns using the same finite-index equivalence as blockSum.
    let c : (Fin (p.blockSum q).size → R) ≃ₗ[Rᵐᵒᵖ]
        (Fin p.size → R) × (Fin q.size → R) :=
      (LinearEquiv.piCongrLeft' Rᵐᵒᵖ (fun _ : Fin (p.blockSum q).size ↦ R)
        finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ Rᵐᵒᵖ R)
    have hc_apply (x : Fin (p.blockSum q).size → R) :
        c x = (x ∘ Fin.castAdd q.size, x ∘ Fin.natAdd p.size) := rfl
    have hc (x : Fin (p.blockSum q).size → R) :
        c ((Matrix.mulVecBilin R Rᵐᵒᵖ (p.blockSum q).matrix) x) =
          ((Matrix.mulVecBilin R Rᵐᵒᵖ p.matrix) (c x).1,
            (Matrix.mulVecBilin R Rᵐᵒᵖ q.matrix) (c x).2) := by
      change c ((Matrix.fromBlocks p.matrix 0 0 q.matrix).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ x) = _
      rw [Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv.symm,
        Matrix.fromBlocks_mulVec]
      apply Prod.ext <;> ext i <;>
        simp [hc_apply, Function.comp_def]
    -- The block multiplication formula restricts these coordinates to the actual images.
    have hmem (x : (p.blockSum q).image) :
        (c x.val).1 ∈ p.image ∧ (c x.val).2 ∈ q.image := by
      obtain ⟨y, hy⟩ := x.property
      rw [← hy]
      rw [hc]
      exact ⟨⟨(c y).1, rfl⟩, ⟨(c y).2, rfl⟩⟩
    let f : (p.blockSum q).image →ₗ[Rᵐᵒᵖ] p.image × q.image := {
      toFun := fun x ↦ (⟨(c x.val).1, (hmem x).1⟩, ⟨(c x.val).2, (hmem x).2⟩)
      map_add' := fun x y ↦ by apply Prod.ext <;> apply Subtype.ext <;> simp
      map_smul' := fun r x ↦ by apply Prod.ext <;> apply Subtype.ext <;> simp }
    -- Coordinate injectivity and explicit block-image preimages give the image equivalence.
    refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro x y hxy
      apply Subtype.ext
      apply c.injective
      exact Prod.ext (congrArg (fun z : p.image × q.image ↦ z.1.val) hxy)
        (congrArg (fun z : p.image × q.image ↦ z.2.val) hxy)
    · rintro ⟨x, y⟩
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      refine ⟨(Matrix.mulVecBilin R Rᵐᵒᵖ (p.blockSum q).matrix).rangeRestrict (c.symm (a, b)), ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · change (c ((Matrix.mulVecBilin R Rᵐᵒᵖ (p.blockSum q).matrix) (c.symm (a, b)))).1 = x.val
        rw [hc, c.apply_symm_apply]
        exact ha
      · change (c ((Matrix.mulVecBilin R Rᵐᵒᵖ (p.blockSum q).matrix) (c.symm (a, b)))).2 = y.val
        rw [hc, c.apply_symm_apply]
        exact hb
  -- Use the chosen presentations of P and Q, without choosing a basis for either module.
  let p := (exists_idempotentMatrix_of_finite_projective R P).choose
  let q := (exists_idempotentMatrix_of_finite_projective R Q).choose
  obtain ⟨eP⟩ := (exists_idempotentMatrix_of_finite_projective R P).choose_spec
  obtain ⟨eQ⟩ := (exists_idempotentMatrix_of_finite_projective R Q).choose_spec
  obtain ⟨eBlock⟩ := hblock p q
  let : Module.Finite Rᵐᵒᵖ (p.blockSum q).image := (p.blockSum q).finite_image
  let : Module.Projective Rᵐᵒᵖ (p.blockSum q).image := (p.blockSum q).projective_image
  -- Compare through the same block image, then apply the defining direct-sum relation.
  calc
    projectiveModuleKZeroClass R (P × Q) =
        projectiveModuleKZeroClass R (p.blockSum q).image :=
      (projectiveModuleKZeroClass_eq_of_linearEquiv
        (eBlock.trans (eP.prodCongr eQ))).symm
    _ = kZeroClass R (p.blockSum q) := projectiveModuleKZeroClass_image (p.blockSum q)
    _ = kZeroClass R p + kZeroClass R q := kZeroClass_blockSum p q
    _ = projectiveModuleKZeroClass R P + projectiveModuleKZeroClass R Q := rfl

/-- Actual free right columns have the class of the identity matrix of the same dimension. -/
theorem projectiveModuleKZeroClass_free (n : ℕ) :
    letI : Module.Finite Rᵐᵒᵖ (Fin n → R) :=
      (finiteFreeRightModule_finite_projective R n).1
    letI : Module.Projective Rᵐᵒᵖ (Fin n → R) :=
      (finiteFreeRightModule_finite_projective R n).2
    projectiveModuleKZeroClass R (Fin n → R) =
      kZeroClass R (IdempotentMatrix.identity R n) := by
  /- Stage 1: the identity matrix acts as the identity on the original right column
  module. Its range is therefore canonically right-linearly equivalent to Fin n → R.
  Stage 2: use this equivalence and the image formula to identify the chosen class with
  the specified identity generator. The explicit unop transport supplies finiteness and
  projectivity, also when n = 0 or R is the zero ring; no dimension theorem is required. -/
  let : Module.Finite Rᵐᵒᵖ (Fin n → R) :=
    (finiteFreeRightModule_finite_projective R n).1
  let : Module.Projective Rᵐᵒᵖ (Fin n → R) :=
    (finiteFreeRightModule_finite_projective R n).2
  let p := IdempotentMatrix.identity R n
  let : Module.Finite Rᵐᵒᵖ p.image := p.finite_image
  let : Module.Projective Rᵐᵒᵖ p.image := p.projective_image
  -- Identity multiplication fixes every original column, including the case n=0.
  have hp : p.image = ⊤ := by
    apply top_unique
    intro x _
    refine ⟨x, ?_⟩
    exact Matrix.one_mulVec x
  -- Compare through the actual full-image inclusion, then use its specified generator.
  let e : p.image ≃ₗ[Rᵐᵒᵖ] (Fin n → R) := LinearEquiv.ofTop p.image hp
  calc
    projectiveModuleKZeroClass R (Fin n → R) = projectiveModuleKZeroClass R p.image :=
      (projectiveModuleKZeroClass_eq_of_linearEquiv e).symm
    _ = kZeroClass R p := projectiveModuleKZeroClass_image p

end AtiyahSinger.RightKTheory
