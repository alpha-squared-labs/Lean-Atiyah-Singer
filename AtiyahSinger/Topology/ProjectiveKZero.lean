/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KZeroFunctor
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The K₀ class of a finite projective module

Public module ID: M2013.

The idempotent presentation of `KZero` already identifies isomorphic image modules.
This file gives an arbitrary finite projective module its class by choosing such a
presentation, then records independence of the choice and compatibility with direct sums.
The class is used for the actual polynomial-loop cokernels in Karoubi III.1.18–1.20.

The construction is the standard finite-projective definition from Karoubi I.6.
It includes the zero ring and does not assume a basis or a constant rank for a projective module.
The group is the existing `KZero`; no second quotient or projective-module universe is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Matrix

universe u v w

variable (R : Type u) [CommRing R]

/-- The K₀ class of a finite projective module, using an actual idempotent presentation. -/
def projectiveModuleKZeroClass (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] : KZero R :=
  kZeroClass R (exists_idempotentMatrix_of_finite_projective R P).choose

variable {R}

/-- Isomorphic finite projective modules determine the same class, independently of presentation. -/
theorem projectiveModuleKZeroClass_eq_of_linearEquiv
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    (e : P ≃ₗ[R] Q) : projectiveModuleKZeroClass R P = projectiveModuleKZeroClass R Q := by
  /- Stage 1: the existence theorem supplies image-module equivalences for the two chosen
  idempotent presentations. Compose them with e to identify these actual image modules.
  Stage 2: translate this equivalence into the rectangular-matrix relation and use
  `kZeroClass_eq_of_isEquivalent`. This also proves independence of every presentation choice. -/
  -- Compare the images of the two chosen presentations through the given module equivalence.
  obtain ⟨eP⟩ := (exists_idempotentMatrix_of_finite_projective R P).choose_spec
  obtain ⟨eQ⟩ := (exists_idempotentMatrix_of_finite_projective R Q).choose_spec
  apply kZeroClass_eq_of_isEquivalent
  apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
  exact ⟨eP.trans (e.trans eQ.symm)⟩

/-- The general module class recovers the specified idempotent generator. -/
theorem projectiveModuleKZeroClass_image (p : IdempotentMatrix R) :
    letI : Module.Finite R p.image := p.finite_image
    letI : Module.Projective R p.image := p.projective_image
    projectiveModuleKZeroClass R p.image = kZeroClass R p := by
  /- Stage 1: choose the idempotent presentation used by the class of p.image. Its defining
  image equivalence identifies its image with the image of this specified p.
  Stage 2: use the rectangular-matrix equivalence criterion and the defining K₀ relation.
  The finite and projective certificates in the statement are those for this same p. -/
  let : Module.Finite R p.image := p.finite_image
  let : Module.Projective R p.image := p.projective_image
  -- The chosen image presentation is equivalent to the same specified image p.image.
  apply kZeroClass_eq_of_isEquivalent
  apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
  exact (exists_idempotentMatrix_of_finite_projective R p.image).choose_spec

set_option backward.isDefEq.respectTransparency.types false in
/-- A direct sum of finite projective modules gives the sum of their K₀ classes. -/
theorem projectiveModuleKZeroClass_prod
    (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q] :
    projectiveModuleKZeroClass R (P × Q) =
      projectiveModuleKZeroClass R P + projectiveModuleKZeroClass R Q := by
  /- Stage 1: take the two chosen idempotents p and q. Splitting coordinates by finSumFinEquiv
  identifies the image of their actual block sum with p.image × q.image, hence with P × Q.
  Stage 2: compare this presentation with the chosen presentation of P × Q using the image
  equivalence relation, and apply `kZeroClass_blockSum`. Finite direct sums are products here. -/
  have hblock (p q : IdempotentMatrix R) :
      Nonempty ((p.blockSum q).image ≃ₗ[R] p.image × q.image) := by
    -- Split the original columns using the same finite-index equivalence as blockSum.
    let c : (Fin (p.blockSum q).size → R) ≃ₗ[R]
        (Fin p.size → R) × (Fin q.size → R) :=
      (LinearEquiv.piCongrLeft' R (fun _ : Fin (p.blockSum q).size ↦ R)
        finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R)
    have hc_apply (x : Fin (p.blockSum q).size → R) :
        c x = (x ∘ Fin.castAdd q.size, x ∘ Fin.natAdd p.size) := rfl
    have hc (x : Fin (p.blockSum q).size → R) :
        c ((p.blockSum q).matrix.mulVecLin x) =
          (p.matrix.mulVecLin (c x).1, q.matrix.mulVecLin (c x).2) := by
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
    let f : (p.blockSum q).image →ₗ[R] p.image × q.image := {
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
      refine ⟨(p.blockSum q).matrix.mulVecLin.rangeRestrict (c.symm (a, b)), ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · change (c ((p.blockSum q).matrix.mulVecLin (c.symm (a, b)))).1 = x.val
        rw [hc, c.apply_symm_apply]
        exact ha
      · change (c ((p.blockSum q).matrix.mulVecLin (c.symm (a, b)))).2 = y.val
        rw [hc, c.apply_symm_apply]
        exact hb
  -- Use the chosen presentations of P and Q, without choosing a basis for either module.
  let p := (exists_idempotentMatrix_of_finite_projective R P).choose
  let q := (exists_idempotentMatrix_of_finite_projective R Q).choose
  obtain ⟨eP⟩ := (exists_idempotentMatrix_of_finite_projective R P).choose_spec
  obtain ⟨eQ⟩ := (exists_idempotentMatrix_of_finite_projective R Q).choose_spec
  obtain ⟨eBlock⟩ := hblock p q
  let : Module.Finite R (p.blockSum q).image := (p.blockSum q).finite_image
  let : Module.Projective R (p.blockSum q).image := (p.blockSum q).projective_image
  -- Compare through the same block image, then apply the defining direct-sum relation.
  calc
    projectiveModuleKZeroClass R (P × Q) =
        projectiveModuleKZeroClass R (p.blockSum q).image :=
      (projectiveModuleKZeroClass_eq_of_linearEquiv
        (eBlock.trans (eP.prodCongr eQ))).symm
    _ = kZeroClass R (p.blockSum q) := projectiveModuleKZeroClass_image (p.blockSum q)
    _ = kZeroClass R p + kZeroClass R q := kZeroClass_blockSum p q
    _ = projectiveModuleKZeroClass R P + projectiveModuleKZeroClass R Q := rfl

/-- A free module on n generators has the class of the n-by-n identity matrix. -/
theorem projectiveModuleKZeroClass_free (n : ℕ) :
    projectiveModuleKZeroClass R (Fin n → R) =
      kZeroClass R (IdempotentMatrix.identity R n) := by
  /- Stage 1: the identity matrix has full image, canonically equivalent to Fin n → R.
  Stage 2: identify the chosen presentation of this free module with that identity image
  and apply the defining isomorphism relation. No nontriviality hypothesis or dimension
  theorem is needed, so this includes n = 0 and the zero ring. -/
  let p := IdempotentMatrix.identity R n
  let : Module.Finite R p.image := p.finite_image
  let : Module.Projective R p.image := p.projective_image
  -- Identity multiplication fixes every original column, including the zero-rank case.
  have hp : p.image = ⊤ := by
    apply top_unique
    intro x _
    refine ⟨x, ?_⟩
    exact Matrix.one_mulVec x
  -- Compare through the actual full-image inclusion, then use its specified generator.
  calc
    projectiveModuleKZeroClass R (Fin n → R) = projectiveModuleKZeroClass R p.image :=
      (projectiveModuleKZeroClass_eq_of_linearEquiv (LinearEquiv.ofTop p.image hp)).symm
    _ = kZeroClass R p := projectiveModuleKZeroClass_image p

end AtiyahSinger
