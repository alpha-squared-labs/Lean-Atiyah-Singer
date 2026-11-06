/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteProjectiveModuleCategory
public import AtiyahSinger.Topology.ProjectiveKZero
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Effective equality in the existing finite-projective K-zero group

Public module ID: M1925.

Equality of two positive classes in the original free-group quotient is witnessed
by one common finite projective summand. The proof compares the original quotient
with mathlib's group completion of the standard monoid of module isomorphism classes.
This auxiliary monoid is local to the proof; the original K-zero group is unchanged.

The common-summand criterion is the defining effective equality in Grothendieck
completion, as used in SG I.9 and Karoubi I.6. No cancellation of projective modules
or unstabilized isomorphism is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Matrix

universe u

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two projective classes agree exactly when one common finite projective summand
makes their original image modules isomorphic. -/
theorem kZeroClass_eq_iff_exists_stable_image_equiv (p q : IdempotentMatrix R) :
    kZeroClass R p = kZeroClass R q ↔
      ∃ r : IdempotentMatrix R, Nonempty ((p.image × r.image) ≃ₗ[R] (q.image × r.image)) := by
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
  constructor
  · intro hpq
    -- Form the standard additive monoid of finite-projective module isomorphism classes.
    let C := FiniteProjectiveModuleCat.{u} R
    let s : Setoid C := {
      r := fun P Q ↦ Nonempty (P.obj ≃ₗ[R] Q.obj)
      iseqv := ⟨fun P ↦ ⟨LinearEquiv.refl R P.obj⟩,
        fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩ }
    let M := Quotient s
    let zeroObj : C := FiniteProjectiveModuleCat.of R (Fin 0 → R)
    let sumObj (P Q : C) : C := FiniteProjectiveModuleCat.of R (P.obj × Q.obj)
    let cls : C → M := Quotient.mk s
    let add : M → M → M := Quotient.map₂ sumObj (by
      intro P P' ⟨e⟩ Q Q' ⟨f⟩
      exact ⟨e.prodCongr f⟩)
    let : AddCommMonoid M := {
      add := add
      zero := cls zeroObj
      add_assoc := by
        intro a b c
        refine Quotient.inductionOn₃ a b c ?_
        intro P Q S
        exact Quotient.sound ⟨LinearEquiv.prodAssoc R P.obj Q.obj S.obj⟩
      zero_add := by
        intro a
        refine Quotient.inductionOn a ?_
        intro P
        exact Quotient.sound ⟨LinearEquiv.uniqueProd⟩
      add_zero := by
        intro a
        refine Quotient.inductionOn a ?_
        intro P
        exact Quotient.sound ⟨LinearEquiv.prodUnique⟩
      add_comm := by
        intro a b
        refine Quotient.inductionOn₂ a b ?_
        intro P Q
        exact Quotient.sound ⟨LinearEquiv.prodComm R P.obj Q.obj⟩
      nsmul := @nsmulRec M ⟨cls zeroObj⟩ ⟨add⟩
      nsmul_zero := fun _ ↦ rfl
      nsmul_succ := fun _ _ ↦ rfl }
    let imageObj (r : IdempotentMatrix R) : C := by
      let := r.finite_image
      let := r.projective_image
      exact FiniteProjectiveModuleCat.of R r.image
    let v (r : IdempotentMatrix R) : Algebra.GrothendieckAddGroup M :=
      Algebra.GrothendieckAddGroup.of (cls (imageObj r))
    -- The two original relation families vanish in this concrete group completion.
    have hiso (a b : IdempotentMatrix R) (hab : a.IsEquivalent b) : v a = v b := by
      apply congrArg Algebra.GrothendieckAddGroup.of
      apply Quotient.sound
      exact (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv a b).mp hab
    have hadd (a b : IdempotentMatrix R) : v (a.blockSum b) = v a + v b := by
      change Algebra.GrothendieckAddGroup.of (cls (imageObj (a.blockSum b))) =
        Algebra.GrothendieckAddGroup.of (cls (imageObj a)) +
          Algebra.GrothendieckAddGroup.of (cls (imageObj b))
      rw [← map_add]
      apply congrArg Algebra.GrothendieckAddGroup.of
      exact Quotient.sound (hblock a b)
    obtain ⟨φ, hφ, _⟩ := kZero_universal_property v hiso hadd
    have heq : Algebra.GrothendieckAddGroup.of (cls (imageObj p)) =
        Algebra.GrothendieckAddGroup.of (cls (imageObj q)) :=
      (hφ p).symm.trans ((congrArg φ hpq).trans (hφ q))
    -- Localization equality extracts one actual common summand without cancellation.
    obtain ⟨c, hc⟩ :=
      (AddSubmonoid.LocalizationMap.eq_iff_exists (AddLocalization.addMonoidOf
        (⊤ : AddSubmonoid M))).mp heq
    obtain ⟨P, hP⟩ := Quotient.exists_rep (c : M)
    rw [← hP] at hc
    obtain ⟨e⟩ : Nonempty ((P.obj × p.image) ≃ₗ[R] (P.obj × q.image)) :=
      Quotient.exact hc
    -- Realize that same finite-projective module by an original finite idempotent.
    obtain ⟨r, ⟨a⟩⟩ := exists_idempotentMatrix_of_finite_projective R P.obj
    refine ⟨r, ⟨?_⟩⟩
    exact ((LinearEquiv.refl R p.image).prodCongr a).trans
      ((LinearEquiv.prodComm R p.image P.obj).trans
        (e.trans ((LinearEquiv.prodComm R P.obj q.image).trans
          ((LinearEquiv.refl R q.image).prodCongr a.symm))))
  · rintro ⟨r, ⟨e⟩⟩
    -- The same summand may be cancelled in the group, without cancelling it as a module.
    obtain ⟨a⟩ := hblock p r
    obtain ⟨b⟩ := hblock q r
    have h := kZeroClass_eq_of_isEquivalent (p.blockSum r) (q.blockSum r)
      ((IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
        ⟨a.trans (e.trans b.symm)⟩)
    rw [kZeroClass_blockSum, kZeroClass_blockSum] at h
    exact add_right_cancel h

end AtiyahSinger
