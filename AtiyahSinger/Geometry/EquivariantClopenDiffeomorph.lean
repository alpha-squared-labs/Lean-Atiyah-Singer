/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantClopenPartition

/-!
# Actual clopen partitions under an equivariant diffeomorphism

Public module ID: M1178.

Pullback keeps the original finite indexing and takes actual inverse-image
open sets, with the restricted ambient action. The corresponding diffeomorphism
of each open piece has the same cotangent square with the original inclusions.
These are the geometric data needed to transport whole elliptic symbol families.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {G M N : Type*} [Group G] [TopologicalSpace M] [TopologicalSpace N]
  [MulAction G M] [MulAction G N]

/-- The actual inverse-image partition keeps its finite indexing and ambient action. -/
def EquivariantClopenPartition.pullback
    (P : EquivariantClopenPartition (G := G) (M := M))
    (f : C(N, M)) (hf : ∀ (g : G) (x : N), f (g • x) = g • f x) :
    EquivariantClopenPartition (G := G) (M := N) where
  size := P.size
  piece i := Opens.comap f (P.piece i)
  isClosed i := (P.isClosed i).preimage f.continuous
  disjoint := by
    intro i j hij
    exact (P.disjoint hij).preimage f
  cover := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have h : f x ∈ ⋃ i, (P.piece i : Set M) := by rw [P.cover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact ⟨i, hi⟩
  invariant := by
    intro i g x
    change f (g • x) ∈ P.piece i ↔ f x ∈ P.piece i
    rw [hf]
    exact P.invariant i g (f x)
  mulAction i := {
    smul := fun g x ↦ ⟨g • x.val, by
      change f (g • x.val) ∈ P.piece i
      rw [hf]
      exact (P.invariant i g (f x.val)).mpr x.property⟩
    one_smul := fun x ↦ Subtype.ext (one_smul G x.val)
    mul_smul := fun g h x ↦ Subtype.ext (mul_smul g h x.val) }
  equivariant := fun _ _ _ ↦ rfl

variable {n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

/-- Restrict the actual diffeomorphism to an open set and its inverse image. -/
def openPreimageDiffeomorph
    (e : N ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ M) (U : Opens M) :
    Opens.comap ⟨e, e.continuous⟩ U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U where
  toFun x := ⟨e x.val, x.property⟩
  invFun x := ⟨e.symm x.val, by
    change e (e.symm x.val) ∈ U
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Cotangent restriction uses the same inverse differential as the ambient diffeomorphism. -/
theorem cotangentDiffeomorph_openPreimage
    (e : N ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ M) (U : Opens M)
    (z : CotangentTotalSpace (n := n) (M := Opens.comap ⟨e, e.continuous⟩ U)) :
    cotangentOpenInclusion U (cotangentDiffeomorph (openPreimageDiffeomorph e U) z) =
      cotangentDiffeomorph e (cotangentOpenInclusion (Opens.comap ⟨e, e.continuous⟩ U) z) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let V := Opens.comap ⟨e, e.continuous⟩ U
  let d := openPreimageDiffeomorph e U
  -- Both actual open inclusions have identity native derivatives.
  have hderiv (y : U) : mfderiv I I d.symm y = mfderiv I I e.symm y.val := by
    have hleft := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) (d.symm y))
      (d.symm.mdifferentiable (by simp) y)
    have hright := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      (e.symm.mdifferentiable (by simp) y.val)
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) y)
    have hmaps : (Subtype.val : V → N) ∘ d.symm = e.symm ∘ (Subtype.val : U → M) := rfl
    rw [hmaps, hright, mfderiv_openSubtypeVal, mfderiv_openSubtypeVal] at hleft
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) hleft.symm
  change (⟨e z.proj.val, z.snd.comp (mfderiv I I d.symm (d z.proj))⟩ :
    CotangentTotalSpace (n := n) (M := M)) =
      ⟨e z.proj.val, z.snd.comp (mfderiv I I e.symm (e z.proj.val))⟩
  rw [hderiv]
  rfl

end AtiyahSinger
