/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantClopenRefinement

/-!
# The native open intersection and its iterated-open carrier

Public module ID: M1319.

The displayed diffeomorphism retains each original ambient point and covector.
It identifies a nested open piece with the actual ambient intersection.
This comparison is used to assemble one common clopen family before
taking direct sums.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The actual intersection is the same smooth submanifold as its nested-open carrier. -/
def openIntersectionDiffeomorph (U V : Opens M) :
    ↥(U ⊓ V) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ openRefinementPiece U V where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Subtype.val : ↥(U ⊓ V) → M)
    exact contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : openRefinementPiece U V ↦ x.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same ambient covector is retained by the native intersection identification. -/
theorem cotangentDiffeomorph_openIntersection (U V : Opens M)
    (z : CotangentTotalSpace (n := n) (M := ↥(U ⊓ V))) :
    cotangentDiffeomorph (openIntersectionDiffeomorph (n := n) U V) z =
      ⟨openIntersectionDiffeomorph (n := n) U V z.proj, z.snd⟩ := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let P := U ⊓ V
  let Q := openRefinementPiece U V
  let e := openIntersectionDiffeomorph (n := n) U V
  -- Both inclusions are the original open embeddings, whose native derivatives are identities.
  have hinc (y : Q) : mfderiv I I (fun x : Q ↦ x.val.val) y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) y.val)
      ((contMDiff_subtype_val (U := Q) (n := ∞)).mdifferentiable (by simp) y)
    rw [mfderiv_openSubtypeVal, mfderiv_openSubtypeVal] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  have hderiv (y : Q) : mfderiv I I e.symm y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      ((contMDiff_subtype_val (U := P) (n := ∞)).mdifferentiable (by simp) (e.symm y))
      (e.symm.mdifferentiable (by simp) y)
    change mfderiv I I (fun x : Q ↦ x.val.val) y =
      (mfderiv I I (Subtype.val : P → M) (e.symm y)).comp (mfderiv I I e.symm y) at h
    rw [hinc, mfderiv_openSubtypeVal] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h.symm
  change (⟨e z.proj, z.snd.comp (mfderiv I I e.symm (e z.proj))⟩ :
    CotangentTotalSpace (n := n) (M := Q)) = ⟨e z.proj, z.snd⟩
  rw [hderiv]
  apply TotalSpace.ext rfl
  apply heq_of_eq
  apply ContinuousLinearMap.ext
  intro v
  rfl

end AtiyahSinger
