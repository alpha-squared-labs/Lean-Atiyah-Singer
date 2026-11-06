/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenIntersectionDiffeomorph

/-!
# Swapping the two native open restrictions

Public module ID: M1323.

The actual point and covector are unchanged when two open restrictions are
applied in the opposite order. This adapter assembles the original clopen
symbol families on either member of a common partition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The two orders of native open restriction preserve the actual ambient point. -/
def openRefinementSwapDiffeomorph (U V : Opens M) :
    openRefinementPiece U V ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ openRefinementPiece V U where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : openRefinementPiece U V ↦ x.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : openRefinementPiece V U ↦ x.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Swapping the native open restrictions retains the same ambient covector. -/
theorem cotangentDiffeomorph_openRefinementSwap (U V : Opens M)
    (z : CotangentTotalSpace (n := n) (M := openRefinementPiece U V)) :
    cotangentDiffeomorph (openRefinementSwapDiffeomorph (n := n) U V) z =
      ⟨openRefinementSwapDiffeomorph (n := n) U V z.proj, z.snd⟩ := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let P := openRefinementPiece U V
  let Q := openRefinementPiece V U
  let e := openRefinementSwapDiffeomorph (n := n) U V
  -- Each double inclusion has identity derivative in the inherited native charts.
  have hinc (A B : Opens M) (y : openRefinementPiece A B) :
      mfderiv I I (fun x : openRefinementPiece A B ↦ x.val.val) y =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      ((contMDiff_subtype_val (U := A) (n := ∞)).mdifferentiable (by simp) y.val)
      ((contMDiff_subtype_val (U := openRefinementPiece A B) (n := ∞)).mdifferentiable
        (by simp) y)
    rw [mfderiv_openSubtypeVal, mfderiv_openSubtypeVal] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  have hderiv (y : Q) : mfderiv I I e.symm y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      (((contMDiff_subtype_val (U := U) (n := ∞)).comp
        (contMDiff_subtype_val (U := P) (n := ∞))).mdifferentiable
          (by simp) (e.symm y)) (e.symm.mdifferentiable (by simp) y)
    change mfderiv I I (fun x : Q ↦ x.val.val) y =
      (mfderiv I I (fun x : P ↦ x.val.val) (e.symm y)).comp (mfderiv I I e.symm y) at h
    rw [hinc, hinc] at h
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
