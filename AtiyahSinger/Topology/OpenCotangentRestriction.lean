/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Topology.OpenCotangentKZero

/-!
# Restricting an open cotangent pushforward to an open source

Public module ID: M1967.

The actual image of an open source subset is again open. Its inherited
parametrization has the same inverse-dual differential as the original map
on that subset. Functoriality therefore identifies its cotangent pushforward
with source open extension followed by the original pushforward. This keeps
the specified maps needed for finite-component analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace Topology
open scoped Manifold ContDiff

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O] [T2Space O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 30

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the original parametrization preserves its exact cotangent open pushforward. -/
theorem exists_cotangentKZeroOpenEmbedding_restriction (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (A : Opens O) :
    ∃ W : Opens M, ∃ d : A ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ W,
      (∀ x : A, (d x).val = (e x.val).val) ∧
      cotangentKZeroOpenEmbedding W d =
        (cotangentKZeroOpenEmbedding U e).comp (cotangentKZeroOpenExtension A) := by
  classical
  let B : Opens U := ⟨e '' (A : Set O), e.toHomeomorph.isOpenMap _ A.isOpen⟩
  let W : Opens M := ⟨Subtype.val '' (B : Set U),
    U.isOpen.isOpenMap_subtype_val _ B.isOpen⟩
  have hWU : (W : Set M) ⊆ U := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  have hback (y : W) : e.symm ⟨y.val, hWU y.property⟩ ∈ A := by
    obtain ⟨z, ⟨x, hx, hzx⟩, hzy⟩ := y.property
    have hz : z = ⟨y.val, hWU y.property⟩ := Subtype.ext hzy
    rw [← hz, ← hzx, e.symm_apply_apply]
    exact hx
  let j : C(W, U) := ⟨fun y ↦ ⟨y.val, hWU y.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let d : A ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ W :=
    { toFun x := ⟨(e x.val).val, ⟨e x.val, ⟨x.val, x.property, rfl⟩, rfl⟩⟩
      invFun y := ⟨e.symm (j y), hback y⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x.val)
      right_inv y := by
        apply Subtype.ext
        change (e (e.symm (j y))).val = y.val
        exact congrArg (fun x : U ↦ x.val) (e.apply_symm_apply (j y))
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff W _).mp
        change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : A ↦ (e x.val).val)
        exact contMDiff_subtype_val.comp (e.contMDiff.comp contMDiff_subtype_val)
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff A _).mp
        change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun y : W ↦ e.symm (j y))
        apply e.symm.contMDiff.comp
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        exact contMDiff_subtype_val }
  refine ⟨W, d, fun _ ↦ rfl, ?_⟩
  -- Native open inclusions have identity derivative; both inverse maps retain the same derivative.
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hj (y : W) : mfderiv I I j y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hs : ContMDiff I I ∞ j := by
      apply (ContMDiff.subtypeVal_comp_iff _ _).mp
      exact contMDiff_subtype_val
    have h := mfderiv_comp y
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) (j y))
      (hs.mdifferentiable (by simp) y)
    change mfderiv I I (Subtype.val : W → M) y = _ at h
    rw [mfderiv_openSubtypeVal, mfderiv_openSubtypeVal] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T ↦ T v) h.symm
  have hderiv (y : W) : mfderiv I I d.symm y = mfderiv I I e.symm (j y) := by
    have hs : ContMDiff I I ∞ j := by
      apply (ContMDiff.subtypeVal_comp_iff _ _).mp
      exact contMDiff_subtype_val
    have hleft := mfderiv_comp y
      ((contMDiff_subtype_val (U := A) (n := ∞)).mdifferentiable (by simp) (d.symm y))
      (d.symm.mdifferentiable (by simp) y)
    have hright := mfderiv_comp y (e.symm.mdifferentiable (by simp) (j y))
      (hs.mdifferentiable (by simp) y)
    rw [mfderiv_openSubtypeVal] at hleft
    rw [hj] at hright
    exact (ContinuousLinearMap.id_comp _).symm.trans
      (hleft.symm.trans (hright.trans (ContinuousLinearMap.comp_id _)))
  let iA := cotangentOpenInclusion (n := n) A
  let iU := cotangentOpenInclusion (n := n) U
  let iW := cotangentOpenInclusion (n := n) W
  let c := cotangentDiffeomorph e
  let b := cotangentDiffeomorph d
  have hsquare : iW ∘ b = (iU ∘ c) ∘ iA := by
    funext z
    change (⟨(e z.proj.val).val, z.snd.comp (mfderiv I I d.symm (d z.proj))⟩ :
      CotangentTotalSpace (n := n) (M := M)) =
        ⟨(e z.proj.val).val, z.snd.comp (mfderiv I I e.symm (e z.proj.val))⟩
    rw [hderiv]
    rfl
  -- Turn each diffeomorphism into its actual open pushforward, then compose the exact square.
  have hU : IsOpenEmbedding iU := isOpenEmbedding_cotangentOpenInclusion U
  have hW : IsOpenEmbedding iW := isOpenEmbedding_cotangentOpenInclusion W
  have hA : IsOpenEmbedding iA := isOpenEmbedding_cotangentOpenInclusion A
  have hmaps := congrArg (fun f : CotangentTotalSpace (n := n) (M := A) →
      CotangentTotalSpace (n := n) (M := M) ↦ f) hsquare
  change (compactSupportKZeroOpenPushforward iW hW).comp
      (compactSupportKZeroHomeomorph b) =
    ((compactSupportKZeroOpenPushforward iU hU).comp
      (compactSupportKZeroHomeomorph c)).comp
        (compactSupportKZeroOpenPushforward iA hA)
  rw [← compactSupportKZeroOpenPushforward_homeomorph,
    ← compactSupportKZeroOpenPushforward_homeomorph,
    ← compactSupportKZeroOpenPushforward_comp,
    ← compactSupportKZeroOpenPushforward_comp,
    ← compactSupportKZeroOpenPushforward_comp]
  congr 1

end AtiyahSinger
