/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedHorizontalCovectorDeformation
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Compact coordinate bounds for the specified horizontal lift

Public module ID: M0092.

The original smooth lift fixes the horizontal part of every actual covector.
In an original associated product chart, its base coordinate differs from
the chart horizontal coordinate by a linear function of the vertical
coordinate. The coefficient has one bound on each compact chart window.

This is the geometric error estimate needed to compare the full base factor
with the actual lifted horizontal symbol along their affine K-class homotopy.
The original lift and Euclidean model change remain fixed throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given horizontal lift has a uniform transverse coordinate bound on each compact window. -/
theorem exists_associatedSphere_horizontalCovector_bound
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (b : B) (c : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (K : Set (EuclideanSpace ℝ (Fin (n + r)))) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b c d).target) :
    let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
    let base : Z → B :=
      associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let lift (z : Z) := split.symm.toContinuousLinearMap.comp (H.lift z)
    let CP := associatedSphereProductChart S b c d
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ K, ∀ (ξ : EuclideanSpace ℝ (Fin n))
      (η : EuclideanSpace ℝ (Fin r)),
      let z₀ := CP.symm z
      let Ξ := covectorFromChart CP z₀ (split.symm (ξ, η))
      ‖covectorInChart c (base z₀) (Ξ.comp (lift z₀)) - ξ‖ ≤ D * ‖η‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin r)
  let XY := EuclideanSpace ℝ (Fin (n + r))
  let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
  let base : Z → B :=
    associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let split : XY ≃L[ℝ] X × Y := EuclideanSpace.finAddEquivProd
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let q := smoothAssociatedSphereProjection S
  let model := linearModelDiffeomorph split.symm Z
  have hchange := contMDiff_mfderiv_linearModelId split.symm Z
  have hglobal := associatedSphere_horizontalCovectorDeformation S H
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  let I := 𝓡 (n + r)
  let Cot := CotangentTotalSpace (n := n + r) (M := Z)
  let CP := associatedSphereProductChart S b c d
  let lift (z : Z) := split.symm.toContinuousLinearMap.comp (H.lift z)
  let part (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    (ξ.comp (lift z)).comp (mfderiv I (𝓡 n) base z)
  have hpart : Continuous (fun z : Cot ↦ (⟨z.proj, part z.proj z.snd⟩ : Cot)) := by
    have h := hglobal.1.comp ((continuous_const (y := (0 : ℝ))).prodMk
      (continuous_id : Continuous (id : Cot → Cot)))
    apply h.congr
    intro z
    dsimp only [Function.comp_apply, id_eq]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    rfl
  have hCP := associatedSphereProductChart_mem_maximalAtlas S b c hc d hd
  have hdiff : CP.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hCP).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hCP).mdifferentiableOn (by simp)⟩
  -- The model derivative transports the given right inverse without choosing a new lift.
  have hright (z : Z) (v : X) : mfderiv I (𝓡 n) base z (lift z v) = v := by
    have he := mfderiv_comp z (q.contMDiff.mdifferentiable (by simp) z)
      (model.symm.contMDiff.mdifferentiable (by simp) z)
    change mfderiv I (𝓡 n) base z =
      (mfderiv 𝓘(ℝ, X × Y) (𝓡 n) q z).comp
        (mfderiv I 𝓘(ℝ, X × Y) id z) at he
    rw [hchange.2.2] at he
    rw [he]
    change mfderiv 𝓘(ℝ, X × Y) (𝓡 n) q z (split (split.symm (H.lift z v))) = v
    rw [split.apply_symm_apply]
    exact H.right_inv z v
  let coord (z : XY) (w : XY) : X :=
    covectorInChart c (base (CP.symm z))
      ((covectorFromChart CP (CP.symm z) w).comp (lift (CP.symm z)))
  let L (z : XY) : XY →ₗ[ℝ] X := {
    toFun := coord z
    map_add' := by
      intro u v
      ext i
      change coord z (u + v) i = coord z u i + coord z v i
      simp [coord, covectorFromChart, covectorInChart, inner_add_left]
    map_smul' := by
      intro a v
      ext i
      change coord z (a • v) i = a * coord z v i
      simp [coord, covectorFromChart, covectorInChart, inner_smul_left] }
  let M (z : XY) : Y →L[ℝ] X :=
    (L z).toContinuousLinearMap.comp
      (split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ X Y))
  -- Continuity of the actual cotangent projection gives continuity of each matrix column.
  have hM : ContinuousOn M CP.target := by
    rw [continuousOn_clm_apply]
    intro η z hz
    let w := split.symm (0, η)
    have hinput : ContinuousAt (fun y : XY ↦
        (⟨CP.symm y, covectorFromChart CP (CP.symm y) w⟩ : Cot)) z := by
      have hbase := contMDiffAt_symm_of_mem_maximalAtlas hCP hz
      have hder := ((contMDiffAt_of_mem_maximalAtlas hCP (CP.map_target hz)).mfderiv_const
        (m := (∞ : WithTop ℕ∞)) (by simp)).comp z hbase
      have hinner : ContMDiffAt I 𝓘(ℝ, CotangentModel (n + r)) ∞
          (fun _ : XY ↦ innerSL ℝ w) z := contMDiffAt_const
      have hmap : ContMDiffAt I (I.prod 𝓘(ℝ, CotangentModel (n + r))) ∞
          (fun y : XY ↦ (⟨CP.symm y, covectorFromChart CP (CP.symm y) w⟩ : Cot)) z := by
        apply (contMDiffAt_hom_bundle _).mpr
        refine ⟨hbase, ?_⟩
        apply (hinner.clm_comp hder).congr_of_eventuallyEq
        filter_upwards with y
        ext v
        simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
          Function.id_def, ContinuousLinearMap.comp_apply]
        rfl
      exact hmap.continuousAt
    have hout := hpart.continuousAt.comp hinput
    have hcoord : ContinuousAt (fun y : XY ↦
        covectorInChart CP (CP.symm y)
          (part (CP.symm y) (covectorFromChart CP (CP.symm y) w))) z := by
      apply (EuclideanSpace.equiv (Fin (n + r)) ℝ).symm.continuous.continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      let v := EuclideanSpace.single i (1 : ℝ)
      have hv : ContinuousAt (fun y : XY ↦
          (⟨CP.symm y, mfderiv I I CP.symm y v⟩ : TangentBundle I Z)) z := by
        have hs : ContMDiffAt I (I.prod I) ∞
            (fun y : XY ↦ (⟨y, v⟩ : TangentBundle I XY)) z := by
          apply contMDiffAt_totalSpace.mpr
          refine ⟨contMDiffAt_id, ?_⟩
          simpa only [trivializationAt_model_space_apply] using
            (contMDiffAt_const (I := I) (I' := I) (c := v) (x := z) (n := ∞))
        exact ((contMDiffAt_symm_of_mem_maximalAtlas hCP hz).continuousAt_tangentMap
          (x₀ := ⟨z, v⟩) (by simp)).comp
            (f := fun y : XY ↦ (⟨y, v⟩ : TangentBundle I XY)) (x := z) hs.continuousAt
      have heval := hout.clm_bundle_apply (F₁ := XY) (F₂ := ℝ) hv
      have heval' := (Bundle.Trivial.homeomorphProd Z ℝ).continuous.continuousAt.snd.comp heval
      apply heval'.congr_of_eventuallyEq
      filter_upwards [CP.open_target.mem_nhds hz] with y hy
      change part (CP.symm y) (covectorFromChart CP (CP.symm y) w)
        (mfderiv I I CP.symm (CP (CP.symm y)) v) = _
      rw [CP.right_inv hy]
      rfl
    have hfirst := split.continuous.continuousAt.fst.comp hcoord
    apply hfirst.continuousWithinAt.congr
    · intro y hy
      have h := hglobal.2 b c hc d hd (CP.symm y) (CP.map_target hy)
        (covectorFromChart CP (CP.symm y) w) 0
      have heq := (congrArg Prod.fst h).symm
      simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
      change coord y (split.symm (0, η)) = _
      exact heq
    · have h := hglobal.2 b c hc d hd (CP.symm z) (CP.map_target hz)
        (covectorFromChart CP (CP.symm z) w) 0
      have heq := (congrArg Prod.fst h).symm
      simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
      change coord z (split.symm (0, η)) = _
      exact heq
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hM.norm.mono hKChart)
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro z hz ξ η z₀ Ξ
  have hzCP : z₀ ∈ CP.source := CP.map_target (hKChart hz)
  have hzBase : base z₀ ∈ c.source := by
    have h := hzCP.1.2.1
    change (associatedSphereTrivialization S b z₀).1 ∈ c.source at h
    rwa [(associatedSphereTrivialization S b).coe_fst hzCP.1.1] at h
  -- Pure horizontal covectors are actual pullbacks, on which the given lift is a right inverse.
  let ν := covectorFromChart c (base z₀) ξ
  let νP := ν.comp (mfderiv I (𝓡 n) base z₀)
  have hcoordP : covectorInChart CP z₀ νP = split.symm (ξ, 0) := by
    apply split.injective
    rw [split.apply_symm_apply]
    have h := covectorInChart_associatedSphereProductChart_pullback S b c hc d hd z₀ hzCP ν
    change split (covectorInChart CP z₀ νP) = (covectorInChart c (base z₀) ν, 0) at h
    rwa [covectorInChart_covectorFromChart c hc (base z₀) hzBase ξ] at h
  have hcancel (α : CotangentFiber (n := n + r) z₀) :
      covectorFromChart CP z₀ (covectorInChart CP z₀ α) = α := by
    have hi : innerSL ℝ (covectorInChart CP z₀ α) =
        α.comp (mfderiv I I CP.symm (CP z₀)) := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin (n + r)) ℝ).toBasis.ext
      intro i
      simp [covectorInChart, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
      rfl
    ext v
    have hinv := congrArg (fun f : XY →L[ℝ] XY ↦ f v) (hdiff.symm_comp_deriv hzCP)
    change (mfderiv I I CP.symm (CP z₀)) (mfderiv I I CP z₀ v) = v at hinv
    exact (DFunLike.congr_fun hi (mfderiv I I CP z₀ v)).trans (congrArg α hinv)
  have hpull : covectorFromChart CP z₀ (split.symm (ξ, 0)) = νP := by
    rw [← hcoordP, hcancel]
  have haxis : L z (split.symm (ξ, 0)) = ξ := by
    change covectorInChart c (base z₀)
      ((covectorFromChart CP z₀ (split.symm (ξ, 0))).comp (lift z₀)) = ξ
    rw [hpull]
    have hν : νP.comp (lift z₀) = ν := by
      ext v
      exact congrArg ν (hright z₀ v)
    rw [hν]
    exact covectorInChart_covectorFromChart c hc (base z₀) hzBase ξ
  have hsplit : split.symm (ξ, η) = split.symm (ξ, 0) + split.symm (0, η) := by
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hformula : covectorInChart c (base z₀) (Ξ.comp (lift z₀)) - ξ = M z η := by
    change L z (split.symm (ξ, η)) - ξ = L z (split.symm (0, η))
    rw [hsplit, map_add, haxis, add_sub_cancel_left]
  rw [hformula]
  have hnorm : ‖M z‖ ≤ max D 0 := by
    have h := hD z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  exact ((M z).le_opNorm η).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg η))

end AtiyahSinger
