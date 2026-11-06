/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductHorizontalCovector
public import AtiyahSinger.Geometry.CotangentModelChange
public import AtiyahSinger.Geometry.HorizontalCotangentDeformation

/-!
# The same global horizontal deformation in the original associated charts

Public module ID: M0093.

Transport the deformation fixed by the supplied horizontal lift through the
specified Euclidean model change. Its horizontal coordinate is the affine
interpolation from the pulled base covector to the original horizontal chart
coordinate; its vertical coordinate scales by the same parameter. Every
original product chart sees this one global deformation. The symbol homotopy
uses its horizontal coordinate and the unscaled original vertical coordinate.
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
/-- One supplied horizontal lift determines the global deformation in every original chart. -/
theorem associatedSphere_horizontalCovectorDeformation
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
    let base : Z → B :=
      associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := linearModelChartedSpace split.symm Z
    letI := isManifold_linearModelChartedSpace split.symm Z
    let lift (z : Z) := split.symm.toContinuousLinearMap.comp (H.lift z)
    let part (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
      (ξ.comp (lift z)).comp (mfderiv (𝓡 (n + r)) (𝓡 n) base z)
    let deformation (t : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
      (1 - t) • part z ξ + t • ξ
    Continuous (fun p : ℝ × CotangentTotalSpace (n := n + r) (M := Z) ↦
      (⟨p.2.proj, deformation p.1 p.2.proj p.2.snd⟩ :
        CotangentTotalSpace (n := n + r) (M := Z))) ∧
      ∀ (b : B) (c : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n))),
        c ∈ atlas (EuclideanSpace ℝ (Fin n)) B →
        ∀ d : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)),
          d ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r) →
          let CP := associatedSphereProductChart S b c d
          ∀ z ∈ CP.source, ∀ (ξ : CotangentFiber (n := n + r) z) (t : ℝ),
            split (covectorInChart CP z (deformation t z ξ)) =
              ((1 - t) • covectorInChart c (base z) (ξ.comp (lift z)) +
                t • (split (covectorInChart CP z ξ)).1,
                t • (split (covectorInChart CP z ξ)).2) := by
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
  let Old := TotalSpace ((X × Y) →L[ℝ] ℝ)
    (fun z : Z ↦ TangentSpace 𝓘(ℝ, X × Y) z →L[ℝ] ℝ)
  have hold := H.continuous_cotangentDeformation q (associatedSphereProjection_isSubmersion S)
  let e := cotangentLinearModelHomeomorph split.symm Z
  let model := linearModelDiffeomorph split.symm Z
  have hchange := contMDiff_mfderiv_linearModelId split.symm Z
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  let New := CotangentTotalSpace (n := n + r) (M := Z)
  let lift (z : Z) := split.symm.toContinuousLinearMap.comp (H.lift z)
  let part (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    (ξ.comp (lift z)).comp (mfderiv (𝓡 (n + r)) (𝓡 n) base z)
  let deformation (t : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    (1 - t) • part z ξ + t • ξ
  have he (z : Old) : e z = (⟨z.proj, z.snd.comp split.toContinuousLinearMap⟩ : New) := rfl
  have hei (z : New) : e.symm z =
      (⟨z.proj, z.snd.comp split.symm.toContinuousLinearMap⟩ : Old) := by
    apply e.injective
    rw [e.apply_symm_apply, he]
    apply congrArg (fun ξ ↦ (⟨z.proj, ξ⟩ : New))
    apply ContinuousLinearMap.ext
    intro v
    exact (congrArg z.snd (split.symm_apply_apply v)).symm
  have hderiv (z : Z) : mfderiv (𝓡 (n + r)) (𝓡 n) base z =
      (mfderiv 𝓘(ℝ, X × Y) (𝓡 n) q z).comp split.toContinuousLinearMap := by
    have hd := mfderiv_comp z (q.contMDiff.mdifferentiable (by simp) z)
      (model.symm.contMDiff.mdifferentiable (by simp) z)
    change mfderiv (𝓡 (n + r)) (𝓡 n) base z =
      (mfderiv 𝓘(ℝ, X × Y) (𝓡 n) q z).comp
        (mfderiv (𝓡 (n + r)) 𝓘(ℝ, X × Y) id z) at hd
    rw [hchange.2.2] at hd
    exact hd
  constructor
  · -- Conjugate the single global deformation, retaining both literal model maps.
    have hc := e.continuous.comp (hold.comp
      (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
    apply hc.congr
    intro p
    dsimp only [Function.comp_apply]
    rw [hei]
    rw [he]
    apply congrArg (fun ξ ↦ (⟨p.2.proj, ξ⟩ : New))
    apply ContinuousLinearMap.ext
    intro v
    change (1 - p.1) • p.2.snd (split.symm (H.lift p.2.proj
        (mfderiv 𝓘(ℝ, X × Y) (𝓡 n) q p.2.proj (split v)))) +
      p.1 • p.2.snd (split.symm (split v)) =
      (1 - p.1) • p.2.snd (split.symm (H.lift p.2.proj
        (mfderiv (𝓡 (n + r)) (𝓡 n) base p.2.proj v))) + p.1 • p.2.snd v
    have hd := congrArg (fun L : XY →L[ℝ] X ↦ L v) (hderiv p.2.proj)
    have hfirst := congrArg
      (fun w : X ↦ (1 - p.1) • p.2.snd (split.symm (H.lift p.2.proj w))) hd
    have hsecond := congrArg (fun w : XY ↦ p.1 • p.2.snd w) (split.symm_apply_apply v)
    exact congrArg₂ (fun a b : ℝ ↦ a + b) hfirst.symm hsecond
  · intro b c hc d hd
    dsimp only
    intro z hz ξ t
    let CP := associatedSphereProductChart S b c d
    have hbase := covectorInChart_associatedSphereProductChart_pullback
      S b c hc d hd z hz (ξ.comp (lift z))
    change split (covectorInChart CP z (part z ξ)) =
      (covectorInChart c (base z) (ξ.comp (lift z)), 0) at hbase
    have hlinear : covectorInChart CP z (deformation t z ξ) =
        (1 - t) • covectorInChart CP z (part z ξ) + t • covectorInChart CP z ξ := by
      ext i
      rfl
    rw [hlinear, map_add, map_smul, map_smul, hbase]
    apply Prod.ext
    · rfl
    · change (1 - t) • (0 : Y) + t • (split (covectorInChart CP z ξ)).2 = _
      simp only [smul_zero, zero_add]
      rfl

end AtiyahSinger
