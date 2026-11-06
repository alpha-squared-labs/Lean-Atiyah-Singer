/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductVerticalCovector
public import AtiyahSinger.Geometry.AssociatedSphereVerticalCotangent

/-!
# The chart vertical covector is the actual fiber restriction

Public module ID: M0216.

For a normalized principal representative, the sphere covector obtained from
the inverse trivialization derivative is exactly the restriction along the
original fiber-inclusion derivative. The fixed flattening of the total tangent
model is retained. This identifies the chart formula with the canonical
vertical cotangent comparison and does not identify tangent vectors with
covectors by a metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same chart vertical covector restricts the original total covector to its actual fiber. -/
theorem associatedSphereVerticalCovector_eq_fiberRestriction
    (b : B) (p : P) (hp : projection p ∈ (S.trivialization b).baseSet)
    (hg : (S.trivialization b p).2 = 1) (y : OrthogonalSphere r) :
    letI : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
    letI := associatedSphereChartedSpace S
    let v := mfderiv (𝓡 r) 𝓘(ℝ, X × Y)
      (associatedBundleMk G P (OrthogonalSphere r) p) y
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := linearModelChartedSpace split.symm Z
    let t := (associatedSphereTrivialization S b).toOpenPartialHomeomorph
    ∀ ξ : H →L[ℝ] ℝ,
      ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r)) t.symm (projection p, y)).comp
        (ContinuousLinearMap.inr ℝ X Y)) =
      (ξ.comp split.symm.toContinuousLinearMap).comp v := by
  classical
  let : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
  let I := 𝓘(ℝ, X × Y)
  let K := 𝓡 (n + r)
  let : IsManifold I ∞ (B × OrthogonalSphere r) := by
    dsimp only [I]
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod B (OrthogonalSphere r)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let i := associatedBundleMk G P (OrthogonalSphere r) p
  let v : Y →L[ℝ] X × Y := mfderiv (𝓡 r) I i y
  have hi : ContMDiff (𝓡 r) I ∞ i := (smoothAssociatedSphereFiberInclusion S p).contMDiff
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let e := linearModelDiffeomorph split.symm Z
  have hchange := contMDiff_mfderiv_linearModelId split.symm Z
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  let t := associatedSphereTrivialization S b
  have htbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hit (y' : OrthogonalSphere r) : i y' ∈ t.source :=
    t.mem_source.mpr (htbase.symm ▸ hp)
  have hforward (y' : OrthogonalSphere r) : t (i y') = (projection p, y') := by
    have h : t (i y') = (projection p, (S.trivialization b p).2 • y') :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y' hp
    rw [hg, one_smul] at h
    exact h
  have hinverse (y' : OrthogonalSphere r) : t.toOpenPartialHomeomorph.symm
      (projection p, y') = i y' := by
    rw [← hforward y']
    exact t.toOpenPartialHomeomorph.left_inv (hit y')
  -- The normalized slice is the original quotient fiber inclusion on every sphere point.
  have hslice : (t.toOpenPartialHomeomorph.symm ∘ fun y' : OrthogonalSphere r ↦
      (projection p, y')) = i := funext hinverse
  have ht : MDifferentiableAt I K t.toOpenPartialHomeomorph.symm (projection p, y) := by
    have h := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have hinv : ContMDiffOn ((𝓡 n).prod (𝓡 r)) K ∞
        t.toOpenPartialHomeomorph.symm t.target := e.contMDiff.comp_contMDiffOn h.2
    rw [← modelWithCornersSelf_prod] at hinv
    have htarget : (projection p, y) ∈ t.target := t.mem_target.mpr (htbase.symm ▸ hp)
    exact (hinv.contMDiffAt (t.open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
  have hgmap : MDifferentiableAt (𝓡 r) I (fun y' : OrthogonalSphere r ↦ (projection p, y')) y := by
    dsimp only [I]
    rw [modelWithCornersSelf_prod]
    exact mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hgderiv : mfderiv (𝓡 r) I (fun y' : OrthogonalSphere r ↦ (projection p, y')) y =
      ContinuousLinearMap.inr ℝ X Y := by
    have h := mfderiv_prodMk (I := 𝓡 r) (I' := 𝓡 n) (I'' := 𝓡 r)
      (f := fun _ : OrthogonalSphere r ↦ projection p) (g := id) (x := y)
      mdifferentiableAt_const mdifferentiableAt_id
    rw [mfderiv_const, mfderiv_id] at h
    rw [← modelWithCornersSelf_prod] at h
    exact h
  have hchart := mfderiv_comp y ht hgmap
  rw [hslice, hgderiv] at hchart
  -- The original total model is changed by precisely the same fixed linear equivalence.
  have hmodel := mfderiv_comp y
    (hchange.1.1.mdifferentiable (by simp) (i y)) (hi.mdifferentiable (by simp) y)
  change mfderiv (𝓡 r) K i y = _ at hmodel
  rw [hchange.2.1] at hmodel
  change mfderiv (𝓡 r) K i y = split.symm.toContinuousLinearMap.comp v at hmodel
  change ∀ ξ : H →L[ℝ] ℝ, _
  intro ξ
  have hderiv := hchart.symm.trans hmodel
  exact congrArg (fun L : Y →L[ℝ] H ↦ ξ.comp L) hderiv

end AtiyahSinger
