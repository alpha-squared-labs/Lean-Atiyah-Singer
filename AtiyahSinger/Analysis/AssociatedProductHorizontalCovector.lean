/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductCovectorCoordinates

/-!
# Horizontal covectors in the actual associated product chart

Public module ID: M0106.

Pullback along the original sphere-bundle projection has exactly the base
chart frequency and zero vertical frequency. This is a statement about the
actual derivative and its dual map, including the fixed Euclidean flattening.
It is used to identify the literal finite horizontal axis and the same-symbol
cotangent comparison.
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
set_option maxHeartbeats 1600000 in

/-- The actual pulled-back base covector has its original horizontal and zero vertical frequency. -/
theorem covectorInChart_associatedSphereProductChart_pullback
    (b : B) (c : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)) :
    let ZC := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
    let base : ZC → B :=
      associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm ZC
    let CP := associatedSphereProductChart S b c d
    ∀ z ∈ CP.source, ∀ ξ : TangentSpace (𝓡 n) (base z) →L[ℝ] ℝ,
      split (covectorInChart CP z (ξ.comp (mfderiv (𝓡 (n + r)) (𝓡 n) base z))) =
        (covectorInChart c (base z) ξ, 0) := by
  classical
  let XC := EuclideanSpace ℝ (Fin n)
  let YC := EuclideanSpace ℝ (Fin r)
  let H := EuclideanSpace ℝ (Fin (n + r))
  let ZC := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
  let base : ZC → B := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let split : H ≃L[ℝ] XC × YC := EuclideanSpace.finAddEquivProd
  let pr : H →L[ℝ] XC := (ContinuousLinearMap.fst ℝ XC YC).comp split.toContinuousLinearMap
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let model := linearModelDiffeomorph split.symm ZC
  let := linearModelChartedSpace split.symm ZC
  let := isManifold_linearModelChartedSpace split.symm ZC
  let CP := associatedSphereProductChart S b c d
  let t := associatedSphereTrivialization S b
  change ∀ z ∈ CP.source, ∀ ξ : TangentSpace (𝓡 n) (base z) →L[ℝ] ℝ, _
  intro z hz ξ
  have hC := associatedSphereProductChart_mem_maximalAtlas S b c hc d hd
  have hproj : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ base :=
    (smoothAssociatedSphereProjection S).contMDiff.comp model.symm.contMDiff
  -- On the original chart, projection after the inverse chart is exactly the base inverse chart.
  have hcoord (u : ZC) (hu : u ∈ CP.source) :
      base u ∈ c.source ∧ pr (CP u) = c (base u) := by
    have ht : u ∈ t.source := hu.1.1
    have hbase : (t u).1 ∈ c.source := hu.1.2.1
    rw [t.coe_fst ht] at hbase
    refine ⟨hbase, ?_⟩
    change (split (split.symm ((c.prod d) (t u)))).1 = c (base u)
    rw [split.apply_symm_apply]
    change c (t u).1 = c (base u)
    rw [t.coe_fst ht]
  have hinv (u : H) (hu : u ∈ CP.target) : base (CP.symm u) = c.symm (pr u) := by
    have h := hcoord (CP.symm u) (CP.map_target hu)
    calc
      _ = c.symm (c (base (CP.symm u))) := (c.left_inv h.1).symm
      _ = c.symm (pr (CP (CP.symm u))) := congrArg c.symm h.2.symm
      _ = _ := by rw [CP.right_inv hu]
  -- Differentiate that local equality to compare the same projection and inverse-chart maps.
  have hnear : (base ∘ CP.symm) =ᶠ[𝓝 (CP z)] (c.symm ∘ pr) :=
    Filter.eventuallyEq_of_mem (CP.open_target.mem_nhds (CP.map_source hz)) hinv
  have hCsmooth := contMDiffAt_symm_of_mem_maximalAtlas hC (CP.map_source hz)
  have hCdiff := hCsmooth.mdifferentiableAt (by simp)
  have hcsmooth := contMDiffAt_symm_of_mem_maximalAtlas
    (subset_maximalAtlas (I := 𝓡 n) (n := ∞) hc) (c.map_source (hcoord z hz).1)
  have hcdiff := hcsmooth.mdifferentiableAt (by simp)
  have hprdiff : MDifferentiableAt (𝓡 (n + r)) (𝓡 n) pr (CP z) :=
    pr.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hcdiff' : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (pr (CP z)) := by
    rw [(hcoord z hz).2]
    exact hcdiff
  have hder : (mfderiv (𝓡 (n + r)) (𝓡 n) base z).comp
      (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) CP.symm (CP z)) =
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c (base z))).comp pr := by
    have h := hnear.mfderiv_eq (I := 𝓡 (n + r)) (I' := 𝓡 n)
    rw [mfderiv_comp (CP z) (hproj.mdifferentiable (by simp) _) hCdiff,
      mfderiv_comp (CP z) hcdiff' hprdiff, CP.left_inv hz, (hcoord z hz).2] at h
    have hp : mfderiv (𝓡 (n + r)) (𝓡 n) pr (CP z) = pr :=
      pr.hasFDerivAt.hasMFDerivAt.mfderiv
    rwa [hp] at h
  -- The dual map is determined on the original horizontal and vertical coordinate basis vectors.
  have hleft (i : Fin n) : pr (EuclideanSpace.single (Fin.castAdd r i) 1) =
      EuclideanSpace.single i 1 := by
    ext j
    change EuclideanSpace.single (Fin.castAdd r i) (1 : ℝ) (Fin.castAdd r j) = _
    simp
  have hright (j : Fin r) : pr (EuclideanSpace.single (Fin.natAdd n j) 1) = 0 := by
    ext i
    change EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) (Fin.castAdd r i) = 0
    simp only [PiLp.single_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  apply Prod.ext
  · ext i
    change ξ (mfderiv (𝓡 (n + r)) (𝓡 n) base z
      (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) CP.symm (CP z)
        (EuclideanSpace.single (Fin.castAdd r i) 1))) =
      ξ (mfderiv (𝓡 n) (𝓡 n) c.symm (c (base z)) (EuclideanSpace.single i 1))
    have h := congrArg (fun L : H →L[ℝ] XC ↦ L (EuclideanSpace.single (Fin.castAdd r i) 1)) hder
    change mfderiv (𝓡 (n + r)) (𝓡 n) base z
      (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) CP.symm (CP z)
        (EuclideanSpace.single (Fin.castAdd r i) 1)) =
      mfderiv (𝓡 n) (𝓡 n) c.symm (c (base z))
        (pr (EuclideanSpace.single (Fin.castAdd r i) 1)) at h
    rw [hleft] at h
    exact congrArg ξ h
  · ext j
    change ξ (mfderiv (𝓡 (n + r)) (𝓡 n) base z
      (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) CP.symm (CP z)
        (EuclideanSpace.single (Fin.natAdd n j) 1))) = 0
    have h := congrArg (fun L : H →L[ℝ] XC ↦ L (EuclideanSpace.single (Fin.natAdd n j) 1)) hder
    change mfderiv (𝓡 (n + r)) (𝓡 n) base z
      (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) CP.symm (CP z)
        (EuclideanSpace.single (Fin.natAdd n j) 1)) =
      mfderiv (𝓡 n) (𝓡 n) c.symm (c (base z))
        (pr (EuclideanSpace.single (Fin.natAdd n j) 1)) at h
    rw [hright] at h
    have hzero : mfderiv (𝓡 n) (𝓡 n) c.symm (c (base z)) (0 : XC) = 0 :=
      map_zero (show XC →L[ℝ] XC from mfderiv (𝓡 n) (𝓡 n) c.symm (c (base z)))
    exact (congrArg ξ h).trans ((congrArg ξ hzero).trans (map_zero ξ))

end AtiyahSinger
