/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Positive comparison of two metrics on the same real bundle

Public module ID: M1346.

The inverse Riesz map of the second metric composed with the first metric's
Riesz map gives an automorphism of the original bundle. Both total maps are
smooth in the native charts, and its quadratic form with respect to the first
metric is strictly positive. No compactness or uniform lower bound is needed.

The comparison is used in the actual normal Thom/pole normalization of P08.
Its construction leaves the fiber topology, base model and ordered bundle
coordinates unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology
open scoped Manifold ContDiff

variable {EB HB X F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] (I : ModelWithCorners ℝ EB HB)
  [TopologicalSpace X] [ChartedSpace HB X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (W : X → Type*) [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace F W)] [FiberBundle F W] [VectorBundle ℝ F W]

set_option maxSynthPendingDepth 30 in
/-- The specified two metrics determine a smooth, strictly positive native comparison. -/
theorem exists_positiveRieszComparison
    (g₀ g₁ : ContMDiffRiemannianMetric I ∞ F W) :
    ∃ A : ∀ x, W x ≃L[ℝ] W x,
      (∀ x (v w : W x), g₁.inner x (A x v) w = g₀.inner x v w) ∧
      ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, A z.proj z.snd⟩ : TotalSpace F W)) ∧
      ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, (A z.proj).symm z.snd⟩ : TotalSpace F W)) ∧
      ∀ x (v : W x), v ≠ 0 → 0 < g₀.inner x v (A x v) := by
  classical
  let D := fun x : X ↦ W x →L[ℝ] ℝ
  let FD := F →L[ℝ] ℝ
  let e (g : ContMDiffRiemannianMetric I ∞ F W) (x : X) : W x ≃L[ℝ] D x := by
    -- Pin down the supplied metric structures before inferring completeness of this fiber.
    let g' := g.toRiemannianMetric
    let : NormedAddCommGroup (W x) :=
      (g'.toCore x).toNormedAddCommGroupOfTopology (g'.continuousAt x) (g'.isVonNBounded x)
    let : InnerProductSpace ℝ (W x) :=
      .ofCoreOfTopology (g'.toCore x) (g'.continuousAt x) (g'.isVonNBounded x)
    let : FiniteDimensional ℝ (W x) := VectorBundle.finiteDimensional ℝ F W x
    let : CompleteSpace (W x) := FiniteDimensional.complete ℝ (W x)
    exact (InnerProductSpace.toDual ℝ (W x)).toContinuousLinearEquiv
  have hforward (g : ContMDiffRiemannianMetric I ∞ F W) :
      ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, FD)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, e g z.proj z.snd⟩ : TotalSpace FD D)) := by
    have h : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F →L[ℝ] FD)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, g.inner z.proj⟩ :
          TotalSpace (F →L[ℝ] FD) (fun x ↦ W x →L[ℝ] D x))) :=
      g.contMDiff.comp (contMDiff_proj (F := F) W (IB := I))
    exact h.clm_bundle_apply (F₁ := F) (F₂ := FD) (E₁ := W) (E₂ := D) contMDiff_id
  have hbackward (g : ContMDiffRiemannianMetric I ∞ F W) :
      ContMDiff (I.prod 𝓘(ℝ, FD)) (I.prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace FD D ↦ (⟨z.proj, (e g z.proj).symm z.snd⟩ :
          TotalSpace F W)) := by
    -- The inverse uses the inverse of the same metric matrix in each original frame.
    have hcoordinates (x : X) : ContMDiffAt I 𝓘(ℝ, FD →L[ℝ] F) ∞
        (fun y ↦ ContinuousLinearMap.inCoordinates FD D F W
          x y x y (e g y).symm.toContinuousLinearMap) x := by
      let a := trivializationAt F W x
      let b := trivializationAt FD D x
      let P (y : X) : F →L[ℝ] FD :=
        (b.continuousLinearMapAt ℝ y).comp
          ((e g y).toContinuousLinearMap.comp (a.symmL ℝ y))
      let Q (y : X) : FD →L[ℝ] F :=
        (a.continuousLinearMapAt ℝ y).comp
          ((e g y).symm.toContinuousLinearMap.comp (b.symmL ℝ y))
      have hPQ (y : X) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
          (P y).comp (Q y) = ContinuousLinearMap.id ℝ FD ∧
            (Q y).comp (P y) = ContinuousLinearMap.id ℝ F := by
        constructor
        · apply ContinuousLinearMap.ext
          intro v
          change b.continuousLinearMapAt ℝ y (e g y (a.symmL ℝ y
            (a.continuousLinearMapAt ℝ y ((e g y).symm (b.symmL ℝ y v))))) = v
          rw [a.symmL_continuousLinearMapAt (R := ℝ) ha, (e g y).apply_symm_apply,
            b.continuousLinearMapAt_symmL hb]
        · apply ContinuousLinearMap.ext
          intro v
          change a.continuousLinearMapAt ℝ y ((e g y).symm (b.symmL ℝ y
            (b.continuousLinearMapAt ℝ y (e g y (a.symmL ℝ y v))))) = v
          rw [b.symmL_continuousLinearMapAt (R := ℝ) hb, (e g y).symm_apply_apply,
            a.continuousLinearMapAt_symmL ha]
      have hax : x ∈ a.baseSet := mem_baseSet_trivializationAt F W x
      have hbx : x ∈ b.baseSet := mem_baseSet_trivializationAt FD D x
      have hP : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] FD) ∞ P x :=
        (contMDiffAt_hom_bundle (fun y ↦ TotalSpace.mk'
          (F →L[ℝ] FD) y (g.inner y))).mp (g.contMDiff x) |>.2
      have hPi : (P x).IsInvertible :=
        ContinuousLinearMap.IsInvertible.of_inverse (hPQ x hax hbx).1 (hPQ x hax hbx).2
      have hinverse := (hPi.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x hP
      change ContMDiffAt I 𝓘(ℝ, FD →L[ℝ] F) ∞ Q x
      apply hinverse.congr_of_eventuallyEq
      filter_upwards [a.open_baseSet.mem_nhds hax, b.open_baseSet.mem_nhds hbx] with y ha hb
      exact (ContinuousLinearMap.inverse_eq (hPQ y ha hb).1 (hPQ y ha hb).2).symm
    intro z
    have hproj := (contMDiff_proj (F := FD) D (IB := I) (n := ∞)).contMDiffAt (x := z)
    exact ((hcoordinates z.proj).comp z hproj).clm_apply_of_inCoordinates
      contMDiffAt_id hproj
  let A (x : X) : W x ≃L[ℝ] W x := (e g₀ x).trans (e g₁ x).symm
  have hpair (x : X) (v w : W x) : g₁.inner x (A x v) w = g₀.inner x v w := by
    change (e g₁ x ((e g₁ x).symm (e g₀ x v))) w = (e g₀ x v) w
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨A, hpair, (hbackward g₁).comp (hforward g₀),
    (hbackward g₀).comp (hforward g₁), ?_⟩
  -- Pair with the same image vector; positivity of g₁ gives positivity relative to g₀.
  intro x v hv
  have hAv : A x v ≠ 0 := fun h ↦ hv ((A x).injective (h.trans (map_zero (A x)).symm))
  rw [← hpair x v (A x v)]
  exact g₁.pos x (A x v) hAv

end AtiyahSinger
