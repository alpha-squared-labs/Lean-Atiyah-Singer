/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateFrequencyFamilies

import AtiyahSinger.Geometry.CompactParameterIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Absolute Jacobians of coordinate families

Public module ID: M0411.

Jointly continuous spatial jets of the inverse coordinate maps induce continuous
spatial jets of the two coordinate-amplitude measure factors on the common valid
segment and invertibility locus. The determinants remain absolute, so the result
allows either orientation of the coordinate maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set Topology
open scoped ContDiff Manifold

/-- The actual coordinate, frequency, and absolute-Jacobian factors are smooth on a valid locus. -/
theorem contDiffOn_coordinateChange_factors {n : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hseg : ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target)
    (hinv : ∀ z ∈ W, (averagedFDeriv e.symm z.1 z.2).IsInvertible) :
    ContDiffOn ℝ ∞ (fun z ↦
      ((e.symm z.1, coordinateFrequencyChange e z.1 z.2), coordinateJacobianFactor e z.1 z.2))
      W := by
  let X := EuclideanSpace ℝ (Fin n)
  have hAvg : ContDiffOn ℝ ∞ (fun z ↦ averagedFDeriv e.symm z.1 z.2) W := by
    let X := EuclideanSpace ℝ (Fin n)
    let J := Set.Icc (0 : ℝ) 1
    let f : J × (X × X) → (X →L[ℝ] X) :=
      fun p ↦ fderiv ℝ e.symm ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2)
    -- The interval carries its usual smooth structure with boundary. Thus all parameters,
    -- including the two endpoints, fall under the compact-parameter integral theorem.
    have ht : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ) ∞
        (fun p : J × (X × X) ↦ (p.1 : ℝ)) :=
      contMDiff_subtypeVal_Icc.comp contMDiff_fst
    have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X) ∞
        (fun p : J × (X × X) ↦ (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
      (ht.smul (contDiff_fst.contMDiff.comp contMDiff_snd)).add
        (((contDiff_const.sub contDiff_id).contMDiff.comp ht).smul
          (contDiff_snd.contMDiff.comp contMDiff_snd))
    have hf : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X →L[ℝ] X) ∞
        f (Set.univ ×ˢ W) := by
      intro p hp
      have hmem : (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2 ∈ e.target := by
        apply hseg p.2 hp.2
        rw [segment_eq_image]
        exact ⟨(p.1 : ℝ), p.1.property, by simp [add_comm]⟩
      have hd : ContDiffAt ℝ ∞ (fderiv ℝ e.symm)
          ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
        (hψ.contDiffAt (e.open_target.mem_nhds hmem)).fderiv_right (by simp)
      exact (hd.contMDiffAt.comp p (hc p)).contMDiffWithinAt
    have h := contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
      (volume : Measure J) hW hf
    -- The subtype measure is ordinary Lebesgue measure restricted to [0,1]. Endpoints
    -- have zero measure, so this is exactly the original oriented interval integral.
    convert h using 1
    funext z
    dsimp only [f, J, averagedFDeriv]
    have he := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
      (fun t ↦ fderiv ℝ e.symm (t • z.1 + (1 - t) • z.2))
    rw [integral_Icc_eq_integral_Ioc] at he
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact he.symm
  have hxTarget (z : X × X) (hz : z ∈ W) : z.1 ∈ e.target :=
    hseg z hz (right_mem_segment ℝ z.2 z.1)
  have hyTarget (z : X × X) (hz : z ∈ W) : z.2 ∈ e.target :=
    hseg z hz (left_mem_segment ℝ z.2 z.1)
  let Jadj : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ] (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro c A; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hAdj : ContDiffOn ℝ ∞
      (fun z ↦ (averagedFDeriv e.symm z.1 z.2).adjoint) W :=
    Jadj.contDiff.comp_contDiffOn hAvg
  have hAdjInv (z : X × X) (hz : z ∈ W) :
      (averagedFDeriv e.symm z.1 z.2).adjoint.IsInvertible := by
    let A := averagedFDeriv e.symm z.1 z.2
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := A.inverse.adjoint)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).inverse_comp_self)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).self_comp_inverse)
  have hΘ : ContDiffOn ℝ ∞ (fun z ↦ coordinateFrequencyChange e z.1 z.2) W := by
    intro z hz
    exact ((hAdjInv z hz).contDiffAt_map_inverse.comp z
      (hAdj.contDiffAt (hW.mem_nhds hz))).contDiffWithinAt
  have hΘinv (z : X × X) (hz : z ∈ W) :
      (coordinateFrequencyChange e z.1 z.2).IsInvertible := (hAdjInv z hz).inverse
  have hφ : ContDiffOn ℝ ∞ (fun z : X × X ↦ e.symm z.1) W := by
    intro z hz
    exact ((hψ.contDiffAt (e.open_target.mem_nhds (hxTarget z hz))).comp z
      contDiffAt_fst).contDiffWithinAt
  -- Invertibility makes both absolute Jacobians smooth; orientation is unrestricted.
  have hdetSmooth (D : X × X → X →L[ℝ] X) (z : X × X)
      (hD : ContDiffAt ℝ ∞ D z) : ContDiffAt ℝ ∞ (fun w ↦ (D w).det) z := by
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ hσ
    apply ContDiffAt.mul contDiffAt_const
    apply contDiffAt_prod
    intro i hi
    simp only [LinearMap.toMatrix_apply]
    exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp z
      (hD.clm_apply contDiffAt_const))
  have hγ : ContDiffOn ℝ ∞ (fun z ↦ coordinateJacobianFactor e z.1 z.2) W := by
    intro z hz
    have hyt := hyTarget z hz
    have hψAt := hψ.contDiffAt (e.open_target.mem_nhds hyt)
    have hDψ : ContDiffAt ℝ ∞ (fun w : X × X ↦ fderiv ℝ e.symm w.2) z :=
      (hψAt.fderiv_right (m := ∞) (by simp)).comp z contDiffAt_snd
    have hdetψ : (fderiv ℝ e.symm z.2).det ≠ 0 := by
      have hforward := (he.contDiffAt
        (e.open_source.mem_nhds (e.map_target hyt))).differentiableAt (by simp)
      have hright : (fderiv ℝ e (e.symm z.2)).comp (fderiv ℝ e.symm z.2) =
          ContinuousLinearMap.id ℝ X := by
        apply (hforward.hasFDerivAt.comp z.2
          (hψAt.differentiableAt (by simp)).hasFDerivAt).unique
        apply (hasFDerivAt_id z.2).congr_of_eventuallyEq
        filter_upwards [e.open_target.mem_nhds hyt] with y hy
        exact e.right_inv hy
      have hd := congrArg ContinuousLinearMap.det hright
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
        LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
      exact right_ne_zero_of_mul_eq_one hd
    have hdetΘ : (coordinateFrequencyChange e z.1 z.2).det ≠ 0 := by
      obtain ⟨A, hA⟩ := hΘinv z hz
      rw [← hA]
      exact A.toLinearEquiv.isUnit_det'.ne_zero
    exact ((hdetSmooth _ z hDψ).abs hdetψ).mul
      ((hdetSmooth _ z (hΘ.contDiffAt (hW.mem_nhds hz))).abs hdetΘ) |>.contDiffWithinAt
  exact (hφ.prodMk hΘ).prodMk hγ

private theorem continuousOn_jet_pair_family
    {Y Z F H : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : Y → Z → F) (g : Y → Z → H) (S : Set (Y × Z))
    (hf : ∀ p ∈ S, ContDiffAt ℝ ∞ (f p.1) p.2)
    (hg : ∀ p ∈ S, ContDiffAt ℝ ∞ (g p.1) p.2)
    (hfj : ∀ k : ℕ, ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (f p.1) p.2) S)
    (hgj : ∀ k : ℕ, ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (g p.1) p.2) S) (k : ℕ) :
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (fun z ↦ (f p.1 z, g p.1 z)) p.2) S := by
  have h := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k ↦ Z) F H).continuous
    |>.comp_continuousOn ((hfj k).prodMk (hgj k))
  apply h.congr
  intro p hp
  exact iteratedFDeriv_prodMk (hf p hp) (hg p hp) (by simp)

private theorem continuousOn_jet_postcomp_family
    {Y Z F H : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : Y → Z → F) (g : F → H) (S : Set (Y × Z))
    (D : Set F) (hD : IsOpen D) (hmap : ∀ p ∈ S, f p.1 p.2 ∈ D)
    (hf : ∀ p ∈ S, ContDiffAt ℝ ∞ (f p.1) p.2)
    (hg : ContDiffOn ℝ ∞ g D)
    (hfj : ∀ k : ℕ, ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (f p.1) p.2) S) (k : ℕ) :
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (g ∘ f p.1) p.2) S := by
  have hc : ContinuousOn (fun p : Y × Z ↦ f p.1 p.2) S := by
    have h := (continuousMultilinearCurryFin0 ℝ Z F).continuous
      |>.comp_continuousOn (hfj 0)
    change ContinuousOn (fun p : Y × Z ↦ (iteratedFDeriv ℝ 0 (f p.1) p.2).curry0) S at h
    simpa only [ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply] using h
  have hgj (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ j g) D := by
    have h := hg.continuousOn_iteratedFDerivWithin (m := j) (by simp) hD.uniqueDiffOn
    apply h.congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen _ hD hx).symm
  exact continuousOn_iteratedFDeriv_comp_family (fun _ ↦ g) f S
    (fun p hp ↦ hg.contDiffAt (hD.mem_nhds (hmap p hp))) hf
    (fun j ↦ (hgj j).comp hc hmap) hfj k

/-- Both absolute coordinate Jacobians retain joint continuity of all spatial derivatives. -/
theorem continuousOn_iteratedFDeriv_coordinateJacobianFactor
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (e : Y → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ∀ t, ContDiffOn ℝ ∞ (e t) (e t).source)
    (hψ : ∀ t, ContDiffOn ℝ ∞ (e t).symm (e t).target)
    (hD : IsOpen {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ (e p.1).target})
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun p : Y × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ k (e p.1).symm p.2) {p | p.2 ∈ (e p.1).target})
    (W : Set (Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
    (hW : IsOpen W)
    (hseg : ∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target)
    (hinv : ∀ p ∈ W, (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible)
    (k : ℕ) :
    ContinuousOn
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (fun z ↦ coordinateJacobianFactor (e p.1) z.1 z.2) p.2) W := by
  let X := EuclideanSpace ℝ (Fin n)
  have hfactors (t : Y) : ContDiffOn ℝ ∞ (fun z ↦
      (((e t).symm z.1, coordinateFrequencyChange (e t) z.1 z.2),
        coordinateJacobianFactor (e t) z.1 z.2)) {z | (t, z) ∈ W} :=
    contDiffOn_coordinateChange_factors (e t) (he t) (hψ t) _
      (hW.preimage (continuous_const.prodMk continuous_id))
      (fun z hz ↦ hseg (t, z) hz) (fun z hz ↦ hinv (t, z) hz)
  let Θ (t : Y) (z : X × X) : X →L[ℝ] X := coordinateFrequencyChange (e t) z.1 z.2
  have hAdjInv (p : Y × (X × X)) (hp : p ∈ W) :
      (averagedFDeriv (e p.1).symm p.2.1 p.2.2).adjoint.IsInvertible := by
    let A := averagedFDeriv (e p.1).symm p.2.1 p.2.2
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := A.inverse.adjoint)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint (hinv p hp).inverse_comp_self
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint (hinv p hp).self_comp_inverse
  have hΘinv (p : Y × (X × X)) (hp : p ∈ W) : (Θ p.1 p.2).IsInvertible :=
    (hAdjInv p hp).inverse
  have hΘ (p : Y × (X × X)) (hp : p ∈ W) : ContDiffAt ℝ ∞ (Θ p.1) p.2 :=
    (hfactors p.1).fst.snd.contDiffAt
      ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp)
  have hΘj := continuousOn_iteratedFDeriv_coordinateFrequencyChange e hψ hD hjets W hW hseg hinv
  let D (t : Y) (z : X × X) : X →L[ℝ] X := fderiv ℝ (e t).symm z.2
  have hy (p : Y × (X × X)) (hp : p ∈ W) : p.2.2 ∈ (e p.1).target :=
    hseg p hp (left_mem_segment ℝ p.2.2 p.2.1)
  have hdAt (t : Y) (x : X) (hx : x ∈ (e t).target) :
      ContDiffAt ℝ ∞ (fderiv ℝ (e t).symm) x :=
    ((hψ t).contDiffAt ((e t).open_target.mem_nhds hx)).fderiv_right (by simp)
  have hDAt (p : Y × (X × X)) (hp : p ∈ W) : ContDiffAt ℝ ∞ (D p.1) p.2 :=
    (hdAt p.1 p.2.2 (hy p hp)).comp p.2 contDiffAt_snd
  have hdj (j : ℕ) : ContinuousOn
      (fun p : Y × X ↦ iteratedFDeriv ℝ j (fderiv ℝ (e p.1).symm) p.2)
      {p | p.2 ∈ (e p.1).target} := by
    let C := continuousMultilinearCurryRightEquiv' ℝ j X X
    have h := C.continuous.comp_continuousOn (hjets (j + 1))
    apply h.congr
    intro p _
    change iteratedFDeriv ℝ j (fderiv ℝ (e p.1).symm) p.2 =
      C (iteratedFDeriv ℝ (j + 1) (e p.1).symm p.2)
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact (C.apply_symm_apply _).symm
  have hDj (j : ℕ) : ContinuousOn
      (fun p : Y × (X × X) ↦ iteratedFDeriv ℝ j (D p.1) p.2) W :=
    continuousOn_iteratedFDeriv_comp_family (fun t ↦ fderiv ℝ (e t).symm)
      (fun _ : Y ↦ Prod.snd) W (fun p hp ↦ hdAt p.1 p.2.2 (hy p hp))
      (fun _ _ ↦ contDiffAt_snd)
      (fun l ↦ (hdj l).comp (continuous_fst.prodMk continuous_snd.snd).continuousOn hy)
      (fun l ↦ ((contDiff_snd : ContDiff ℝ ∞ (Prod.snd : X × X → X)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn) j
  -- Each original coordinate inverse derivative has nonzero determinant.
  have hdetD (p : Y × (X × X)) (hp : p ∈ W) : (D p.1 p.2).det ≠ 0 := by
    have hyt := hy p hp
    have hf := ((he p.1).contDiffAt
      ((e p.1).open_source.mem_nhds ((e p.1).map_target hyt))).differentiableAt (by simp)
    have hb := ((hψ p.1).contDiffAt ((e p.1).open_target.mem_nhds hyt)).differentiableAt
      (by simp)
    have hr : (fderiv ℝ (e p.1) ((e p.1).symm p.2.2)).comp (D p.1 p.2) =
        ContinuousLinearMap.id ℝ X := by
      apply (hf.hasFDerivAt.comp p.2.2 hb.hasFDerivAt).unique
      apply (hasFDerivAt_id p.2.2).congr_of_eventuallyEq
      filter_upwards [(e p.1).open_target.mem_nhds hyt] with y hy
      exact (e p.1).right_inv hy
    have hd := congrArg ContinuousLinearMap.det hr
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
    exact right_ne_zero_of_mul_eq_one hd
  have hdetΘ (p : Y × (X × X)) (hp : p ∈ W) : (Θ p.1 p.2).det ≠ 0 := by
    obtain ⟨A, hA⟩ := hΘinv p hp
    rw [← hA]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  have hdetSmooth : ContDiff ℝ ∞ (fun A : X →L[ℝ] X ↦ A.det) := by
    rw [contDiff_iff_contDiffAt]
    intro A
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ hσ
    apply ContDiffAt.mul contDiffAt_const
    apply contDiffAt_prod
    intro i hi
    simp only [LinearMap.toMatrix_apply]
    exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp A
      (contDiffAt_id.clm_apply contDiffAt_const))
  let S : Set ((X →L[ℝ] X) × (X →L[ℝ] X)) := {p | p.1.det ≠ 0 ∧ p.2.det ≠ 0}
  have hS : IsOpen S :=
    (isOpen_compl_singleton.preimage (hdetSmooth.continuous.comp continuous_fst)).inter
      (isOpen_compl_singleton.preimage (hdetSmooth.continuous.comp continuous_snd))
  have hF : ContDiffOn ℝ ∞ (fun p : (X →L[ℝ] X) × (X →L[ℝ] X) ↦
      |p.1.det| * |p.2.det|) S := by
    intro p hp
    exact (((hdetSmooth.contDiffAt.comp p contDiffAt_fst).abs hp.1).mul
      ((hdetSmooth.contDiffAt.comp p contDiffAt_snd).abs hp.2)).contDiffWithinAt
  exact continuousOn_jet_postcomp_family (fun t z ↦ (D t z, Θ t z))
    (fun p : (X →L[ℝ] X) × (X →L[ℝ] X) ↦ |p.1.det| * |p.2.det|) W S hS
    (fun p hp ↦ ⟨hdetD p hp, hdetΘ p hp⟩)
    (fun p hp ↦ (hDAt p hp).prodMk (hΘ p hp)) hF
    (continuousOn_jet_pair_family D Θ W hDAt hΘ hDj hΘj) k

/-- The exact coordinate amplitude has continuous spatial-frequency jets on the common locus. -/
theorem continuousOn_iteratedFDeriv_coordinateAmplitude
    {Y : Type*} [TopologicalSpace Y] {n r s : ℕ}
    (e : Y → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ∀ t, ContDiffOn ℝ ∞ (e t) (e t).source)
    (hψ : ∀ t, ContDiffOn ℝ ∞ (e t).symm (e t).target)
    (hD : IsOpen {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ (e p.1).target})
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun p : Y × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ k (e p.1).symm p.2) {p | p.2 ∈ (e p.1).target})
    (W : Set (Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
    (hW : IsOpen W)
    (hseg : ∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target)
    (hinv : ∀ p ∈ W, (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible)
    (χ : Y → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ)
    (hχ : ∀ t, ContDiffOn ℝ ∞ (χ t) {z | (t, z) ∈ W})
    (hχj : ∀ k : ℕ, ContinuousOn
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (χ p.1) p.2) W)
    (p : SymbolFunction n r s) (hp : ContDiff ℝ ∞ (Function.uncurry p)) (k : ℕ) :
    ContinuousOn
      (fun q : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
          EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (fun z ↦ coordinateAmplitude (e q.1) (χ q.1) p z.1.1 z.1.2 z.2) q.2)
      {q | (q.1, q.2.1) ∈ W} := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)
  let Φ (t : Y) (z : X × X) : X := (e t).symm z.1
  let Θ (t : Y) (z : X × X) : X →L[ℝ] X := coordinateFrequencyChange (e t) z.1 z.2
  let J (t : Y) (z : X × X) : ℝ := coordinateJacobianFactor (e t) z.1 z.2
  have hs (q : Y × (X × X)) (hq : q ∈ W) :
      ContDiffAt ℝ ∞ (fun z ↦ ((Φ q.1 z, Θ q.1 z), J q.1 z)) q.2 :=
    (contDiffOn_coordinateChange_factors (e q.1) (he q.1) (hψ q.1)
      {z | (q.1, z) ∈ W} (hW.preimage (continuous_const.prodMk continuous_id))
      (fun z hz ↦ hseg (q.1, z) hz) (fun z hz ↦ hinv (q.1, z) hz)).contDiffAt
        ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq)
  have hΦj (j : ℕ) : ContinuousOn
      (fun q : Y × (X × X) ↦ iteratedFDeriv ℝ j (Φ q.1) q.2) W :=
    continuousOn_iteratedFDeriv_comp_family (fun t ↦ (e t).symm)
      (fun _ : Y ↦ Prod.fst) W
      (fun q hq ↦ (hψ q.1).contDiffAt ((e q.1).open_target.mem_nhds
        (hseg q hq (right_mem_segment ℝ q.2.2 q.2.1))))
      (fun _ _ ↦ contDiffAt_fst)
      (fun l ↦ (hjets l).comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
        (fun q hq ↦ hseg q hq (right_mem_segment ℝ q.2.2 q.2.1)))
      (fun l ↦ ((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : X × X → X)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn) j
  have hΘj := continuousOn_iteratedFDeriv_coordinateFrequencyChange e hψ hD hjets W hW hseg hinv
  have hJj := continuousOn_iteratedFDeriv_coordinateJacobianFactor e he hψ hD hjets W hW hseg hinv
  have hpj := continuousOn_jet_pair_family Φ Θ W
    (fun q hq ↦ (hs q hq).fst.fst) (fun q hq ↦ (hs q hq).fst.snd) hΦj hΘj
  have hfj := continuousOn_jet_pair_family (fun t z ↦ (Φ t z, Θ t z)) J W
    (fun q hq ↦ (hs q hq).fst) (fun q hq ↦ (hs q hq).snd) hpj hJj
  let F := (((X × (X →L[ℝ] X)) × ℝ) × ℝ)
  let f (t : Y) (z : X × X) : F := (((Φ t z, Θ t z), J t z), χ t z)
  have hf (q : Y × (X × X)) (hq : q ∈ W) : ContDiffAt ℝ ∞ (f q.1) q.2 :=
    (hs q hq).prodMk ((hχ q.1).contDiffAt
      ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq))
  have hfsj : ∀ j : ℕ, ContinuousOn
      (fun q : Y × (X × X) ↦ iteratedFDeriv ℝ j (f q.1) q.2) W :=
    continuousOn_jet_pair_family (fun t z ↦ ((Φ t z, Θ t z), J t z)) χ W hs
      (fun q hq ↦ (hχ q.1).contDiffAt
        ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq)) hfj hχj
  -- Lift the spatial factors to the frequency product and use only smooth evaluation operations.
  let S : Set (Y × ((X × X) × X)) := {q | (q.1, q.2.1) ∈ W}
  let g (t : Y) (z : (X × X) × X) : F × X := (f t z.1, z.2)
  have hg (q : Y × ((X × X) × X)) (hq : q ∈ S) : ContDiffAt ℝ ∞ (g q.1) q.2 :=
    ((hf (q.1, q.2.1) hq).comp q.2 contDiffAt_fst).prodMk contDiffAt_snd
  have hleftj (j : ℕ) : ContinuousOn
      (fun q : Y × ((X × X) × X) ↦ iteratedFDeriv ℝ j (fun z ↦ f q.1 z.1) q.2) S :=
    continuousOn_iteratedFDeriv_comp_family f (fun _ : Y ↦ Prod.fst) S
      (fun q hq ↦ hf (q.1, q.2.1) hq) (fun _ _ ↦ contDiffAt_fst)
      (fun l ↦ (hfsj l).comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
        (fun _ hq ↦ hq))
      (fun l ↦ ((contDiff_fst : ContDiff ℝ ∞
        (Prod.fst : (X × X) × X → X × X)).continuous_iteratedFDeriv (by simp)).comp
          continuous_snd |>.continuousOn) j
  have hgj : ∀ j : ℕ, ContinuousOn
      (fun q : Y × ((X × X) × X) ↦ iteratedFDeriv ℝ j (g q.1) q.2) S :=
    continuousOn_jet_pair_family (fun t z ↦ f t z.1) (fun _ : Y ↦ Prod.snd) S
      (fun q hq ↦ (hf (q.1, q.2.1) hq).comp q.2 contDiffAt_fst)
      (fun _ _ ↦ contDiffAt_snd) hleftj
      (fun l ↦ ((contDiff_snd : ContDiff ℝ ∞ (Prod.snd : (X × X) × X → X)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn)
  let H (w : F × X) : V := (w.1.2 * w.1.1.2) • p w.1.1.1.1 (w.1.1.1.2 w.2)
  have hH : ContDiff ℝ ∞ H := by
    have hc : ContDiff ℝ ∞ (fun w : F × X ↦ (w.1.1.1.1, w.1.1.1.2 w.2)) :=
      contDiff_fst.fst.fst.fst.prodMk
        (contDiff_fst.fst.fst.snd.clm_apply contDiff_snd)
    exact (contDiff_fst.snd.mul contDiff_fst.fst.snd).smul (hp.comp hc)
  exact continuousOn_jet_postcomp_family g H S univ isOpen_univ
    (fun _ _ ↦ mem_univ _) hg hH.contDiffOn hgj k

private theorem continuous_jet_of_closed_support
    {Y X V : Type*} [TopologicalSpace Y] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Y → X → V) (S C : Set (Y × X)) (hS : IsOpen S) (hC : IsClosed C)
    (hCS : C ⊆ S) (hzero : ∀ p ∉ C, f p.1 p.2 = 0)
    (hjet : ∀ k : ℕ, ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (f p.1) p.2) S) (k : ℕ) :
    Continuous (fun p : Y × X ↦ iteratedFDeriv ℝ k (f p.1) p.2) := by
  have hz (p : Y × X) (hp : p ∉ C) : iteratedFDeriv ℝ k (f p.1) p.2 = 0 := by
    have heq : f p.1 =ᶠ[𝓝 p.2] (fun _ ↦ 0) := by
      filter_upwards [((continuous_const.prodMk continuous_id).continuousAt
        (x := p.2)).eventually (hC.isOpen_compl.mem_nhds hp)] with x hx
      exact hzero (p.1, x) hx
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply]
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ C
  · exact (hjet k p (hCS hp)).continuousAt (hS.mem_nhds (hCS hp))
  · apply (continuousAt_const (y := (0 : X [×k]→L[ℝ] V))).congr_of_eventuallyEq
    filter_upwards [hC.isOpen_compl.mem_nhds hp] with q hq
    exact hz q hq

/-- A closed common cutoff support globalizes the actual coordinate-amplitude jet family. -/
theorem continuous_iteratedFDeriv_coordinateAmplitude
    {Y : Type*} [TopologicalSpace Y] {n r s : ℕ}
    (e : Y → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ∀ t, ContDiffOn ℝ ∞ (e t) (e t).source)
    (hψ : ∀ t, ContDiffOn ℝ ∞ (e t).symm (e t).target)
    (hD : IsOpen {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ (e p.1).target})
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun p : Y × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ k (e p.1).symm p.2) {p | p.2 ∈ (e p.1).target})
    (W C : Set (Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
    (hW : IsOpen W) (hC : IsClosed C) (hCW : C ⊆ W)
    (hseg : ∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target)
    (hinv : ∀ p ∈ W, (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible)
    (χ : Y → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ)
    (hχ : ∀ t, ContDiffOn ℝ ∞ (χ t) {z | (t, z) ∈ W})
    (hχj : ∀ k : ℕ, ContinuousOn
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (χ p.1) p.2) W)
    (hχC : ∀ t z, χ t z ≠ 0 → (t, z) ∈ C)
    (p : SymbolFunction n r s) (hp : ContDiff ℝ ∞ (Function.uncurry p)) (k : ℕ) :
    Continuous
      (fun q : Y × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
          EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k
          (fun z ↦ coordinateAmplitude (e q.1) (χ q.1) p z.1.1 z.1.2 z.2) q.2) := by
  let X := EuclideanSpace ℝ (Fin n)
  let f (t : Y) (z : (X × X) × X) := coordinateAmplitude (e t) (χ t) p z.1.1 z.1.2 z.2
  let π (q : Y × ((X × X) × X)) : Y × (X × X) := (q.1, q.2.1)
  have hπ : Continuous π := continuous_fst.prodMk continuous_snd.fst
  apply continuous_jet_of_closed_support f (π ⁻¹' W) (π ⁻¹' C)
    (hW.preimage hπ) (hC.preimage hπ) (preimage_mono hCW) _ _ k
  · intro q hq
    have hzero : χ q.1 q.2.1 = 0 := by
      by_contra hn
      exact hq (hχC q.1 q.2.1 hn)
    simp only [f, coordinateAmplitude, Prod.eta, hzero, zero_mul, zero_smul]
  · exact continuousOn_iteratedFDeriv_coordinateAmplitude e he hψ hD hjets W hW
      hseg hinv χ hχ hχj p hp

end AtiyahSinger
