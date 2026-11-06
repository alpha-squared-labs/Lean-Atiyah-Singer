/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AveragedCoordinateDerivatives

import AtiyahSinger.Geometry.CompactParameterIntegral
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Frequency matrices for coordinate families

Public module ID: M0410.

Jointly continuous spatial jets of the inverse coordinate maps induce jointly
continuous spatial jets of the inverse-transpose frequency change on a common
valid segment and invertibility locus. The parameter needs only a topology.
Matrix inversion is used on its open invertible locus; this regularity bounds
the coordinate amplitudes on compact parameter blocks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set Topology
open scoped ContDiff Manifold

/-- Original coordinate frequency changes retain continuous spatial jets on their valid locus. -/
theorem continuousOn_iteratedFDeriv_coordinateFrequencyChange
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (e : Y → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
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
        iteratedFDeriv ℝ k (fun z ↦ coordinateFrequencyChange (e p.1) z.1 z.2) p.2) W := by
  let X := EuclideanSpace ℝ (Fin n)
  let A (t : Y) (z : X × X) : X →L[ℝ] X := averagedFDeriv (e t).symm z.1 z.2
  have hAvg (t : Y) : ContDiffOn ℝ ∞
      (fun z ↦ averagedFDeriv (e t).symm z.1 z.2) {z | (t, z) ∈ W} := by
    let Wt : Set (X × X) := {z | (t, z) ∈ W}
    have hWt : IsOpen Wt := hW.preimage (continuous_const.prodMk continuous_id)
    let X := EuclideanSpace ℝ (Fin n)
    let J := Set.Icc (0 : ℝ) 1
    let f : J × (X × X) → (X →L[ℝ] X) :=
      fun p ↦ fderiv ℝ (e t).symm ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2)
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
        f (Set.univ ×ˢ Wt) := by
      intro p hp
      have hmem : (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2 ∈ (e t).target := by
        apply hseg (t, p.2) hp.2
        rw [segment_eq_image]
        exact ⟨(p.1 : ℝ), p.1.property, by simp [add_comm]⟩
      have hd : ContDiffAt ℝ ∞ (fderiv ℝ (e t).symm)
          ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
        ((hψ t).contDiffAt ((e t).open_target.mem_nhds hmem)).fderiv_right (by simp)
      exact (hd.contMDiffAt.comp p (hc p)).contMDiffWithinAt
    have h := contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
      (volume : Measure J) hWt hf
    -- The subtype measure is ordinary Lebesgue measure restricted to [0,1]. Endpoints
    -- have zero measure, so this is exactly the original oriented interval integral.
    convert h using 1
    funext z
    dsimp only [f, J, averagedFDeriv]
    have he := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
      (fun s ↦ fderiv ℝ (e t).symm (s • z.1 + (1 - s) • z.2))
    rw [integral_Icc_eq_integral_Ioc] at he
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact he.symm
  have hAjets (j : ℕ) : ContinuousOn
      (fun p : Y × (X × X) ↦ iteratedFDeriv ℝ j (A p.1) p.2) W :=
    continuousOn_iteratedFDeriv_averagedFDeriv (fun t ↦ (e t).symm)
      {p | p.2 ∈ (e p.1).target} hD hψ hjets W hW hseg j
  have hA : ContinuousOn (fun p : Y × (X × X) ↦ A p.1 p.2) W := by
    have h := (continuousMultilinearCurryFin0 ℝ (X × X) (X →L[ℝ] X)).continuous
      |>.comp_continuousOn (hAjets 0)
    change ContinuousOn (fun p : Y × (X × X) ↦
      (iteratedFDeriv ℝ 0 (A p.1) p.2).curry0) W at h
    simpa only [Function.comp_def, ContinuousMultilinearMap.curry0_apply,
      iteratedFDeriv_zero_apply, id_eq] using h
  -- Adjoint is a real linear isometry, and inversion is smooth on invertible matrices.
  let Jadj : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ] (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro c B; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  let S : Set (X →L[ℝ] X) := {B | B.IsInvertible}
  have hS : IsOpen S := ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let F : (X →L[ℝ] X) → (X →L[ℝ] X) := fun B ↦ B.adjoint.inverse
  have hF : ContDiffOn ℝ ∞ F S := by
    intro B hB
    have hBadj : B.adjoint.IsInvertible := by
      apply ContinuousLinearMap.IsInvertible.of_inverse (g := B.inverse.adjoint)
      · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
          congrArg ContinuousLinearMap.adjoint hB.inverse_comp_self
      · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
          congrArg ContinuousLinearMap.adjoint hB.self_comp_inverse
    exact (hBadj.contDiffAt_map_inverse.comp B Jadj.contDiff.contDiffAt).contDiffWithinAt
  have hFjets (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ j F) S := by
    have h := hF.continuousOn_iteratedFDerivWithin (m := j) (by simp) hS.uniqueDiffOn
    apply h.congr
    intro B hB
    exact (iteratedFDerivWithin_of_isOpen _ hS hB).symm
  -- Apply the parameterized chain rule to the same averaged matrix, retaining every jet.
  exact continuousOn_iteratedFDeriv_comp_family (fun _ : Y ↦ F) A W
    (fun p hp ↦ hF.contDiffAt (hS.mem_nhds (hinv p hp)))
    (fun p hp ↦ (hAvg p.1).contDiffAt
      ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp))
    (fun j ↦ (hFjets j).comp hA hinv) hAjets k

end AtiyahSinger
