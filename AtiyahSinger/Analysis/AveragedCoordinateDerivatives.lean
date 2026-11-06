/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactJetIntegral
public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.SmoothCompositionFamilies

import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Spatial derivatives of averaged coordinate families

Public module ID: M0316.

The averaged derivative along a segment retains joint continuity of all spatial
jets for an arbitrary topological parameter. Only the two endpoints are
differentiated. Integration is over the fixed unit interval, and the whole
segment must remain in the original open coordinate domain. This supplies
parameter control for the actual frequency change in equivariant PDO averaging
without a differentiable inverse map on the parameter group.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff Manifold

private theorem continuousOn_integrated_spatial_jets
    {T Y H F : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] [TopologicalSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure T) [IsFiniteMeasure μ] (f : T → Y → H → F)
    (W : Set (Y × H)) (hW : IsOpen W)
    (hf : ∀ t y, ContDiffOn ℝ ∞ (f t y) {x | (y, x) ∈ W})
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun p : T × (Y × H) ↦ iteratedFDeriv ℝ k (f p.1 p.2.1) p.2.2)
      (univ ×ˢ W)) (k : ℕ) :
    ContinuousOn
      (fun p : Y × H ↦ iteratedFDeriv ℝ k (fun x ↦ ∫ t, f t p.1 x ∂μ) p.2) W := by
  have hcont : ContinuousOn
      (fun p : Y × H ↦ ∫ t, iteratedFDeriv ℝ k (f t p.1) p.2 ∂μ) W := by
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    · exact (hjets k).comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)
    · intro p t hp ht
      exact (ht (mem_univ t)).elim
  apply hcont.congr
  intro p hp
  apply iteratedFDeriv_integral_of_continuous_jets μ
    (hW.preimage (continuous_const.prodMk continuous_id)) (fun t ↦ hf t p.1) _ k hp
  intro j
  exact (hjets j).comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
    (fun q hq ↦ ⟨hq.1, hq.2⟩)

/-- Averaging coordinate derivatives along valid segments preserves continuous spatial jets. -/
theorem continuousOn_iteratedFDeriv_averagedFDeriv
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (ψ : Y → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (D : Set (Y × EuclideanSpace ℝ (Fin n))) (hD : IsOpen D)
    (hψ : ∀ y, ContDiffOn ℝ ∞ (ψ y) {x | (y, x) ∈ D})
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun p : Y × EuclideanSpace ℝ (Fin n) ↦ iteratedFDeriv ℝ k (ψ p.1) p.2) D)
    (W : Set (Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
    (hW : IsOpen W)
    (hseg : ∀ p ∈ W, ∀ x ∈ segment ℝ p.2.2 p.2.1, (p.1, x) ∈ D) (k : ℕ) :
    ContinuousOn
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (fun z ↦ averagedFDeriv (ψ p.1) z.1 z.2) p.2) W := by
  let X := EuclideanSpace ℝ (Fin n)
  let J := Set.Icc (0 : ℝ) 1
  let γ (t : J) (z : X × X) : X := (t : ℝ) • z.1 + (1 - (t : ℝ)) • z.2
  have hγmem (t : J) (z : X × X) : γ t z ∈ segment ℝ z.2 z.1 := by
    rw [segment_eq_image]
    exact ⟨(t : ℝ), t.property, by simp only [γ, add_comm]⟩
  have hγsmooth (t : J) : ContDiff ℝ ∞ (γ t) := by
    change ContDiff ℝ ∞ (fun z : X × X ↦ (t : ℝ) • z.1 + (1 - (t : ℝ)) • z.2)
    fun_prop
  -- The affine segment family is smooth in its interval parameter and both endpoints.
  have ht : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ) ∞
      (fun p : J × (X × X) ↦ (p.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hγjoint : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X) ∞
      (fun p : J × (X × X) ↦ γ p.1 p.2) :=
    (ht.smul (contDiff_fst.contMDiff.comp contMDiff_snd)).add
      (((contDiff_const.sub contDiff_id).contMDiff.comp ht).smul
        (contDiff_snd.contMDiff.comp contMDiff_snd))
  have hγjets (j : ℕ) : Continuous
      (fun p : J × (X × X) ↦ iteratedFDeriv ℝ j (γ p.1) p.2) := by
    exact continuousOn_univ.mp ((contMDiffOn_iteratedFDeriv_parameter
      (𝓡∂ 1) isOpen_univ hγjoint.contMDiffOn j).continuousOn)
  -- Currying the next original jet gives the jets of the original first derivative.
  have hdjets (j : ℕ) : ContinuousOn
      (fun p : Y × X ↦ iteratedFDeriv ℝ j (fderiv ℝ (ψ p.1)) p.2) D := by
    let C := continuousMultilinearCurryRightEquiv' ℝ j X X
    have h := C.continuous.comp_continuousOn (hjets (j + 1))
    apply h.congr
    intro p _
    change iteratedFDeriv ℝ j (fderiv ℝ (ψ p.1)) p.2 =
      C (iteratedFDeriv ℝ (j + 1) (ψ p.1) p.2)
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact (C.apply_symm_apply _).symm
  have hdAt (y : Y) (x : X) (hx : (y, x) ∈ D) :
      ContDiffAt ℝ ∞ (fderiv ℝ (ψ y)) x :=
    ((hψ y).contDiffAt ((hD.preimage
      (continuous_const.prodMk continuous_id)).mem_nhds hx)).fderiv_right (by simp)
  let f (t : J) (y : Y) (z : X × X) : X →L[ℝ] X := fderiv ℝ (ψ y) (γ t z)
  have hf (t : J) (y : Y) : ContDiffOn ℝ ∞ (f t y) {z | (y, z) ∈ W} := by
    intro z hz
    exact ((hdAt y (γ t z) (hseg (y, z) hz _ (hγmem t z))).comp z
      (hγsmooth t).contDiffAt).contDiffWithinAt
  have hfj (j : ℕ) : ContinuousOn
      (fun p : J × (Y × (X × X)) ↦ iteratedFDeriv ℝ j (f p.1 p.2.1) p.2.2)
      (univ ×ˢ W) := by
    let S : Set ((J × Y) × (X × X)) := {p | (p.1.2, p.2) ∈ W}
    have hcomp := continuousOn_iteratedFDeriv_comp_family
      (fun p : J × Y ↦ fderiv ℝ (ψ p.2)) (fun p : J × Y ↦ γ p.1) S
      (fun p hp ↦ hdAt p.1.2 (γ p.1.1 p.2)
        (hseg (p.1.2, p.2) hp _ (hγmem p.1.1 p.2)))
      (fun p _ ↦ (hγsmooth p.1.1).contDiffAt)
      (fun l ↦ (hdjets l).comp
        (show Continuous (fun p : (J × Y) × (X × X) ↦
          (p.1.2, γ p.1.1 p.2)) from
            continuous_fst.snd.prodMk (hγjoint.continuous.comp
              (continuous_fst.fst.prodMk continuous_snd))).continuousOn
        (fun p hp ↦ hseg (p.1.2, p.2) hp _ (hγmem p.1.1 p.2)))
      (fun l ↦ (hγjets l).comp
        (continuous_fst.fst.prodMk continuous_snd) |>.continuousOn) j
    exact hcomp.comp
      ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd).continuousOn
      (fun _ hp ↦ hp.2)
  -- Integrate exactly these spatial jets; the parameter Y is never differentiated.
  have h := continuousOn_integrated_spatial_jets (volume : Measure J) f W hW hf hfj k
  have havg (y : Y) : (fun z ↦ ∫ t : J, f t y z) =
      (fun z : X × X ↦ averagedFDeriv (ψ y) z.1 z.2) := by
    funext z
    have he := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
      (fun t ↦ fderiv ℝ (ψ y) (t • z.1 + (1 - t) • z.2))
    rw [integral_Icc_eq_integral_Ioc] at he
    rw [averagedFDeriv, intervalIntegral.integral_of_le zero_le_one]
    exact he
  simpa only [havg] using h

end AtiyahSinger
