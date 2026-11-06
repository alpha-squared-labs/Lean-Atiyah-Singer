/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange

/-!
# Common neighborhoods for coordinate families

Public module ID: M0404.

Joint continuity of the original inverse coordinate derivative gives an open
parameter-and-endpoint neighborhood of the valid diagonal on which all segments
remain valid and their averaged derivatives are invertible. This is the common
localization needed before constructing finite parameter blocks for PDO averaging.
The parameter has only a topology; no smooth inverse group operation is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 20 in
set_option maxHeartbeats 600000 in

/-- A continuous derivative family has a common open valid change-of-frequency locus. -/
theorem exists_coordinateChange_family_neighborhood {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (e : Y → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ∀ t, ContDiffOn ℝ ∞ (e t) (e t).source)
    (hψ : ∀ t, ContDiffOn ℝ ∞ (e t).symm (e t).target)
    (hD : IsOpen {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ (e p.1).target})
    (hd : ContinuousOn
      (fun p : Y × EuclideanSpace ℝ (Fin n) ↦ fderiv ℝ (e p.1).symm p.2)
      {p | p.2 ∈ (e p.1).target}) :
    ∃ W : Set (Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧
      (∀ t x, x ∈ (e t).target → (t, (x, x)) ∈ W) ∧
      ∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target ∧
        (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible := by
  let X := EuclideanSpace ℝ (Fin n)
  let D : Set (Y × X) := {p | p.2 ∈ (e p.1).target}
  let S : Set (Y × (X × X)) := {p | segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target ∧
    (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible}
  refine ⟨interior S, isOpen_interior, ?_, fun p hp ↦ (show p ∈ S from interior_subset hp)⟩
  intro t x hx
  -- At this diagonal point, the original coordinate inverse law supplies invertibility.
  obtain ⟨W, _, hdiag, hvalid⟩ := exists_coordinateChange_neighborhood (e t) (he t) (hψ t)
    {x} isCompact_singleton (singleton_subset_iff.mpr hx)
  have hinv : (fderiv ℝ (e t).symm x).IsInvertible := by
    have h := (hvalid (x, x) (hdiag ⟨x, mem_singleton x, rfl⟩)).2
    rwa [averagedFDeriv_diag] at h
  have hopen : IsOpen {T : X →L[ℝ] X | T.IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  obtain ⟨ε, hε, hεinv⟩ := Metric.isOpen_iff.mp hopen (fderiv ℝ (e t).symm x) hinv
  have hnear : ∀ᶠ p : Y × X in 𝓝 (t, x), p ∈ D ∧
      dist (fderiv ℝ (e p.1).symm p.2) (fderiv ℝ (e t).symm x) < ε / 2 := by
    have hcont := (hd (t, x) hx).continuousAt (hD.mem_nhds hx)
    filter_upwards [hD.mem_nhds hx, hcont (Metric.ball_mem_nhds _ (half_pos hε))] with p hp hd
    exact ⟨hp, hd⟩
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  -- One product neighborhood controls the inverse derivatives along every small-ball segment.
  apply mem_interior_iff_mem_nhds.mpr
  have hsquare : U ×ˢ (Metric.ball x δ ×ˢ Metric.ball x δ) ∈ 𝓝 (t, (x, x)) :=
    by simpa only [nhds_prod_eq] using Filter.prod_mem_prod hU (Filter.prod_mem_prod
      (Metric.ball_mem_nhds x hδ) (Metric.ball_mem_nhds x hδ))
  filter_upwards [hsquare] with p hp
  have hsegment : segment ℝ p.2.2 p.2.1 ⊆ Metric.ball x δ :=
    (convex_ball x δ).segment_subset hp.2.2 hp.2.1
  have hcontrol (z : X) (hz : z ∈ Metric.ball x δ) :
      z ∈ (e p.1).target ∧
        dist (fderiv ℝ (e p.1).symm z) (fderiv ℝ (e t).symm x) < ε / 2 :=
    @hUV (p.1, z) ⟨hp.1, hδV hz⟩
  have hsegmentV : segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target :=
    hsegment.trans (fun z hz ↦ (hcontrol z hz).1)
  refine ⟨hsegmentV, ?_⟩
  let γ (s : ℝ) : X := s • p.2.1 + (1 - s) • p.2.2
  have hγ (s : ℝ) (hs : s ∈ Icc 0 1) : γ s ∈ Metric.ball x δ := by
    apply hsegment
    rw [segment_eq_image]
    exact ⟨s, hs, by simp only [γ, add_comm]⟩
  have hcontinuous : ContinuousOn (fun s ↦ fderiv ℝ (e p.1).symm (γ s)) (uIcc 0 1) := by
    apply ((hψ p.1).continuousOn_fderiv_of_isOpen (e p.1).open_target (by simp)).comp
      (show ContinuousOn γ (uIcc 0 1) from (by fun_prop : Continuous γ).continuousOn)
    intro s hs
    apply (hcontrol (γ s) (hγ s ?_)).1
    simpa only [uIcc_of_le zero_le_one] using hs
  -- The interval has length one, so the average stays in the same invertibility ball.
  have hbound : ‖averagedFDeriv (e p.1).symm p.2.1 p.2.2 -
      fderiv ℝ (e t).symm x‖ ≤ ε / 2 := by
    have heq : averagedFDeriv (e p.1).symm p.2.1 p.2.2 - fderiv ℝ (e t).symm x =
        ∫ s in (0 : ℝ)..1, fderiv ℝ (e p.1).symm (γ s) - fderiv ℝ (e t).symm x := by
      rw [intervalIntegral.integral_sub hcontinuous.intervalIntegrable
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp only [sub_zero, one_smul]
      rfl
    rw [heq]
    have hnorm (s : ℝ) (hs : s ∈ uIoc 0 1) :
        ‖fderiv ℝ (e p.1).symm (γ s) - fderiv ℝ (e t).symm x‖ ≤ ε / 2 := by
      have hs' : s ∈ Icc 0 1 := by
        simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hs
      simpa only [dist_eq_norm] using (hcontrol (γ s) (hγ s hs')).2.le
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  apply hεinv
  change dist (averagedFDeriv (e p.1).symm p.2.1 p.2.2) (fderiv ℝ (e t).symm x) < ε
  simpa only [dist_eq_norm] using hbound.trans_lt (half_lt_self hε)

end AtiyahSinger
