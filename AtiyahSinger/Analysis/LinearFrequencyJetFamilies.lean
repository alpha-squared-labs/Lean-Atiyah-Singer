/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Jets of parameterized linear frequency substitutions

Public module ID: M0780.

A continuous spatial jet family of base points and frequency matrices gives a
continuous jet family of the actual normalized substitution on space times
frequency. The additional frequency variable is passive until the fixed smooth
matrix evaluation is applied. The parameter has only a topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff

/-- Spatial jets of coordinate data control the full normalized frequency substitution family. -/
theorem continuousOn_iteratedFDeriv_linear_frequency_family
    {T Z X : Type*} [TopologicalSpace T]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (d : T → Z → X × (X →L[ℝ] X)) (W : Set (T × Z)) (hW : IsOpen W)
    (hd : ∀ t, ContDiffOn ℝ ∞ (d t) {z | (t, z) ∈ W})
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun p : T × Z ↦ iteratedFDeriv ℝ k (d p.1) p.2) W) (k : ℕ) :
    ContinuousOn
      (fun p : (T × Z) × X ↦ iteratedFDeriv ℝ k
        (fun z : Z × X ↦ ((d p.1.1 z.1).1, (d p.1.1 z.1).2 z.2)) (p.1.2, p.2))
      (W ×ˢ univ) := by
  let F := X × (X →L[ℝ] X)
  let S : Set (T × (Z × X)) := {p | (p.1, p.2.1) ∈ W}
  have hds (p : T × Z) (hp : p ∈ W) : ContDiffAt ℝ ∞ (d p.1) p.2 :=
    (hd p.1).contDiffAt ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp)
  have hleftj (j : ℕ) : ContinuousOn
      (fun p : T × (Z × X) ↦ iteratedFDeriv ℝ j (fun z ↦ d p.1 z.1) p.2) S :=
    continuousOn_iteratedFDeriv_comp_family d (fun _ : T ↦ Prod.fst) S
      (fun p hp ↦ hds (p.1, p.2.1) hp) (fun _ _ ↦ contDiffAt_fst)
      (fun l ↦ (hjets l).comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
        (fun _ hp ↦ hp))
      (fun l ↦ ((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Z × X → Z)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn) j
  let g (t : T) (z : Z × X) : F × X := (d t z.1, z.2)
  have hg (p : T × (Z × X)) (hp : p ∈ S) : ContDiffAt ℝ ∞ (g p.1) p.2 :=
    ((hds (p.1, p.2.1) hp).comp p.2 contDiffAt_fst).prodMk contDiffAt_snd
  have hgj (j : ℕ) : ContinuousOn
      (fun p : T × (Z × X) ↦ iteratedFDeriv ℝ j (g p.1) p.2) S := by
    have hright : ContinuousOn
        (fun p : T × (Z × X) ↦ iteratedFDeriv ℝ j (Prod.snd : Z × X → X) p.2) S :=
      ((contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Z × X → X)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn
    have h := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin j ↦ Z × X) F X).continuous
      |>.comp_continuousOn ((hleftj j).prodMk hright)
    apply h.congr
    intro p hp
    exact iteratedFDeriv_prodMk ((hds (p.1, p.2.1) hp).comp p.2 contDiffAt_fst)
      (contDiffAt_snd : ContDiffAt ℝ ∞ (Prod.snd : Z × X → X) p.2) (by simp)
  have hgcont : ContinuousOn (fun p : T × (Z × X) ↦ g p.1 p.2) S := by
    have h := (continuousMultilinearCurryFin0 ℝ (Z × X) (F × X)).continuous
      |>.comp_continuousOn (hgj 0)
    change ContinuousOn (fun p : T × (Z × X) ↦ (iteratedFDeriv ℝ 0 (g p.1) p.2).curry0) S at h
    simpa only [ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply] using h
  let H (p : F × X) : X × X := (p.1.1, p.1.2 p.2)
  have hH : ContDiff ℝ ∞ H :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.clm_apply contDiff_snd)
  have hcomp := continuousOn_iteratedFDeriv_comp_family (fun _ : T ↦ H) g S
    (fun _ _ ↦ hH.contDiffAt) hg
    (fun j ↦ (hH.continuous_iteratedFDeriv (by simp)).comp_continuousOn hgcont) hgj k
  exact hcomp.comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)).continuousOn
    (fun _ hp ↦ hp.1)

end AtiyahSinger
