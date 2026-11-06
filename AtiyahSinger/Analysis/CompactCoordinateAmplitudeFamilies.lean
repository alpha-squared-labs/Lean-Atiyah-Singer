/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSymbolCoordinateFamilies
public import AtiyahSinger.Analysis.LinearFrequencyJetFamilies
public import AtiyahSinger.Analysis.MixedJetFamilies

import all AtiyahSinger.Analysis.CoordinateJacobianFamilies
import all AtiyahSinger.Analysis.MixedJetFamilies

/-!
# Compactly supported families of coordinate amplitudes

Public module ID: M0349.

One compact subset of the original parameter-and-space locus controls the
actual coordinate substitutions and linear matrix coefficients. The full
spatial jets first produce continuous amplitude jets. Uniform symbol estimates
then control the original three mixed derivatives, without introducing a
continuous selection of reduced symbols.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 25 in
set_option maxHeartbeats 1200000 in

/-- Compact moving coordinate data give a continuous, uniformly bounded amplitude family. -/
theorem uniform_amplitude_family_of_compact_coordinate_data
    {T : Type*} [TopologicalSpace T] [T2Space T] {n r q : ℕ}
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol univ m p)
    (W C : Set (T × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
    (hW : IsOpen W) (hC : IsCompact C) (hCW : C ⊆ W)
    (φ : T → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n))
    (Θ : T → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : T → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ]
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hdata : ∀ t, ContDiffOn ℝ ∞ (fun z ↦ (φ t z, Θ t z)) {z | (t, z) ∈ W})
    (hdataj : ∀ k : ℕ, ContinuousOn (fun a ↦ iteratedFDeriv ℝ k
      (fun z ↦ (φ a.1 z, Θ a.1 z)) a.2) W)
    (hinv : ∀ a ∈ W, (Θ a.1 a.2).IsInvertible)
    (hL : ∀ t, ContDiffOn ℝ ∞ (L t) {z | (t, z) ∈ W})
    (hLj : ∀ k : ℕ, ContinuousOn (fun a ↦ iteratedFDeriv ℝ k (L a.1) a.2) W)
    (hzero : ∀ a ∉ C, L a.1 a.2 = 0) :
    let a : T → AmplitudeFunction n r q :=
      fun t x y ξ ↦ L t (x, y) (p (φ t (x, y)) (Θ t (x, y) ξ))
    (∀ t, IsAmplitude m (a t)) ∧
    (∀ t, tsupport (Function.uncurry (a t)) ⊆ Prod.snd '' C) ∧
    (∀ k : ℕ, Continuous (fun b : T × ((EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (fun z ↦ a b.1 z.1.1 z.1.2 z.2) b.2)) ∧
    (∀ i j k : ℕ, Continuous (fun b : T × ((EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) ↦
        amplitudeDerivative (a b.1) i j k b.2.1.1 b.2.1.2 b.2.2)) ∧
    (∀ i j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t x y ξ,
      ‖amplitudeDerivative (a t) i j k x y ξ‖ ≤
        D * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Z := X × X
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let a : T → AmplitudeFunction n r q :=
    fun t x y ξ ↦ L t (x, y) (p (φ t (x, y)) (Θ t (x, y) ξ))
  let O (t : T) : Set Z := {z | (t, z) ∈ W}
  have hO (t : T) : IsOpen (O t) := hW.preimage (continuous_const.prodMk continuous_id)
  have hp' : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using hp.1
  have hds (b : T × Z) (hb : b ∈ W) :
      ContDiffAt ℝ ∞ (fun z ↦ (φ b.1 z, Θ b.1 z)) b.2 :=
    (hdata b.1).contDiffAt ((hO b.1).mem_nhds hb)
  have hLs (b : T × Z) (hb : b ∈ W) : ContDiffAt ℝ ∞ (L b.1) b.2 :=
    (hL b.1).contDiffAt ((hO b.1).mem_nhds hb)
  have hclosed : IsClosed C := hC.isClosed
  -- Assemble the original spatial factors before adjoining the passive frequency variable.
  let D := (X × (X →L[ℝ] X)) × (H →L[ℝ] H)
  let d (t : T) (z : Z) : D := ((φ t z, Θ t z), L t z)
  have hds' (b : T × Z) (hb : b ∈ W) : ContDiffAt ℝ ∞ (d b.1) b.2 :=
    (hds b hb).prodMk (hLs b hb)
  have hdj : ∀ k : ℕ, ContinuousOn
      (fun b : T × Z ↦ iteratedFDeriv ℝ k (d b.1) b.2) W :=
    continuousOn_jet_pair_family (fun t z ↦ (φ t z, Θ t z)) L W
      hds hLs hdataj hLj
  let S : Set (T × (Z × X)) := {b | (b.1, b.2.1) ∈ W}
  let C' : Set (T × (Z × X)) := {b | (b.1, b.2.1) ∈ C}
  have hS : IsOpen S := hW.preimage (continuous_fst.prodMk continuous_snd.fst)
  have hC' : IsClosed C' := hclosed.preimage (continuous_fst.prodMk continuous_snd.fst)
  let f (t : T) (z : Z × X) : D × X := (d t z.1, z.2)
  have hfs (b : T × (Z × X)) (hb : b ∈ S) : ContDiffAt ℝ ∞ (f b.1) b.2 :=
    ((hds' (b.1, b.2.1) hb).comp b.2 contDiffAt_fst).prodMk contDiffAt_snd
  have hleftj (k : ℕ) : ContinuousOn
      (fun b : T × (Z × X) ↦ iteratedFDeriv ℝ k (fun z ↦ d b.1 z.1) b.2) S :=
    continuousOn_iteratedFDeriv_comp_family d (fun _ : T ↦ Prod.fst) S
      (fun b hb ↦ hds' (b.1, b.2.1) hb) (fun _ _ ↦ contDiffAt_fst)
      (fun j ↦ (hdj j).comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
        (fun _ hb ↦ hb))
      (fun j ↦ ((contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Z × X → Z)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn) k
  have hfj : ∀ k : ℕ, ContinuousOn
      (fun b : T × (Z × X) ↦ iteratedFDeriv ℝ k (f b.1) b.2) S :=
    continuousOn_jet_pair_family (fun t z ↦ d t z.1) (fun _ : T ↦ Prod.snd) S
      (fun b hb ↦ (hds' (b.1, b.2.1) hb).comp b.2 contDiffAt_fst)
      (fun _ _ ↦ contDiffAt_snd) hleftj
      (fun j ↦ ((contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Z × X → X)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn)
  let F (z : D × X) : H := z.1.2 (p z.1.1.1 (z.1.1.2 z.2))
  have hF : ContDiff ℝ ∞ F := contDiff_fst.snd.clm_apply
    (hp'.comp (contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.clm_apply contDiff_snd)))
  have hlocalj : ∀ k : ℕ, ContinuousOn
      (fun b : T × (Z × X) ↦ iteratedFDeriv ℝ k
        (fun z ↦ a b.1 z.1.1 z.1.2 z.2) b.2) S :=
    continuousOn_jet_postcomp_family f F S univ isOpen_univ
      (fun _ _ ↦ mem_univ _) hfs hF.contDiffOn hfj
  have hz (b : T × (Z × X)) (hb : b ∉ C') : a b.1 b.2.1.1 b.2.1.2 b.2.2 = 0 := by
    change L b.1 b.2.1 _ = 0
    rw [hzero (b.1, b.2.1) hb, zero_apply]
  -- Outside the same closed support all spatial germs vanish, including every derivative.
  have haj : ∀ k : ℕ, Continuous (fun b : T × (Z × X) ↦ iteratedFDeriv ℝ k
      (fun z ↦ a b.1 z.1.1 z.1.2 z.2) b.2) :=
    continuous_jet_of_closed_support (fun t z ↦ a t z.1.1 z.1.2 z.2) S C' hS hC'
      (fun _ hb ↦ hCW hb) hz hlocalj
  have has (t : T) : ContDiff ℝ ∞ (fun z : Z × X ↦ a t z.1.1 z.1.2 z.2) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzC : (t, z.1) ∈ C
    · exact hF.contDiffAt.comp z (hfs (t, z) (hCW hzC))
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      filter_upwards [((continuous_const.prodMk continuous_fst).continuousAt (x := z)).eventually
          (hclosed.isOpen_compl.mem_nhds hzC)] with w hw
      exact hz (t, w) hw
  have ham := continuous_amplitudeDerivative_of_continuous_jets a has haj
  have hdcont : ContinuousOn (fun b : T × Z ↦ (φ b.1 b.2, Θ b.1 b.2)) W := by
    have h := (continuousMultilinearCurryFin0 ℝ Z (X × (X →L[ℝ] X))).continuous
      |>.comp_continuousOn (hdataj 0)
    change ContinuousOn (fun b : T × Z ↦
      (iteratedFDeriv ℝ 0 (fun z ↦ (φ b.1 z, Θ b.1 z)) b.2).curry0) W at h
    simpa only [ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply] using h
  have hgb := continuousOn_iteratedFDeriv_linear_frequency_family
    (fun t z ↦ (φ t z, Θ t z)) W hW hdata hdataj
  have hbound (i k : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t z ξ,
      ‖iteratedFDeriv ℝ i (fun w : Z ↦ iteratedFDeriv ℝ k
        (fun η ↦ a t w.1 w.2 η) ξ) z‖ ≤ D * (1 + ‖ξ‖) ^ (m - (k : ℝ)) := by
    obtain ⟨D, hD, hDb⟩ := exists_bound_symbol_comp_of_isCompact_parameter
      univ isOpen_univ m p hp W C hW hC hCW φ Θ L (fun t ↦ (hdata t).fst)
        (fun t ↦ (hdata t).snd) hL hdcont.fst hdcont.snd
        (fun _ _ ↦ mem_univ _) hinv hgb hLj i k
    refine ⟨D, hD, ?_⟩
    intro t z ξ
    by_cases hzC : (t, z) ∈ C
    · exact hDb t z hzC ξ
    · have heq : (fun w : Z ↦ iteratedFDeriv ℝ k (fun η ↦ a t w.1 w.2 η) ξ)
          =ᶠ[𝓝 z] (fun _ ↦ 0) := by
        filter_upwards [((continuous_const.prodMk continuous_id).continuousAt (x := z)).eventually
          (hclosed.isOpen_compl.mem_nhds hzC)] with w hw
        have hz' : (fun η ↦ a t w.1 w.2 η) = fun _ ↦ (0 : H) := by
          funext η
          exact hz (t, (w, η)) hw
        rw [hz', iteratedFDeriv_fun_zero, Pi.zero_apply]
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply,
        norm_zero]
      exact mul_nonneg hD (by positivity)
  have habound (i j k : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t x y ξ,
      ‖amplitudeDerivative (a t) i j k x y ξ‖ ≤
        D * (1 + ‖ξ‖) ^ (m - (k : ℝ)) := by
    obtain ⟨D, hD, hDb⟩ := hbound (i + j) k
    refine ⟨D, hD, ?_⟩
    intro t x y ξ
    have hs := (partial_jet_family (fun t (z : Z × X) ↦ a t z.1.1 z.1.2 z.2) has haj k).1 t
    have hspatial : ContDiff ℝ ∞ (fun z : Z ↦ iteratedFDeriv ℝ k
        (a t z.1 z.2) ξ) := hs.comp (contDiff_id.prodMk contDiff_const)
    exact (norm_mixed_iteratedFDeriv_le
      (fun x y ↦ iteratedFDeriv ℝ k (a t x y) ξ) hspatial i j x y).trans (hDb t (x, y) ξ)
  refine ⟨?_, ?_, haj, ham, habound⟩
  · intro t
    refine ⟨has t, ?_⟩
    intro K hK i j k
    obtain ⟨D, hD, hDb⟩ := habound i j k
    exact ⟨D, hD, fun x y _ ξ ↦ hDb t x y ξ⟩
  · intro t
    apply closure_minimal ?_ (hC.image continuous_snd).isClosed
    intro z hz'
    by_contra hout
    have htC : (t, z) ∉ C := fun h ↦ hout ⟨(t, z), h, rfl⟩
    apply hz'
    funext ξ
    exact hz (t, (z, ξ)) htC

end AtiyahSinger
