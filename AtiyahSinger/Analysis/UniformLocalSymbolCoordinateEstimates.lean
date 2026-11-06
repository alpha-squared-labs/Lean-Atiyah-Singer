/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.UniformSymbolCoordinateEstimates

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Uniform symbol estimates in moving open coordinate domains

Public module ID: M1043.

Uniform derivative bounds are local statements. A family of coordinate maps may
be smooth only on parameter-dependent open domains, and the set of evaluation
points may move with that parameter. A local plateau and translation to the
origin reduce every germ to the existing global quantitative chain rule. The
extensions need not depend continuously on the parameter: their jets at the
specified original points agree exactly with the original jets.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set Topology
open scoped ContDiff

private theorem exists_contDiff_extension_germ
    {Z F : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Z → F) (W : Set Z) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (z : Z) (hz : z ∈ W) :
    ∃ q : Z → F, ContDiff ℝ ∞ q ∧ q =ᶠ[𝓝 z] f := by
  -- A compact plateau retains the complete original germ at this one point.
  obtain ⟨U, hU, hzU, hUW, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := z)) hW (singleton_subset_iff.mpr hz)
  obtain ⟨V, hV, hUV, hVW, _⟩ :=
    exists_open_between_and_isCompact_closure hUc hW hUW
  obtain ⟨β, hβ, _, hsβ, hβone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  have hβW : tsupport β ⊆ W := by
    simpa only [tsupport, hsβ] using hVW
  have hone : ∀ x ∈ U, β x = 1 := fun x hx ↦ (hβone x).mp (subset_closure hx)
  let q (x : Z) : F := β x • f x
  have hq : ContDiff ℝ ∞ q := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport β
    · exact hβ.contDiffAt.smul (hf.contDiffAt (hW.mem_nhds (hβW hx)))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hx] with y hy
      simp only [q, image_eq_zero_of_notMem_tsupport hy, zero_smul]
  refine ⟨q, hq, ?_⟩
  filter_upwards [hU.mem_nhds (hzU (mem_singleton z))] with x hx
  simp only [q, hone x hx, one_smul]

/-- Uniform local normalized jets preserve symbol order on parameter-dependent point sets. -/
theorem exists_uniform_bound_symbol_comp_linear_frequency_of_contDiffOn
    {T : Type*} {Z X V : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : X → X → V) (hp : ContDiff ℝ ∞ (Function.uncurry p))
    (φ : T → Z → X) (Θ : T → Z → X →L[ℝ] X)
    (W K : T → Set Z) (hW : ∀ t, IsOpen (W t)) (hKW : ∀ t, K t ⊆ W t)
    (hφ : ∀ t, ContDiffOn ℝ ∞ (φ t) (W t))
    (hΘ : ∀ t, ContDiffOn ℝ ∞ (Θ t) (W t)) (m : ℝ)
    (hgbound : ∀ a : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t,
      ∀ w ∈ K t ×ˢ Metric.closedBall (0 : X) 1,
        ‖iteratedFDeriv ℝ a (fun z : Z × X ↦ (φ t z.1, Θ t z.1 z.2)) w‖ ≤ D)
    (hpbound : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t z, z ∈ K t → ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (p x) ξ) (φ t z)‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (j : ℝ)))
    (B : ℝ) (hB : 1 ≤ B)
    (hupper : ∀ t z, z ∈ K t → ∀ ξ, ‖Θ t z ξ‖ ≤ B * ‖ξ‖)
    (hlower : ∀ t z, z ∈ K t → ∀ ξ, ‖ξ‖ ≤ B * ‖Θ t z ξ‖) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t z, z ∈ K t → ∀ ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ t w) (Θ t w η)) ξ) z‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  classical
  let S := {v : T × Z // v.2 ∈ K v.1}
  have hext (v : S) : ∃ q : Z → X × (X →L[ℝ] X), ContDiff ℝ ∞ q ∧
      q =ᶠ[𝓝 v.val.2] (fun x ↦ (φ v.val.1 x, Θ v.val.1 x)) :=
    exists_contDiff_extension_germ _ (W v.val.1) (hW v.val.1)
      ((hφ v.val.1).prodMk (hΘ v.val.1)) v.val.2 (hKW v.val.1 v.property)
  choose q hq hqeq using hext
  let φ' (v : S) (x : Z) : X := (q v (x + v.val.2)).1
  let Θ' (v : S) (x : Z) : X →L[ℝ] X := (q v (x + v.val.2)).2
  have hφ' (v : S) : ContDiff ℝ ∞ (φ' v) :=
    (hq v).fst.comp (contDiff_id.add contDiff_const)
  have hΘ' (v : S) : ContDiff ℝ ∞ (Θ' v) :=
    (hq v).snd.comp (contDiff_id.add contDiff_const)
  have heq (v : S) : ∀ᶠ x : Z in 𝓝 0,
      φ' v x = φ v.val.1 (x + v.val.2) ∧ Θ' v x = Θ v.val.1 (x + v.val.2) := by
    have h := (hqeq v).comp_tendsto
      (show Tendsto (fun x : Z ↦ x + v.val.2) (𝓝 0) (𝓝 v.val.2) from by
        have hc : Continuous (fun x : Z ↦ x + v.val.2) :=
          continuous_id.add continuous_const
        simpa only [ContinuousAt, zero_add] using hc.continuousAt (x := (0 : Z)))
    filter_upwards [h] with x hx
    exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  have heq0 (v : S) : φ' v 0 = φ v.val.1 v.val.2 ∧ Θ' v 0 = Θ v.val.1 v.val.2 := by
    simpa only [zero_add] using (heq v).self_of_nhds
  let g (t : T) (w : Z × X) : X × X := (φ t w.1, Θ t w.1 w.2)
  have hjeteq (v : S) (η : X) (a : ℕ) :
      iteratedFDeriv ℝ a (fun w : Z × X ↦ (φ' v w.1, Θ' v w.1 w.2)) (0, η) =
        iteratedFDeriv ℝ a (g v.val.1) (v.val.2, η) := by
    have hevent : (fun w : Z × X ↦ (φ' v w.1, Θ' v w.1 w.2)) =ᶠ[𝓝 (0, η)]
        (fun w ↦ g v.val.1 (w + (v.val.2, 0))) := by
      filter_upwards [continuous_fst.continuousAt.eventually (heq v)] with w hw
      simp only [g, Prod.add_def, add_zero, hw.1, hw.2]
    rw [(hevent.iteratedFDeriv ℝ a).eq_of_nhds, iteratedFDeriv_comp_add_right]
    simp only [Prod.add_def, zero_add, add_zero]
  -- One fixed singleton now indexes the same original germs at all moving points.
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_symbol_comp_linear_frequency p hp
    φ' hφ' Θ' hΘ' m {0}
    (fun a ↦ by
      obtain ⟨D, hD, hDb⟩ := hgbound a
      refine ⟨D, hD, ?_⟩
      intro v w hw
      have hw0 : w.1 = 0 := mem_singleton_iff.mp hw.1
      rw [show w = (0, w.2) by ext <;> simp [hw0], hjeteq]
      exact hDb v.val.1 (v.val.2, w.2) ⟨v.property, hw.2⟩)
    (fun a b ↦ by
      obtain ⟨D, hD, hDb⟩ := hpbound a b
      refine ⟨D, hD, ?_⟩
      intro v z hz ξ
      have hz0 : z = 0 := mem_singleton_iff.mp hz
      rw [hz0, (heq0 v).1]
      exact hDb v.val.1 v.val.2 v.property ξ)
    B hB
    (fun v z hz ξ ↦ by
      have hz0 : z = 0 := mem_singleton_iff.mp hz
      rw [hz0, (heq0 v).2]
      exact hupper v.val.1 v.val.2 v.property ξ)
    (fun v z hz ξ ↦ by
      have hz0 : z = 0 := mem_singleton_iff.mp hz
      rw [hz0, (heq0 v).2]
      exact hlower v.val.1 v.val.2 v.property ξ) i j
  refine ⟨C, hC, ?_⟩
  intro t z hz ξ
  let v : S := ⟨(t, z), hz⟩
  have hevent : (fun x ↦ iteratedFDeriv ℝ j
      (fun η ↦ p (φ' v x) (Θ' v x η)) ξ) =ᶠ[𝓝 0]
      (fun x ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ t (x + z)) (Θ t (x + z) η)) ξ) := by
    filter_upwards [heq v] with x hx
    simp only [hx.1, hx.2]
    rfl
  have h := hbound v 0 (mem_singleton 0) ξ
  rw [(hevent.iteratedFDeriv ℝ i).eq_of_nhds] at h
  have htrans := iteratedFDeriv_comp_add_right i z (0 : Z)
    (f := fun x ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ t x) (Θ t x η)) ξ) (𝕜 := ℝ)
  rw [htrans] at h
  simpa only [zero_add] using h

end AtiyahSinger
