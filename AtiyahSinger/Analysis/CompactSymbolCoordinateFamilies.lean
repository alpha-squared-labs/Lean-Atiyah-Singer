/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolQuotient
public import AtiyahSinger.Analysis.UniformAmplitudeCoordinateEstimates

/-!
# Compact families of original symbol coordinate changes

Public module ID: M0361.

A compact set in the actual parameter-and-space domain gives uniform symbol
estimates from continuous normalized coordinate jets and coefficient jets.
The spatial domain and compact slice may vary with the parameter. A single
source plateau extends the original local symbol while retaining its full
frequency family and every mixed germ on the compact image. No continuity in
a symbol topology, compactness of all parameter space, or support of the
coefficient is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff Manifold

/-- Compact moving coordinate data preserve the original real symbol order uniformly. -/
theorem exists_bound_symbol_comp_of_isCompact_parameter
    {T : Type*} [TopologicalSpace T]
    {Z H : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {n r q : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol U m p)
    (W C : Set (T × Z)) (hW : IsOpen W) (hC : IsCompact C) (hCW : C ⊆ W)
    (φ : T → Z → EuclideanSpace ℝ (Fin n))
    (Θ : T → Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : T → Z → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ] H)
    (hφ : ∀ t, ContDiffOn ℝ ∞ (φ t) {z | (t, z) ∈ W})
    (hΘ : ∀ t, ContDiffOn ℝ ∞ (Θ t) {z | (t, z) ∈ W})
    (hL : ∀ t, ContDiffOn ℝ ∞ (L t) {z | (t, z) ∈ W})
    (hφcont : ContinuousOn (fun z : T × Z ↦ φ z.1 z.2) W)
    (hΘcont : ContinuousOn (fun z : T × Z ↦ Θ z.1 z.2) W)
    (hφU : ∀ z ∈ W, φ z.1 z.2 ∈ U)
    (hinv : ∀ z ∈ W, (Θ z.1 z.2).IsInvertible)
    (hgjets : ∀ a : ℕ, ContinuousOn
      (fun y : (T × Z) × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ a
          (fun z : Z × EuclideanSpace ℝ (Fin n) ↦ (φ y.1.1 z.1, Θ y.1.1 z.1 z.2))
          (y.1.2, y.2)) (W ×ˢ univ))
    (hLjets : ∀ a : ℕ, ContinuousOn
      (fun z : T × Z ↦ iteratedFDeriv ℝ a (L z.1) z.2) W) (i j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t z, (t, z) ∈ C → ∀ ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ L t w (p (φ t w) (Θ t w η))) ξ) z‖ ≤
          D * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let K (t : T) : Set Z := {z | (t, z) ∈ C}
  let O (t : T) : Set Z := {z | (t, z) ∈ W}
  have hO (t : T) : IsOpen (O t) := hW.preimage (continuous_const.prodMk continuous_id)
  let S : Set X := (fun z : T × Z ↦ φ z.1 z.2) '' C
  have hS : IsCompact S := hC.image_of_continuousOn (hφcont.mono hCW)
  have hSU : S ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφU z (hCW hz)
  -- One fixed source plateau preserves the whole frequency family on the compact image.
  obtain ⟨β, hβzero, hβone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, X) hU.isClosed_compl hS.isClosed
      (disjoint_compl_left_iff_subset.mpr hSU)
  have hβ : ContDiff ℝ ∞ β := contMDiff_iff_contDiff.mp β.contMDiff
  have hβzero' (x : X) (hx : x ∉ U) : β =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) :=
    hβzero.filter_mono (nhds_le_nhdsSet hx)
  have hβone' (x : X) (hx : x ∈ S) : β =ᶠ[nhds x] (fun _ ↦ (1 : ℝ)) :=
    hβone.filter_mono (nhds_le_nhdsSet hx)
  let p' : X → X → V := fun x ξ ↦ β x • p x ξ
  have hp' : ContDiff ℝ ∞ (Function.uncurry p') := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ U
    · exact (hβ.comp contDiff_fst).contDiffAt.smul
        (hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩))
    · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [(hβzero' z.1 hz).comp_tendsto continuous_fst.continuousAt] with w hw
      change β w.1 = 0 at hw
      simp only [p', Function.uncurry, hw, zero_smul]
  have hpeq (t : T) (z : Z) (hz : (t, z) ∈ C) :
      p' =ᶠ[nhds (φ t z)] p := by
    filter_upwards [hβone' (φ t z) ⟨(t, z), hz, rfl⟩] with x hx
    change β x = 1 at hx
    funext ξ
    simp only [p', hx, one_smul]
  have hpbound (a b : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t z, z ∈ K t → ∀ ξ,
      ‖iteratedFDeriv ℝ a (fun x ↦ iteratedFDeriv ℝ b (p' x) ξ) (φ t z)‖ ≤
        D * (1 + ‖ξ‖) ^ (m - (b : ℝ)) := by
    obtain ⟨D, hD, hDb⟩ := hp.2 S hSU hS a b
    refine ⟨D, hD, ?_⟩
    intro t z hz ξ
    have heq : (fun x ↦ iteratedFDeriv ℝ b (p' x) ξ) =ᶠ[nhds (φ t z)]
        (fun x ↦ iteratedFDeriv ℝ b (p x) ξ) := by
      filter_upwards [hpeq t z hz] with x hx
      rw [hx]
    rw [(heq.iteratedFDeriv ℝ a).eq_of_nhds]
    exact hDb (φ t z) ⟨(t, z), hz, rfl⟩ ξ
  -- Compactness controls every normalized coordinate jet and every coefficient jet.
  have hgbound (a : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t,
      ∀ w ∈ K t ×ˢ Metric.closedBall (0 : X) 1,
        ‖iteratedFDeriv ℝ a (fun z : Z × X ↦ (φ t z.1, Θ t z.1 z.2)) w‖ ≤ D := by
    obtain ⟨D, hD⟩ := (hC.prod (isCompact_closedBall (0 : X) 1)).exists_bound_of_continuousOn
      ((hgjets a).mono (prod_mono hCW (subset_univ _)))
    refine ⟨max D 0, le_max_right _ _, ?_⟩
    intro t w hw
    exact (hD ((t, w.1), w.2) ⟨hw.1, hw.2⟩).trans (le_max_left _ _)
  have hLbound (a : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ t z, z ∈ K t →
      ‖iteratedFDeriv ℝ a (L t) z‖ ≤ D := by
    obtain ⟨D, hD⟩ := hC.exists_bound_of_continuousOn ((hLjets a).mono hCW)
    exact ⟨max D 0, le_max_right _ _, fun t z hz ↦ (hD (t, z) hz).trans (le_max_left _ _)⟩
  -- The actual inverse matrices give a common two-sided frequency comparison.
  have hΘinv : ContinuousOn (fun z : T × Z ↦ (Θ z.1 z.2).inverse) C := by
    intro z hz
    exact (((hinv z (hCW hz)).contDiffAt_map_inverse (n := ∞)).continuousAt).comp_continuousWithinAt
      (f := fun w : T × Z ↦ Θ w.1 w.2) ((hΘcont.mono hCW) z hz)
  obtain ⟨B₁, hB₁⟩ := hC.exists_bound_of_continuousOn (hΘcont.mono hCW)
  obtain ⟨B₂, hB₂⟩ := hC.exists_bound_of_continuousOn hΘinv
  let B : ℝ := max 1 (max B₁ B₂)
  have hB : 1 ≤ B := le_max_left _ _
  have hupper (t : T) (z : Z) (hz : z ∈ K t) (ξ : X) : ‖Θ t z ξ‖ ≤ B * ‖ξ‖ :=
    (Θ t z).le_opNorm ξ |>.trans (mul_le_mul_of_nonneg_right
      ((hB₁ (t, z) hz).trans ((le_max_left _ _).trans (le_max_right _ _))) (norm_nonneg _))
  have hlower (t : T) (z : Z) (hz : z ∈ K t) (ξ : X) : ‖ξ‖ ≤ B * ‖Θ t z ξ‖ := by
    calc
      ‖ξ‖ = ‖(Θ t z).inverse (Θ t z ξ)‖ := by rw [(hinv (t, z) (hCW hz)).inverse_apply_self]
      _ ≤ ‖(Θ t z).inverse‖ * ‖Θ t z ξ‖ := (Θ t z).inverse.le_opNorm _
      _ ≤ B * ‖Θ t z ξ‖ := mul_le_mul_of_nonneg_right
        ((hB₂ (t, z) hz).trans ((le_max_right _ _).trans (le_max_right _ _))) (norm_nonneg _)
  obtain ⟨D, hD, hDb⟩ := exists_uniform_bound_linearMap_symbol_comp_of_contDiffOn
    p' hp' φ Θ O K hO (fun _ _ hz ↦ hCW hz) hφ hΘ m hgbound hpbound B hB hupper hlower
      L hL hLbound i j
  refine ⟨D, hD, ?_⟩
  intro t z hz ξ
  -- Restore the original local symbol before taking the exact mixed derivative.
  have hlocal : (fun w η ↦ L t w (p' (φ t w) (Θ t w η))) =ᶠ[nhds z]
      (fun w η ↦ L t w (p (φ t w) (Θ t w η))) := by
    have hφat := ((hφ t).contDiffAt ((hO t).mem_nhds (hCW hz))).continuousAt
    filter_upwards [(hpeq t z hz).comp_tendsto hφat] with w hw
    change p' (φ t w) = p (φ t w) at hw
    rw [hw]
  have hder : (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ L t w (p' (φ t w) (Θ t w η))) ξ)
      =ᶠ[nhds z] (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ L t w (p (φ t w) (Θ t w η))) ξ) := by
    filter_upwards [hlocal] with w hw
    rw [hw]
  rw [← (hder.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hDb t z hz ξ

end AtiyahSinger
