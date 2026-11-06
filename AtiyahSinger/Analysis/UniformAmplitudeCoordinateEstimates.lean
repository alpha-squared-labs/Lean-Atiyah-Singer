/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothCompositionFamilies
public import AtiyahSinger.Analysis.UniformLocalSymbolCoordinateEstimates

/-!
# Uniform amplitude estimates with spatial linear factors

Public module ID: M1042.

A family of spatial linear coefficients with uniform derivative bounds preserves
the real symbol order after local base and frequency substitutions. The coefficient may
include both frame transformations, the absolute Jacobians, and the fixed
near-diagonal localization. Its derivatives are bounded on the specified moving
sets. Frequency differentiation never hits that coefficient.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set Topology
open scoped ContDiff Manifold

/-- Local spatial linear factors preserve uniform symbol bounds on the specified moving sets. -/
theorem exists_uniform_bound_linearMap_symbol_comp_of_contDiffOn
    {T : Type*} {Z X V V' : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
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
    (hlower : ∀ t z, z ∈ K t → ∀ ξ, ‖ξ‖ ≤ B * ‖Θ t z ξ‖)
    (L : T → Z → V →L[ℝ] V') (hL : ∀ t, ContDiffOn ℝ ∞ (L t) (W t))
    (hLbound : ∀ a : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t z, z ∈ K t →
      ‖iteratedFDeriv ℝ a (L t) z‖ ≤ D) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t z, z ∈ K t → ∀ ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ L t w (p (φ t w) (Θ t w η))) ξ) z‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  let q (t : T) (z : Z) (ξ : X) : V := p (φ t z) (Θ t z ξ)
  have hq (t : T) : ContDiffOn ℝ ∞ (Function.uncurry (q t)) (W t ×ˢ univ) := by
    intro w hw
    have hφat := (hφ t).contDiffAt ((hW t).mem_nhds hw.1)
    have hΘat := (hΘ t).contDiffAt ((hW t).mem_nhds hw.1)
    exact (hp.contDiffAt.comp w ((hφat.comp w contDiffAt_fst).prodMk
      ((hΘat.comp w contDiffAt_fst).clm_apply contDiffAt_snd))).contDiffWithinAt
  have hqj (t : T) (ξ : X) :
      ContDiffOn ℝ ∞ (fun z ↦ iteratedFDeriv ℝ j (q t z) ξ) (W t) := by
    have hparam (a : ℕ) (z : Z) (hz : z ∈ W t) : ContDiffAt ℝ ∞
        (fun p : Z × X ↦ iteratedFDeriv ℝ a (q t p.1) p.2) (z, ξ) := by
      have hbase : ContDiffAt ℝ ∞ (Function.uncurry (q t)) (z, ξ) :=
        (hq t).contDiffAt (((hW t).prod isOpen_univ).mem_nhds ⟨hz, mem_univ ξ⟩)
      induction a with
      | zero =>
        exact hbase.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ X V).symm : _ →L[ℝ] X [×0]→L[ℝ] V)
      | succ a ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun p : Z × X ↦ fun η : X ↦
              iteratedFDeriv ℝ a (q t p.1) η)) ((z, ξ), ξ) :=
          ih.comp ((z, ξ), ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun p : Z × X ↦ fderiv ℝ (iteratedFDeriv ℝ a (q t p.1)) p.2) (z, ξ) :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (a + 1) ↦ X) V).symm :
            _ →L[ℝ] X [×(a + 1)]→L[ℝ] V)
    intro z hz
    exact ((hparam j z hz).comp z (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hqbound (a : ℕ) := exists_uniform_bound_symbol_comp_linear_frequency_of_contDiffOn
    p hp φ Θ W K hW hKW hφ hΘ m hgbound hpbound B hB hupper hlower a j
  choose C hC hCb using hqbound
  choose D hD hDb using hLbound
  let C' := ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * D a * C (i - a)
  have hC' : 0 ≤ C' := Finset.sum_nonneg (fun a _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD a)) (hC (i - a)))
  let N := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ X) V V'
  have hN : ‖N‖ ≤ 1 := by
    apply N.opNorm_le_bound zero_le_one
    intro A
    rw [one_mul]
    apply (N A).opNorm_le_bound (norm_nonneg A)
    intro v
    exact A.norm_compContinuousMultilinearMap_le v
  refine ⟨C', hC', ?_⟩
  intro t z hzK ξ
  have hzW := hKW t hzK
  -- All frequency derivatives belong to the symbol factor; spatial derivatives use Leibniz.
  have hevent : (fun w ↦ iteratedFDeriv ℝ j
      (fun η ↦ L t w (p (φ t w) (Θ t w η))) ξ) =ᶠ[𝓝 z]
      (fun w ↦ N (L t w) (iteratedFDeriv ℝ j (q t w) ξ)) := by
    filter_upwards [(hW t).mem_nhds hzW] with w hw
    have hslice : ContDiffAt ℝ ∞ (q t w) ξ :=
      ((hq t).contDiffAt (((hW t).prod isOpen_univ).mem_nhds
        ⟨hw, mem_univ ξ⟩)).comp ξ (contDiffAt_const.prodMk contDiffAt_id)
    exact (L t w).iteratedFDeriv_comp_left hslice (by simp)
  rw [(hevent.iteratedFDeriv ℝ i).eq_of_nhds]
  have hprod := N.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    (hL t) (hqj t ξ) (hW t).uniqueDiffOn hzW (n := i) (by simp) hN
  simp only [iteratedFDerivWithin_of_isOpen _ (hW t) hzW] at hprod
  apply hprod.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  calc
    _ ≤ (i.choose a : ℝ) * D a *
        (C (i - a) * (1 + ‖ξ‖) ^ (m - (j : ℝ))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hDb a t z hzK) (Nat.cast_nonneg _))
        (hCb (i - a) t z hzK ξ) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hD a))
    _ = _ := by ring

/-- Uniform spatial coefficient bounds preserve the order of locally transformed symbols. -/
theorem exists_uniform_bound_linearMap_symbol_comp
    {T : Type*} {Z X V V' : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V']
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
    (hlower : ∀ t z, z ∈ K t → ∀ ξ, ‖ξ‖ ≤ B * ‖Θ t z ξ‖)
    (L : T → Z → V →L[ℝ] V') (hL : ∀ t, ContDiff ℝ ∞ (L t))
    (hsupp : ∀ t, tsupport (L t) ⊆ K t)
    (hLbound : ∀ a : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ t z, z ∈ K t →
      ‖iteratedFDeriv ℝ a (L t) z‖ ≤ D) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t z ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ L t w (p (φ t w) (Θ t w η))) ξ) z‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := exists_uniform_bound_linearMap_symbol_comp_of_contDiffOn
    p hp φ Θ W K hW hKW hφ hΘ m hgbound hpbound B hB hupper hlower
    L (fun t ↦ (hL t).contDiffOn) hLbound i j
  refine ⟨C, hC, ?_⟩
  intro t z ξ
  by_cases hz : z ∈ tsupport (L t)
  · exact hCb t z (hsupp t hz) ξ
  · -- Outside its original closed support, the whole coefficient and all jets vanish locally.
    have hevent : (fun w ↦ iteratedFDeriv ℝ j
        (fun η ↦ L t w (p (φ t w) (Θ t w η))) ξ) =ᶠ[𝓝 z] (fun _ ↦ 0) := by
      filter_upwards [(isClosed_tsupport (L t)).isOpen_compl.mem_nhds hz] with w hw
      have hzero : L t w = 0 := image_eq_zero_of_notMem_tsupport hw
      simp only [hzero, zero_apply, iteratedFDeriv_fun_zero, Pi.zero_apply]
    rw [(hevent.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg hC (by positivity)

end AtiyahSinger
