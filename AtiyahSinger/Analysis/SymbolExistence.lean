/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolQuotient

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import AtiyahSinger.Analysis.InverseSymbolEstimates
import all AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Inversion and asymptotic summation of local symbols

Public module ID: M1020.

High-frequency inversion and general asymptotic summation use the original
local symbol filtration, mixed derivatives and open-domain hypotheses.
The inverse norm bound is supplied explicitly. Summation uses frequency
cutoffs with radii chosen along a compact spatial exhaustion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set
open scoped ContDiff Topology

set_option maxSynthPendingDepth 25

variable {n r q : ℕ}

set_option maxHeartbeats 800000 in
-- This local extension combines parameter differentiation and the spatial Leibniz estimate.
/-- Preserve the full frequency family near a compact spatial set while extending the symbol.
This extension supplies inverse estimates and frequency truncations in summation. -/
private theorem exists_symbol_extension_of_isCompact
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol U m p)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ p' : SymbolFunction n r q, IsSymbol univ m p' ∧
      ∀ x ∈ K, p' =ᶠ[nhds x] p := by
  classical
  -- Spatial cutoffs provide a globally smooth representative without changing the germs on K.
  have hLocalized (χ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
      IsSymbol Set.univ m (fun x ξ ↦ (χ x : ℂ) • p x ξ) := by
    /- Stage 1: near the cutoff support use the smooth product formula. Outside
    that closed support the extension is zero on a neighborhood, including at the
    boundary of U. These descriptions give joint smoothness on the full space.
    Stage 2: the compact cutoff support lies inside U. Leibniz's rule and the
    finitely many coefficient bounds needed for each mixed
    derivative give the symbol estimate there; outside, that derivative vanishes.
    No smoothness of the original totalized p outside U is used. -/
    classical
    let P := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    have hχc : ContDiff ℝ ∞ (fun x ↦ (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
    -- Outside the closed cutoff support the full frequency-valued symbol vanishes locally.
    have hzero (x : P) (hx : x ∉ tsupport χ) :
        (fun x ξ ↦ (χ x : ℂ) • p x ξ) =ᶠ[nhds x] (fun _ ↦ 0) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      funext ξ
      simp [image_eq_zero_of_notMem_tsupport hy]
    refine ⟨?_, ?_⟩
    · intro z _
      apply ContDiffAt.contDiffWithinAt
      by_cases hz : z.1 ∈ tsupport χ
      · have hpz := hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds
          ⟨hs hz, Set.mem_univ z.2⟩)
        apply ((hχc.contDiffAt.comp z contDiffAt_fst).smul hpz).congr_of_eventuallyEq
        filter_upwards [continuous_fst.continuousAt (hU.mem_nhds (hs hz))] with y hy
        change y.1 ∈ U at hy
        simp only [Function.uncurry]
        rfl
      · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
        filter_upwards [continuous_fst.continuousAt (hzero z.1 hz)] with y hy
        exact congrFun hy y.2
    · intro K _ _ i j
      -- Parameter differentiation retains smoothness before applying the spatial product rule.
      have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
          (f : P → P → V) (x ξ : P)
          (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ)) (k : ℕ) :
          ContDiffAt ℝ ∞ (fun z : P × P ↦ iteratedFDeriv ℝ k (f z.1) z.2) (x, ξ) := by
        induction k with
        | zero =>
          exact hf.continuousLinearMap_comp
            ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
        | succ k ih =>
          have h : ContDiffAt ℝ ∞
              (Function.uncurry (fun z : P × P ↦ fun η : P ↦ iteratedFDeriv ℝ k (f z.1) η))
              ((x, ξ), ξ) := ih.comp ((x, ξ), ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
          have hd : ContDiffAt ℝ ∞
              (fun z : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) (x, ξ) :=
            h.fderiv contDiffAt_snd (by simp)
          exact hd.continuousLinearMap_comp
            ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P) V).symm :
              _ →L[ℝ] P [×(k + 1)]→L[ℝ] V)
      have hfreq (ξ : P) : ContDiffOn ℝ ∞ (fun x ↦ iteratedFDeriv ℝ j (p x) ξ) U := by
        intro x hx
        exact ((parametric p x ξ
          (hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ ξ⟩)) j).comp x
            (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
      -- The fixed support itself is compact in U, and controls every cutoff and symbol derivative.
      have hbounded (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport χ,
          ‖iteratedFDeriv ℝ k (fun y ↦ (χ y : ℂ)) x‖ ≤ B := by
        obtain ⟨B, hB⟩ := (hc.image (hχc.continuous_iteratedFDeriv (by simp)).norm).bddAbove
        exact ⟨max B 0, le_max_right _ _, fun x hx ↦
          (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
      choose B hB hb using hbounded
      choose C hC hcBound using fun k ↦ hp.2 (tsupport χ) hs hc k j
      refine ⟨∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * B k * C (i - k),
        Finset.sum_nonneg (fun k _ ↦ mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hC (i - k))), ?_⟩
      intro x _ ξ
      by_cases hx : x ∈ tsupport χ
      · have hxU := hs hx
        have heq : (fun y ↦ iteratedFDeriv ℝ j ((fun x ξ ↦ (χ x : ℂ) • p x ξ) y) ξ) =ᶠ[nhds x]
            (fun y ↦ (χ y : ℂ) • iteratedFDeriv ℝ j (p y) ξ) := by
          filter_upwards [hU.mem_nhds hxU] with y hy
          have hpy := (hp.1.contDiffAt
            ((hU.prod isOpen_univ).mem_nhds ⟨hy, Set.mem_univ ξ⟩)).comp ξ
              (contDiffAt_const.prodMk contDiffAt_id)
          exact iteratedFDeriv_const_smul_apply' (hpy.of_le (by simp))
        rw [symbolDerivative, (heq.iteratedFDeriv ℝ i).eq_of_nhds]
        have hbound := norm_iteratedFDerivWithin_smul_le hχc.contDiffOn (hfreq ξ)
          hU.uniqueDiffOn hxU (n := i) (by simp)
        simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hbound
        apply hbound.trans
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        have hpk := hcBound (i - k) x hx ξ
        change ‖iteratedFDeriv ℝ (i - k) (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) x‖ ≤ _ at hpk
        calc
          (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun y ↦ (χ y : ℂ)) x‖ *
              ‖iteratedFDeriv ℝ (i - k) (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) x‖ ≤
              (i.choose k : ℝ) * B k * (C (i - k) * (1 + ‖ξ‖) ^ (m - (j : ℝ))) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hb k x hx) (Nat.cast_nonneg _)) hpk
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB k))
          _ = _ := by ring
      · -- Off that support every mixed derivative is the derivative of a local zero family.
        have heq : (fun y ↦ iteratedFDeriv ℝ j ((fun x ξ ↦ (χ x : ℂ) • p x ξ) y) ξ) =ᶠ[nhds x]
            (fun _ ↦ 0) := by
          filter_upwards [hzero x hx] with y hy
          rw [hy]
          exact congrFun (iteratedFDeriv_zero (𝕜 := ℝ) (n := j)) ξ
        rw [symbolDerivative, (heq.iteratedFDeriv ℝ i).eq_of_nhds]
        simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        exact mul_nonneg (Finset.sum_nonneg (fun k _ ↦ mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hC (i - k))))
          (Real.rpow_nonneg (by positivity) _)
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W', hW', hWW', hW'U, hW'c⟩ :=
    exists_open_between_and_isCompact_closure hWc hU hWU
  obtain ⟨β, hβ, _, hβsupp, hβone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW' isClosed_closure hWW'
  have hcβ : HasCompactSupport β := by
    simpa only [HasCompactSupport, tsupport, hβsupp] using hW'c
  have hβU : tsupport β ⊆ U := by
    simpa only [tsupport, hβsupp] using hW'U
  let p' : SymbolFunction n r q := fun x ξ ↦ (β x : ℂ) • p x ξ
  have hp' : IsSymbol univ m p' := hLocalized β hβ hcβ hβU
  refine ⟨p', hp', ?_⟩
  intro x hx
  filter_upwards [hW.mem_nhds (hKW hx)] with y hy
  funext ξ
  have hβy : β y = 1 := (hβone y).mp (subset_closure hy)
  simp only [p', hβy, Complex.ofReal_one, one_smul]

set_option maxHeartbeats 800000 in
-- Fixed-radius inversion combines local matrix derivative estimates with compact frequency bounds.
/-- SL01: the high-frequency inverse has order -m after a cutoff.
An inverse bound is explicit; pointwise invertibility of an arbitrary symbol is insufficient. -/
theorem exists_inverse_symbol (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m R : ℝ) (hR : 0 < R)
    (p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)))
    (hp : IsSymbol U m p)
    (hinv : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → (p x ξ).IsInvertible)
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
        ‖(p x ξ).inverse‖ ≤ C * (1 + ‖ξ‖) ^ (-m)) :
    ∃ a, IsSymbol U (-m) a ∧
      ∀ x ∈ U, ∀ ξ, R + 2 ≤ ‖ξ‖ → a x ξ = (p x ξ).inverse := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  -- A fixed frequency plateau uses the original uniform radius throughout U.
  let φ : ContDiffBump (0 : X) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  let χ : X → ℝ := fun ξ ↦ 1 - φ ξ
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub φ.contDiff
  have hχzero (ξ : X) (hξ : ‖ξ‖ ≤ R + 1) : χ ξ = 0 := by
    change 1 - φ ξ = 0
    rw [φ.one_of_mem_closedBall (by simpa [φ] using hξ), sub_self]
  have hχone (ξ : X) (hξ : R + 2 ≤ ‖ξ‖) : χ ξ = 1 := by
    change 1 - φ ξ = 1
    rw [φ.zero_of_le_dist (by simpa [φ] using hξ), sub_zero]
  let a : SymbolFunction n r r := fun x ξ ↦ χ ξ • (p x ξ).inverse
  have ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ) := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    by_cases hξ : R < ‖z.2‖
    · have hi : ContDiffAt ℝ ∞
          (ContinuousLinearMap.inverse : (V →L[ℂ] V) → (V →L[ℂ] V)) (p z.1 z.2) :=
        ((hinv z.1 hz.1 z.2 hξ.le).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ
      have hiComp := ContDiffAt.comp (f := Function.uncurry p)
        (g := (ContinuousLinearMap.inverse : (V →L[ℂ] V) → (V →L[ℂ] V)))
        z hi (hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))
      exact (hχ.comp contDiff_snd).contDiffAt.smul hiComp
    · apply (contDiffAt_const (c := (0 : V →L[ℂ] V))).congr_of_eventuallyEq
      have hsmall : ‖z.2‖ < R + 1 := by linarith [le_of_not_gt hξ]
      filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hsmall]
        with w hw
      change χ w.2 • (p w.1 w.2).inverse = 0
      rw [hχzero w.2 hw.le, zero_smul]
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · intro K hKU hK i j
    obtain ⟨p', hp', heq⟩ := exists_symbol_extension_of_isCompact U hU m p hp K hKU hK
    obtain ⟨B, hB, hbound⟩ := hbound K hKU hK
    obtain ⟨D, hD, hDbound⟩ := exists_symbolDerivative_inverse_bound m p' hp' K hK R B hB
      (fun x hx ξ hξ ↦ by rw [congrFun ((heq x hx).eq_of_nhds) ξ]; exact hinv x (hKU hx) ξ hξ)
      (fun x hx ξ hξ ↦ by rw [congrFun ((heq x hx).eq_of_nhds) ξ]; exact hbound x hx ξ hξ) i j
    -- Above R+3 the same cutoff inverse and localized inverse agree on neighborhoods.
    have hhigh (x : X) (hx : x ∈ K) (ξ : X) (hξ : R + 3 ≤ ‖ξ‖) :
        ‖symbolDerivative a i j x ξ‖ ≤ D * (1 + ‖ξ‖) ^ (-m - (j : ℝ)) := by
      have hevent : (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) =ᶠ[nhds x]
          (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (p' y η).inverse) ξ) := by
        filter_upwards [heq x hx] with y hy
        have hevent' : a y =ᶠ[nhds ξ] (fun η ↦ (p' y η).inverse) := by
          have hstrict : R + 2 < ‖ξ‖ := by linarith
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hstrict]
            with η hη
          change χ η • (p y η).inverse = (p' y η).inverse
          rw [hχone η hη.le, one_smul, congrFun hy η]
        exact (hevent'.iteratedFDeriv ℝ j).eq_of_nhds
      have hder : symbolDerivative a i j x ξ =
          symbolDerivative (fun y η ↦ (p' y η).inverse) i j x ξ :=
        (hevent.iteratedFDeriv ℝ i).eq_of_nhds
      rw [hder]
      exact hDbound x hx ξ (by linarith)
    -- At bounded frequencies every weighted mixed derivative is continuous on K times a ball.
    have parametric {P Q H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
        [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup H] [NormedSpace ℝ H]
        (f : P → Q → H) (x : P) (y : Q)
        (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
        ContDiffAt ℝ ∞ (fun z : P × Q ↦ iteratedFDeriv ℝ j (f z.1) z.2) (x, y) := by
      induction j with
      | zero =>
        exact hf.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Q H).symm : _ →L[ℝ] Q [×0]→L[ℝ] H)
      | succ j ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun z : P × Q ↦ fun w : Q ↦ iteratedFDeriv ℝ j (f z.1) w))
            ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun z : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2) (x, y) :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) H).symm :
            _ →L[ℝ] Q [×(j + 1)]→L[ℝ] H)
    let w : X × X → ℝ := fun z ↦ (1 + ‖z.2‖) ^ (-m - (j : ℝ))
    have hwpos (z : X × X) : 0 < w z := by
      dsimp only [w]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hw : Continuous w := by
      have hbase : Continuous (fun z : X × X ↦ (1 : ℝ) + ‖z.2‖) :=
        continuous_const.add continuous_snd.norm
      exact hbase.rpow_const (fun _ ↦ Or.inl (ne_of_gt (by positivity)))
    have hratio : ContinuousOn (fun z : X × X ↦
        ‖symbolDerivative a i j z.1 z.2‖ / w z) (K ×ˢ Metric.closedBall 0 (R + 3)) := by
      intro z hz
      have haz := ha.contDiffAt
        ((hU.prod isOpen_univ).mem_nhds ⟨hKU hz.1, mem_univ _⟩)
      have hfreq := parametric a z.1 z.2 haz j
      have hswap := hfreq.comp (z.2, z.1) (contDiffAt_snd.prodMk contDiffAt_fst)
      have hspace := parametric (fun ξ x ↦ iteratedFDeriv ℝ j (a x) ξ) z.2 z.1 hswap i
      exact (((hspace.comp z (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt.norm).div
        hw.continuousAt (hwpos z).ne').continuousWithinAt
    obtain ⟨D₀, hD₀⟩ := ((hK.prod (isCompact_closedBall (0 : X) (R + 3))).image_of_continuousOn
      hratio).bddAbove
    refine ⟨max D (max D₀ 0), hD.trans (le_max_left _ _), ?_⟩
    intro x hx ξ
    by_cases hξ : R + 3 ≤ ‖ξ‖
    · exact (hhigh x hx ξ hξ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (hwpos (x, ξ)).le)
    · have hlow : (x, ξ) ∈ K ×ˢ Metric.closedBall (0 : X) (R + 3) :=
        ⟨hx, by simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_not_ge hξ⟩
      have hdiv := hD₀ ⟨(x, ξ), hlow, rfl⟩
      exact ((div_le_iff₀ (hwpos (x, ξ))).mp hdiv).trans
        (mul_le_mul_of_nonneg_right
          ((le_max_left D₀ 0).trans (le_max_right D (max D₀ 0))) (hwpos (x, ξ)).le)
  · intro x _ ξ hξ
    simp only [a, hχone ξ hξ, one_smul]

set_option maxHeartbeats 800000 in
-- Frequency rescaling reduces each mixed Leibniz estimate to bounded full derivatives.
/-- Frequency truncations have symbol bounds uniform in every dilation radius at least one. -/
private theorem exists_bound_frequency_truncation
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol U m p)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (hφ : φ.rOut ≤ 2)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) (hK : IsCompact K) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (fun y η ↦ (1 - φ (R⁻¹ • η)) • p y η) i j x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let k := i + j
  obtain ⟨p', hp', heq⟩ := exists_symbol_extension_of_isCompact U hU m p hp K hKU hK
  have hs : ContDiff ℝ ∞ (Function.uncurry p') := by
    simpa only [univ_prod_univ, contDiffOn_univ] using hp'.1
  choose A hA hbound using hp'.2 K (subset_univ _) hK
  let A' := ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1), A u v
  have hA' : 0 ≤ A' := Finset.sum_nonneg (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦ hA u v))
  have hAA' (u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) : A u v ≤ A' := by
    have h₁ : A u v ≤ ∑ w ∈ Finset.range (k + 1), A u w :=
      Finset.single_le_sum (fun w _ ↦ hA u w) (Finset.mem_range.mpr (by omega))
    have h₂ : (∑ w ∈ Finset.range (k + 1), A u w) ≤ A' :=
      Finset.single_le_sum (fun w _ ↦ Finset.sum_nonneg (fun v _ ↦ hA w v))
        (Finset.mem_range.mpr (by omega))
    exact h₁.trans h₂
  let χ : X → ℝ := fun ξ ↦ 1 - φ ξ
  have hφsmooth : ContDiff ℝ ∞ (φ : X → ℝ) := φ.contDiff
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub hφsmooth
  have hχbound (b : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ ξ : X,
      ‖iteratedFDeriv ℝ b χ ξ‖ ≤ D := by
    obtain ⟨D, hD⟩ := (φ.hasCompactSupport.iteratedFDeriv b).exists_bound_of_continuous
      (hφsmooth.continuous_iteratedFDeriv (by simp))
    refine ⟨1 + max D 0, by positivity, ?_⟩
    intro ξ
    have hconst : ‖iteratedFDeriv ℝ b (fun _ : X ↦ (1 : ℝ)) ξ‖ ≤ 1 := by
      cases b with
      | zero => simp
      | succ b => simp [iteratedFDeriv_succ_const]
    rw [show χ = (fun _ : X ↦ (1 : ℝ)) - (φ : X → ℝ) from rfl,
      iteratedFDeriv_sub_apply
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : X ↦ (1 : ℝ))).contDiffAt.of_le (by simp))
        (hφsmooth.contDiffAt.of_le (by simp))]
    exact (norm_sub_le _ _).trans
      (add_le_add hconst ((hD ξ).trans (le_max_left _ _)))
  choose D hD hχD using hχbound
  let C := ∑ b ∈ Finset.range (k + 1),
    (k.choose b : ℝ) * (D b * 3 ^ b) * (2 ^ (k - b) * A')
  have hC : 0 ≤ C := Finset.sum_nonneg (fun b _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD b) (by positivity)))
      (mul_nonneg (by positivity) hA'))
  refine ⟨max C (A i j), le_max_of_le_left hC, ?_⟩
  intro R hR x hx ξ
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let b : SymbolFunction n r q := fun y η ↦ χ (R⁻¹ • η) • p' y η
  have hder : symbolDerivative (fun y η ↦ (1 - φ (R⁻¹ • η)) • p y η) i j x ξ =
      symbolDerivative b i j x ξ := by
    have hnear : (fun y ↦ iteratedFDeriv ℝ j
        (fun η ↦ (1 - φ (R⁻¹ • η)) • p y η) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) := by
      filter_upwards [heq x hx] with y hy
      congr 1
      funext η
      change χ (R⁻¹ • η) • p y η = χ (R⁻¹ • η) • p' y η
      rw [congrFun hy η]
    exact (hnear.iteratedFDeriv ℝ i).eq_of_nhds
  rw [hder]
  by_cases hlarge : 2 * R < ‖ξ‖
  · -- Beyond the transition annulus the truncation is locally the original symbol.
    have hfreq (y : X) : b y =ᶠ[nhds ξ] p' y := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlarge]
        with η hη
      have hnorm : 2 < ‖R⁻¹ • η‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
        exact (lt_inv_mul_iff₀ hRpos).mpr (by simpa only [mul_comm] using hη)
      have hφzero : φ (R⁻¹ • η) = 0 := φ.zero_of_le_dist
        (by simpa only [dist_zero_right] using hφ.trans hnorm.le)
      simp only [b, χ, hφzero, sub_zero, one_smul]
    have hder' : symbolDerivative b i j x ξ = symbolDerivative p' i j x ξ := by
      apply congrArg (fun f ↦ iteratedFDeriv ℝ i f x)
      funext y
      exact ((hfreq y).iteratedFDeriv ℝ j).eq_of_nhds
    rw [hder']
    exact (hbound i j x hx ξ).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
  · -- At frequencies of norm at most 2R, normalize by 1 + ‖ξ‖.
    let t : ℝ := 1 + ‖ξ‖
    have ht : 0 < t := by dsimp [t]; positivity
    let η : X := t⁻¹ • ξ
    have htη : t • η = ξ := smul_inv_smul₀ ht.ne' ξ
    let a' : X → X → H := fun y ζ ↦ p' y (t • ζ)
    have hscale : ContDiff ℝ ∞ (fun z : X × X ↦ t • z.2) :=
      (contDiff_const (c := t)).smul contDiff_snd
    have ha' : ContDiff ℝ ∞ (Function.uncurry a') :=
      hs.comp (contDiff_fst.prodMk hscale)
    have hscaled (u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) :
        ‖iteratedFDeriv ℝ u (fun y ↦ iteratedFDeriv ℝ v (a' y) η) x‖ ≤ A' * t ^ m := by
      rw [mixed_iteratedFDeriv_frequency_smul p' t ht.ne' u v, htη,
        norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht v)]
      calc
        _ ≤ t ^ v * (A u v * t ^ (m - (v : ℝ))) :=
          mul_le_mul_of_nonneg_left (hbound u v x hx ξ) (pow_nonneg ht.le _)
        _ = A u v * t ^ m := by
          rw [mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add ht]
          congr 2
          ring
        _ ≤ A' * t ^ m := mul_le_mul_of_nonneg_right (hAA' u v hu hv)
          (Real.rpow_nonneg ht.le _)
    have hfull (u : ℕ) (hu : u ≤ k) :
        ‖iteratedFDeriv ℝ u (Function.uncurry a') (x, η)‖ ≤
          (2 ^ u * A') * t ^ m := by
      have h := norm_iteratedFDeriv_uncurry_le_of_mixed a' ha' u x η (A' * t ^ m)
        (mul_nonneg hA' (Real.rpow_nonneg ht.le _))
        (fun v hv w hw ↦ hscaled v w (hv.trans hu) (hw.trans hu))
      exact h.trans_eq (by ring)
    let L : X × X →L[ℝ] X := (R⁻¹ * t) • ContinuousLinearMap.snd ℝ X X
    have hL : ‖L‖ ≤ 3 := by
      apply L.opNorm_le_bound (by norm_num)
      intro z
      change ‖(R⁻¹ * t) • z.2‖ ≤ 3 * ‖z‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr hRpos) ht)]
      apply mul_le_mul _ (norm_snd_le z) (norm_nonneg _) (by norm_num)
      apply (inv_mul_le_iff₀ hRpos).mpr
      dsimp [t]
      have hsmall := le_of_not_gt hlarge
      linarith
    have hcut (u : ℕ) : ‖iteratedFDeriv ℝ u (χ ∘ L) (x, η)‖ ≤ D u * 3 ^ u := by
      have h := L.iteratedFDerivWithin_comp_right (x := (x, η)) hχ.contDiffOn uniqueDiffOn_univ
        (by simpa only [preimage_univ] using (uniqueDiffOn_univ (𝕜 := ℝ) (E := X × X)))
        (mem_univ _) (i := u) (by simp)
      simp only [preimage_univ, iteratedFDerivWithin_univ] at h
      rw [h]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hχD u _) (pow_le_pow_left₀ (norm_nonneg _) hL _)
        (pow_nonneg (norm_nonneg _) _) (hD u)
    have hprod := norm_iteratedFDeriv_smul_le (hχ.comp L.contDiff) ha' (x, η)
      (n := k) (by simp)
    have hprodBound : ‖iteratedFDeriv ℝ k
        (fun z : X × X ↦ χ (L z) • a' z.1 z.2) (x, η)‖ ≤ C * t ^ m := by
      apply hprod.trans
      dsimp [C]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro u hu
      calc
        _ ≤ (k.choose u : ℝ) * (D u * 3 ^ u) *
            ((2 ^ (k - u) * A') * t ^ m) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hcut u) (Nat.cast_nonneg _))
            (hfull (k - u) (Nat.sub_le _ _)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD u) (by positivity)))
        _ = _ := by ring
    have hsame : (fun z : X × X ↦ χ (L z) • a' z.1 z.2) =
        Function.uncurry (fun y ζ ↦ b y (t • ζ)) := by
      funext z
      change χ ((R⁻¹ * t) • z.2) • p' z.1 (t • z.2) =
        χ (R⁻¹ • (t • z.2)) • p' z.1 (t • z.2)
      rw [smul_smul]
    rw [hsame] at hprodBound
    have hbScaled : ContDiff ℝ ∞ (Function.uncurry (fun y ζ ↦ b y (t • ζ))) := by
      rw [← hsame]
      exact (hχ.comp L.contDiff).smul ha'
    have hmixed := norm_mixed_iteratedFDeriv_le (X := X) (Y := X) (V := H)
      (fun y ζ ↦ b y (t • ζ)) hbScaled i j x η
    have hnorm := hmixed.trans hprodBound
    rw [mixed_iteratedFDeriv_frequency_smul b t ht.ne' i j, htη,
      norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht j)] at hnorm
    have hdivide := (le_div_iff₀ (pow_pos ht j)).mpr
      (show ‖symbolDerivative b i j x ξ‖ * t ^ j ≤ C * t ^ m by
        simpa only [mul_comm, symbolDerivative] using hnorm)
    have hweight : C * t ^ m / t ^ j = C * t ^ (m - (j : ℝ)) := by
      rw [Real.rpow_sub ht, Real.rpow_natCast]
      ring
    exact (hdivide.trans_eq hweight).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le _))

set_option maxHeartbeats 800000 in
-- Local finiteness identifies each derivative with a finite sum before estimating its tail.
/-- An eventually geometric family of symbol seminorms controls the locally finite sum. -/
private theorem isSymbol_tsum_of_geometric_tail
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (m : ℝ)
    (c : ℕ → SymbolFunction n r q) (hc : ∀ k, IsSymbol U m (c k))
    (L : ℕ) (hzero : ∀ k, L ≤ k → ∀ x ∈ U, ∀ ξ,
      ‖ξ‖ < (k : ℝ) → c k x ξ = 0)
    (htail : ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K → ∀ i j : ℕ,
      ∃ J : ℕ, ∀ k, J ≤ k → ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (c k) i j x ξ‖ ≤
          (1 / (2 : ℝ)) ^ k * (1 + ‖ξ‖) ^ (m - (j : ℝ))) :
    IsSymbol U m (fun x ξ ↦ ∑' k, c k x ξ) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let a : SymbolFunction n r q := fun x ξ ↦ ∑' k, c k x ξ
  have hfinite (T : ℕ) (hLT : L ≤ T) (x : X) (hx : x ∈ U) (ξ : X)
      (hξ : ‖ξ‖ < (T : ℝ)) : a x ξ = ∑ k ∈ Finset.range T, c k x ξ := by
    apply tsum_eq_sum
    intro k hk
    have hTk : T ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    exact hzero k (hLT.trans hTk) x hx ξ (hξ.trans_le (by exact_mod_cast hTk))
  have hsmooth (k : ℕ) (x : X) (hx : x ∈ U) (ξ : X) :
      ContDiffAt ℝ ∞ (Function.uncurry (c k)) (x, ξ) :=
    (hc k).1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
  have parametric {P Q H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup H] [NormedSpace ℝ H]
      (f : P → Q → H) (x : P) (y : Q)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun z : P × Q ↦ iteratedFDeriv ℝ j (f z.1) z.2) (x, y) := by
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q H).symm : _ →L[ℝ] Q [×0]→L[ℝ] H)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun z : P × Q ↦ fun w : Q ↦ iteratedFDeriv ℝ j (f z.1) w))
          ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun z : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2) (x, y) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) H).symm :
          _ →L[ℝ] Q [×(j + 1)]→L[ℝ] H)
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨T₀, hT₀⟩ := exists_nat_gt ‖z.2‖
    let T := max L T₀
    have hzT : ‖z.2‖ < (T : ℝ) := hT₀.trans_le (by exact_mod_cast le_max_right L T₀)
    have hsum : ContDiffAt ℝ ∞ (fun z : X × X ↦ ∑ k ∈ Finset.range T, c k z.1 z.2) z :=
      ContDiffAt.sum (fun k _ ↦ hsmooth k z.1 hz.1 z.2)
    apply ContDiffAt.contDiffWithinAt
    apply hsum.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt (hU.mem_nhds hz.1),
      (isOpen_lt continuous_snd.norm continuous_const).mem_nhds hzT] with w hwU hwT
    exact hfinite T (le_max_left _ _) w.1 hwU w.2 hwT
  · intro K hKU hK i j
    obtain ⟨J, hJ⟩ := htail K hKU hK i j
    choose B hB hbound using fun k ↦ (hc k).2 K hKU hK i j
    refine ⟨(∑ k ∈ Finset.range J, B k) + 2,
      add_nonneg (Finset.sum_nonneg (fun k _ ↦ hB k)) (by norm_num), ?_⟩
    intro x hx ξ
    obtain ⟨T₀, hT₀⟩ := exists_nat_gt ‖ξ‖
    let T := max L T₀
    have hξT : ‖ξ‖ < (T : ℝ) := hT₀.trans_le (by exact_mod_cast le_max_right L T₀)
    -- The same finite range works on a full frequency neighborhood and a spatial neighborhood.
    have hfreq : (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) =ᶠ[nhds x]
        (fun y ↦ ∑ k ∈ Finset.range T, iteratedFDeriv ℝ j (c k y) ξ) := by
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      have hevent : a y =ᶠ[nhds ξ] (fun η ↦ ∑ k ∈ Finset.range T, c k y η) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hξT] with η hη
        exact hfinite T (le_max_left _ _) y hy η hη
      rw [(hevent.iteratedFDeriv ℝ j).eq_of_nhds]
      exact iteratedFDeriv_fun_sum_apply (fun k _ ↦
        ((hsmooth k y hy ξ).comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hder : symbolDerivative a i j x ξ =
        ∑ k ∈ Finset.range T, symbolDerivative (c k) i j x ξ := by
      rw [symbolDerivative, (hfreq.iteratedFDeriv ℝ i).eq_of_nhds]
      exact iteratedFDeriv_fun_sum_apply (fun k _ ↦
        ((parametric (c k) x ξ (hsmooth k x (hKU hx) ξ) j).comp x
          (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp))
    change ‖symbolDerivative a i j x ξ‖ ≤ _
    rw [hder]
    let w : ℝ := (1 + ‖ξ‖) ^ (m - (j : ℝ))
    have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    have hterm (k : ℕ) : ‖symbolDerivative (c k) i j x ξ‖ ≤
        ((if k < J then B k else 0) + (1 / (2 : ℝ)) ^ k) * w := by
      by_cases hk : k < J
      · rw [ite_eq_left hk, add_mul]
        exact (hbound k x hx ξ).trans
          (le_add_of_nonneg_right (mul_nonneg (by positivity) hw))
      · rw [ite_eq_right hk, zero_add]
        exact hJ k (Nat.le_of_not_gt hk) x hx ξ
    have hprefix : (∑ k ∈ Finset.range T, if k < J then B k else 0) ≤
        ∑ k ∈ Finset.range J, B k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      · intro k _ _
        exact hB k
    calc
      _ ≤ ∑ k ∈ Finset.range T,
          ((if k < J then B k else 0) + (1 / (2 : ℝ)) ^ k) * w :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ ↦ hterm k))
      _ = ((∑ k ∈ Finset.range T, if k < J then B k else 0) +
          ∑ k ∈ Finset.range T, (1 / (2 : ℝ)) ^ k) * w := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
      _ ≤ ((∑ k ∈ Finset.range J, B k) + 2) * w :=
        mul_le_mul_of_nonneg_right (add_le_add hprefix (sum_geometric_two_le T)) hw

set_option maxHeartbeats 1200000 in
-- The radius selection and all remainder estimates use one locally finite symbol family.
/-- SR01: asymptotic summation of symbols of order tending to negative infinity. -/
theorem exists_symbol_expansion (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℕ → ℝ) (hm : StrictAnti m) (hlim : Filter.Tendsto m Filter.atTop Filter.atBot)
    (terms : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hterms : ∀ j, IsSymbol U (m j) (terms j)) :
    ∃ a, HasSymbolExpansion U m a terms := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let φ : ContDiffBump (0 : X) := ⟨1, 2, by norm_num, by norm_num⟩
  -- A compact exhaustion makes the infinitely many spatial seminorms countable.
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let e : CompactExhaustion U := CompactExhaustion.choice U
  let K : ℕ → Set X := fun k ↦ Subtype.val '' e k
  have hK (k : ℕ) : IsCompact (K k) := (e.isCompact k).image continuous_subtype_val
  have hKU (k : ℕ) : K k ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hKmono : Monotone K := fun i j hij ↦ image_mono (e.subset hij)
  have hcover (S : Set X) (hSU : S ⊆ U) (hS : IsCompact S) : ∃ k, S ⊆ K k := by
    obtain ⟨k, hk⟩ := hS.elim_directed_cover (fun k ↦ interior (K k))
      (fun _ ↦ isOpen_interior) (fun x hx ↦ by
        obtain ⟨k, hk⟩ := e.exists_mem_nhds ⟨x, hSU hx⟩
        have h := hU.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hk
        exact mem_iUnion.mpr ⟨k, mem_interior_iff_mem_nhds.mpr h⟩)
      (Monotone.directed_le (fun i j hij ↦ interior_mono (hKmono hij)))
    exact ⟨k, hk.trans interior_subset⟩
  choose C hC hbound using fun k i j ↦ exists_bound_frequency_truncation
    U hU (m k) (terms k) (hterms k) φ (by norm_num [φ]) (K k) (hKU k) (hK k) i j
  let A : ℕ → ℝ := fun k ↦
    ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), C k i j
  have hA (k : ℕ) : 0 ≤ A k :=
    Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC k i j))
  have hCA (k i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) : C k i j ≤ A k := by
    have h₁ : C k i j ≤ ∑ v ∈ Finset.range (k + 1), C k i v :=
      Finset.single_le_sum (fun v _ ↦ hC k i v) (Finset.mem_range.mpr (by omega))
    have h₂ : (∑ v ∈ Finset.range (k + 1), C k i v) ≤ A k :=
      Finset.single_le_sum (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦ hC k u v))
        (Finset.mem_range.mpr (by omega))
    exact h₁.trans h₂
  -- Each strict order gap lets one radius control the first k spatial and derivative tests.
  have hradius (k : ℕ) : ∃ S : ℝ, ∀ t : ℝ, S ≤ t →
      A (k + 1) * t ^ (m (k + 1) - m k) ≤ (1 / (2 : ℝ)) ^ (k + 1) := by
    have hgap : 0 < m k - m (k + 1) := sub_pos.mpr (hm (Nat.lt_succ_self k))
    have hdecay : Tendsto (fun t : ℝ ↦ A (k + 1) * t ^ (m (k + 1) - m k))
        atTop (nhds 0) := by
      simpa only [neg_sub, mul_zero] using
        (tendsto_rpow_neg_atTop hgap).const_mul (A (k + 1))
    obtain ⟨S, hS⟩ := eventually_atTop.mp
      (hdecay.eventually (Iio_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1))))
    exact ⟨S, fun t ht ↦ (hS t ht).le⟩
  choose S hS using hradius
  let R : ℕ → ℝ
    | 0 => 1
    | k + 1 => max ((k + 1 : ℕ) + 1 : ℝ) (S k)
  have hR (k : ℕ) : 1 ≤ R k := by
    cases k with
    | zero => exact le_rfl
    | succ k =>
      exact (le_add_of_nonneg_left (Nat.cast_nonneg (k + 1))).trans (le_max_left _ _)
  have hkR (k : ℕ) : (k : ℝ) ≤ R k := by
    cases k with
    | zero => norm_num [R]
    | succ k =>
      exact (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)
  let b : ℕ → SymbolFunction n r q := fun k x ξ ↦
    (1 - φ ((R k)⁻¹ • ξ)) • terms k x ξ
  have hbzero (k : ℕ) (x ξ : X) (hξ : ‖ξ‖ ≤ R k) : b k x ξ = 0 := by
    have hRpos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
    have hnorm : ‖(R k)⁻¹ • ξ‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
      exact (inv_mul_le_iff₀ hRpos).mpr (by simpa only [mul_one] using hξ)
    have hone : φ ((R k)⁻¹ • ξ) = 1 :=
      φ.one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall, dist_zero_right, φ] using hnorm)
    simp only [b, hone, sub_self, zero_smul]
  have hbone (k : ℕ) (x ξ : X) (hξ : 2 * R k ≤ ‖ξ‖) : b k x ξ = terms k x ξ := by
    have hRpos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
    have hnorm : 2 ≤ ‖(R k)⁻¹ • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
      exact (le_inv_mul_iff₀ hRpos).mpr (by simpa only [mul_comm] using hξ)
    have hzero : φ ((R k)⁻¹ • ξ) = 0 :=
      φ.zero_of_le_dist (by simpa only [dist_zero_right, φ] using hnorm)
    simp only [b, hzero, sub_zero, one_smul]
  have hb (k : ℕ) : IsSymbol U (m k) (b k) := by
    refine ⟨?_, ?_⟩
    · have hscale : ContDiff ℝ ∞ (fun z : X × X ↦ (R k)⁻¹ • z.2) :=
        (contDiff_const (c := (R k)⁻¹)).smul contDiff_snd
      have hcut : ContDiff ℝ ∞ (fun z : X × X ↦ 1 - φ ((R k)⁻¹ • z.2)) :=
        contDiff_const.sub ((φ.contDiff : ContDiff ℝ ∞ (φ : X → ℝ)).comp hscale)
      exact hcut.contDiffOn.smul (hterms k).1
    · intro Q hQU hQ i j
      obtain ⟨D, hD, hDbound⟩ := exists_bound_frequency_truncation
        U hU (m k) (terms k) (hterms k) φ (by norm_num [φ]) Q hQU hQ i j
      exact ⟨D, hD, hDbound (R k) (hR k)⟩
  have hderzero (k i j : ℕ) (x ξ : X) (hξ : ‖ξ‖ < R k) :
      symbolDerivative (b k) i j x ξ = 0 := by
    have hfreq (y : X) : iteratedFDeriv ℝ j (b k y) ξ = 0 := by
      have heq : b k y =ᶠ[nhds ξ] (fun _ ↦ 0) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hξ] with η hη
        exact hbzero k y η hη.le
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using (heq.iteratedFDeriv ℝ j).eq_of_nhds
    simp only [symbolDerivative, hfreq, iteratedFDeriv_fun_zero, Pi.zero_apply]
  have hsmall (k i j : ℕ) (hi : i ≤ k + 1) (hj : j ≤ k + 1)
      (x : X) (hx : x ∈ K (k + 1)) (ξ : X) :
      ‖symbolDerivative (b (k + 1)) i j x ξ‖ ≤
        (1 / (2 : ℝ)) ^ (k + 1) * (1 + ‖ξ‖) ^ (m k - (j : ℝ)) := by
    by_cases hξ : ‖ξ‖ < R (k + 1)
    · rw [hderzero (k + 1) i j x ξ hξ, norm_zero]
      positivity
    · let t : ℝ := 1 + ‖ξ‖
      have ht : 0 < t := by dsimp [t]; positivity
      have hSt : S k ≤ t := by
        have h := (le_max_right ((k + 1 : ℕ) + 1 : ℝ) (S k)).trans (le_of_not_gt hξ)
        dsimp [t]
        linarith
      have hnorm := hbound (k + 1) i j (R (k + 1)) (hR (k + 1)) x hx ξ
      calc
        _ ≤ A (k + 1) * t ^ (m (k + 1) - (j : ℝ)) := hnorm.trans
          (mul_le_mul_of_nonneg_right (hCA (k + 1) i j hi hj) (Real.rpow_nonneg ht.le _))
        _ = (A (k + 1) * t ^ (m (k + 1) - m k)) * t ^ (m k - (j : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add ht]
          congr 2
          ring
        _ ≤ (1 / (2 : ℝ)) ^ (k + 1) * t ^ (m k - (j : ℝ)) :=
          mul_le_mul_of_nonneg_right (hS k t hSt) (Real.rpow_nonneg ht.le _)
  let a : SymbolFunction n r q := fun x ξ ↦ ∑' k, b k x ξ
  refine ⟨a, ?_⟩
  intro N
  -- Correct only finitely many low-frequency pieces when forming the N-th remainder.
  let c : ℕ → SymbolFunction n r q := fun k ↦ b k - if k < N then terms k else 0
  have hc (k : ℕ) : IsSymbol U (m N) (c k) := by
    by_cases hk : k < N
    · have hdiff : IsSmoothingSymbol U (b k - terms k) := by
        apply isSmoothingSymbol_of_frequency_support hU (b k - terms k) (2 * R k)
          ((hb k).1.sub (hterms k).1)
        intro x hx ξ hξ
        exact sub_eq_zero.mpr (hbone k x ξ hξ)
      simpa only [c, ite_eq_left hk] using hdiff (m N)
    · simpa only [c, ite_eq_right hk, sub_zero] using
        (hb k).mono (hm.antitone (Nat.le_of_not_gt hk))
  have hcZero (k : ℕ) (hNk : N ≤ k) (x : X) (_hx : x ∈ U) (ξ : X)
      (hξ : ‖ξ‖ < (k : ℝ)) : c k x ξ = 0 := by
    change (b k - if k < N then terms k else 0) x ξ = 0
    rw [ite_eq_right (Nat.not_lt_of_ge hNk), sub_zero]
    exact hbzero k x ξ (hξ.le.trans (hkR k))
  have hcTail (Q : Set X) (hQU : Q ⊆ U) (hQ : IsCompact Q) (i j : ℕ) :
      ∃ J : ℕ, ∀ k, J ≤ k → ∀ x ∈ Q, ∀ ξ,
        ‖symbolDerivative (c k) i j x ξ‖ ≤
          (1 / (2 : ℝ)) ^ k * (1 + ‖ξ‖) ^ (m N - (j : ℝ)) := by
    obtain ⟨k₀, hk₀⟩ := hcover Q hQU hQ
    -- Cofinality places every sufficiently late term below this specified remainder order.
    obtain ⟨Jm, hJm⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_atBot (m N)))
    refine ⟨N + k₀ + i + j + Jm + 1, ?_⟩
    intro k hk x hx ξ
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hNk : ¬l + 1 < N := by omega
    have hci : c (l + 1) = b (l + 1) := by simp only [c, ite_eq_right hNk, sub_zero]
    rw [hci]
    have h := hsmall l i j (by omega) (by omega) x (hKmono (by omega) (hk₀ hx)) ξ
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ])
        (sub_le_sub_right (hJm l (by omega)) _)) (by positivity))
  have hcSum := isSymbol_tsum_of_geometric_tail U hU (m N) c hc N hcZero hcTail
  -- Both series are locally finite; identify the constructed sum with the original remainder.
  have heq : EqOn (fun x ξ ↦ ∑' k, c k x ξ) (a - ∑ k ∈ Finset.range N, terms k) U := by
    intro x hx
    funext ξ
    obtain ⟨T₀, hT₀⟩ := exists_nat_gt ‖ξ‖
    let T := max N T₀
    have hξT : ‖ξ‖ < (T : ℝ) := hT₀.trans_le (by exact_mod_cast le_max_right N T₀)
    have hTs (k : ℕ) (hk : k ∉ Finset.range T) : b k x ξ = 0 := by
      have hTk : T ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
      exact hbzero k x ξ (hξT.le.trans ((by exact_mod_cast hTk : (T : ℝ) ≤ k).trans (hkR k)))
    change (∑' k, c k x ξ) = (a - ∑ k ∈ Finset.range N, terms k) x ξ
    rw [tsum_eq_sum (f := fun k ↦ c k x ξ) (s := Finset.range T) (fun k hk ↦ by
      have hTk : T ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
      exact hcZero k ((le_max_left _ _).trans hTk) x hx ξ
        (hξT.trans_le (by exact_mod_cast hTk)))]
    change (∑ k ∈ Finset.range T, (b k x ξ - (if k < N then terms k else 0) x ξ)) =
      (∑' k, b k x ξ) - (∑ k ∈ Finset.range N, terms k) x ξ
    rw [Finset.sum_sub_distrib, tsum_eq_sum hTs]
    congr 1
    simp only [Finset.sum_apply, ite_apply, Pi.zero_apply]
    rw [← Finset.sum_filter]
    have hfilter : (Finset.range T).filter (fun k ↦ k < N) = Finset.range N := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter]
  -- Equality on the open domain preserves the original total mixed derivatives.
  refine ⟨?_, ?_⟩
  · apply hcSum.1.congr
    intro z hz
    exact (congrFun (heq hz.1) z.2).symm
  · intro Q hQU hQ i j
    obtain ⟨D, hD, hDbound⟩ := hcSum.2 Q hQU hQ i j
    refine ⟨D, hD, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j
        ((a - ∑ k ∈ Finset.range N, terms k) y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ ∑' k, c k y η) ξ) := by
      filter_upwards [hU.mem_nhds (hQU hx)] with y hy
      have hfun := heq hy
      rw [← hfun]
    rw [symbolDerivative, (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hDbound x hx ξ

end AtiyahSinger
