/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzJetIntegral
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Banach-valued parameterized Schwartz operators

Public module ID: M0948.

The separating continuous complex dual extends scalar integral exchange to
an integrable Banach image. Actual image integrability remains explicit.
On compact parameter intervals it follows from continuity, so the fundamental
theorem of calculus gives a strong derivative. This supplies weighted-jet
outputs for the local operator argument in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- An integrable Banach image of a Schwartz family commutes with its actual integral. -/
theorem schwartz_integral_map
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)
    (F : Y → 𝓢(E, ℂ)) (hF : Continuous F)
    (hI : ∀ k j : ℕ, Integrable (fun y ↦ SchwartzMap.seminorm ℂ k j (F y)) μ)
    (f : 𝓢(E, ℂ)) (hf : ∀ x, f x = ∫ y, F y x ∂μ)
    (L : 𝓢(E, ℂ) →L[ℂ] V) (hLF : Integrable (fun y ↦ L (F y)) μ) :
    L f = ∫ y, L (F y) ∂μ := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  have h := schwartz_integral_apply μ F hF hI f hf (φ.comp L)
  exact h.trans (φ.integral_comp_comm hLF)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A continuous Schwartz derivative may be passed through a continuous Banach-valued map. -/
theorem hasDerivAt_schwartzMap
    (F F' : ℝ → 𝓢(E, ℂ)) (hF' : Continuous F')
    (hderiv : ∀ (t : ℝ) (x : E), HasDerivAt (fun u ↦ F u x) (F' t x) t)
    (L : 𝓢(E, ℂ) →L[ℂ] V) (t : ℝ) :
    HasDerivAt (fun u ↦ L (F u)) (L (F' t)) t := by
  have hseminorm (k j : ℕ) : Continuous (fun u ↦ SchwartzMap.seminorm ℂ k j (F' u)) := by
    have h := ((schwartzWeightedJet (E := E) k j).continuous.comp hF').norm
    change Continuous (fun u ↦ ‖schwartzWeightedJet k j (F' u)‖) at h
    simpa only [norm_schwartzWeightedJet] using h
  have heval (x : E) : Continuous (fun u ↦ F' u x) := by
    let c := continuousMultilinearCurryFin0 ℝ E ℂ
    have h := c.continuous.comp (((BoundedContinuousFunction.evalCLM ℂ x).comp
      (schwartzWeightedJet (E := E) 0 0)).continuous.comp hF')
    change Continuous (fun u ↦ c (‖x‖ ^ 0 • iteratedFDeriv ℝ 0 (F' u) x)) at h
    simp only [pow_zero, one_smul] at h
    change Continuous (fun u ↦ iteratedFDeriv ℝ 0 (F' u) x (0 : Fin 0 → E)) at h
    simpa only [iteratedFDeriv_zero_apply] using h
  -- On an ordered compact interval, every original seminorm is integrable.
  have hint (a b : ℝ) (hab : a ≤ b) :
      L (F b) - L (F a) = ∫ u in a..b, L (F' u) := by
    have hpoint (x : E) : (F b - F a) x = ∫ u in Ioc a b, F' u x := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ ↦ hderiv u x) ((heval x).intervalIntegrable a b)
      rw [intervalIntegral.integral_of_le hab] at h
      exact h.symm
    have h := schwartz_integral_map (volume.restrict (Ioc a b)) F' hF'
      (fun k j ↦ (hseminorm k j).integrableOn_Ioc) (F b - F a) hpoint L
      ((L.continuous.comp hF').integrableOn_Ioc)
    rw [map_sub, ← intervalIntegral.integral_of_le hab] at h
    exact h
  have hall (a b : ℝ) : L (F b) - L (F a) = ∫ u in a..b, L (F' u) := by
    rcases le_total a b with hab | hba
    · exact hint a b hab
    · rw [intervalIntegral.integral_symm, ← hint b a hba]
      abel
  -- The same identity for varying endpoints gives the claimed derivative.
  have hc : Continuous (fun u ↦ L (F' u)) := L.continuous.comp hF'
  have hFTC := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable t t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have heq : (fun u ↦ L (F u)) = (fun u ↦ L (F t) + ∫ v in t..u, L (F' v)) := by
    funext u
    exact (sub_eq_iff_eq_add.mp (hall t u)).trans (add_comm _ _)
  rw [heq]
  have h := (hasDerivAt_const t (L (F t))).add hFTC
  change HasDerivAt (fun u ↦ L (F t) + ∫ v in t..u, L (F' v)) (0 + L (F' t)) t at h
  simpa only [zero_add] using h

/-- A continuous Schwartz derivative tower gives a smooth Banach value under a continuous map. -/
theorem contDiff_schwartzMap_of_derivative_tower
    (F : ℕ → ℝ → 𝓢(E, ℂ)) (hF : ∀ k : ℕ, Continuous (F k))
    (hderiv : ∀ (k : ℕ) (t : ℝ) (x : E),
      HasDerivAt (fun u ↦ F k u x) (F (k + 1) t x) t)
    (L : 𝓢(E, ℂ) →L[ℂ] V) : ContDiff ℝ ∞ (fun t ↦ L (F 0 t)) := by
  have hD (k : ℕ) (t : ℝ) :
      HasDerivAt (fun u ↦ L (F k u)) (L (F (k + 1) t)) t :=
    hasDerivAt_schwartzMap (F k) (F (k + 1)) (hF (k + 1)) (hderiv k) L t
  -- Each derivative is the functional of the next original Schwartz derivative.
  have hfinite (n : ℕ) : ∀ k : ℕ, ContDiff ℝ n (fun t ↦ L (F k t)) := by
    induction n with
    | zero =>
      intro k
      exact contDiff_zero.mpr (L.continuous.comp (hF k))
    | succ n ih =>
      intro k
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 from rfl, contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hD k t).differentiableAt, by simp, ?_⟩
      have heq : deriv (fun t ↦ L (F k t)) = (fun t ↦ L (F (k + 1) t)) :=
        funext fun t ↦ (hD k t).deriv
      rw [heq]
      exact ih (k + 1)
  exact contDiff_infty.mpr (fun n ↦ hfinite n 0)

end AtiyahSinger
