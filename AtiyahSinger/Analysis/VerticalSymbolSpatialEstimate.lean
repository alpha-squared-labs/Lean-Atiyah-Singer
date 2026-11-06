/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LowConeVerticalEstimate

import AtiyahSinger.Analysis.CompactJetIntegral
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Vertical graph estimates from horizontal vanishing

A compactly spatially supported joint symbol of order one that vanishes on
horizontal covectors has its actual quantization controlled by vertical H1
energy. The fundamental theorem of calculus in the vertical frequency gives
linear vertical growth for every spatial jet, using only the order-zero bound
for one frequency derivative. Compact-parameter integration commutes with the
spatial derivatives, so no exchange of unbounded operator-valued derivatives
or full joint order-zero factorization is needed.

This is the analytic estimate for a symbol difference whose exact horizontal
vanishing has already been proved. Establishing that cancellation for actual
coordinate changes, paired cutoffs and finite partitions is a separate input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

variable {n m r q : ℕ}

set_option maxHeartbeats 1200000 in

/-- A joint order-one symbol vanishing on horizontal covectors has a vertical graph estimate. -/
theorem exists_quantize_vertical_estimate_of_horizontal_zero
    (a : SymbolFunction (n + m) r q) (ha : IsSymbol univ 1 a)
    (K : Set (EuclideanSpace ℝ (Fin (n + m)))) (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → ∀ ξ, a x ξ = 0)
    (hzero : ∀ x ξ, a x
      ((EuclideanSpace.finAddEquivProd (n := n) (m := m)).symm (ξ, 0)) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q))),
        (∀ x, v x = quantize a u x) →
        ‖v.toLp 2‖ ^ 2 ≤ C * (‖u.toLp 2‖ ^ 2 +
          ∑ j : Fin m,
            ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))
              u).toLp 2‖ ^ 2) := by
  classical
  let X := EuclideanSpace ℝ (Fin (n + m))
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let split : X ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using ha.1
  have hsp (ξ : X) : ContDiff ℝ ∞ (fun x ↦ a x ξ) :=
    hs.comp (contDiff_id.prodMk contDiff_const)
  -- The frequency derivative remains jointly smooth before any spatial differentiation.
  let D : X → X → X →L[ℝ] V := fun x ξ ↦ fderiv ℝ (a x) ξ
  have hD : ContDiff ℝ ∞ (Function.uncurry D) := by
    have h : ContDiff ℝ ∞ (Function.uncurry (fun z : X × X ↦ a z.1)) :=
      hs.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact h.fderiv contDiff_snd (by simp)
  have hparam {P W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (f : P → X → W) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : P × X ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ X W).symm : _ →L[ℝ] X [×0]→L[ℝ] W)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : P × X ↦ fun y : X ↦
            iteratedFDeriv ℝ k (f z.1) y)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : P × X ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) W).symm :
          _ →L[ℝ] X [×(k + 1)]→L[ℝ] W)
  apply exists_quantize_vertical_estimate_of_spatial_bounds a
    hs.continuous.stronglyMeasurable hsp K hK hsupp
  intro i
  obtain ⟨C, hC, hb⟩ := ha.2 K (subset_univ K) hK i 1
  have hDbound (ξ x : X) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i (fun y ↦ D y ξ) x‖ ≤ C := by
    have heq : (fun y ↦ iteratedFDeriv ℝ 1 (a y) ξ) =
        (continuousMultilinearCurryFin1 ℝ X V).symm ∘ (fun y ↦ D y ξ) := by
      funext y
      ext v
      simp only [iteratedFDeriv_one_apply, Function.comp_apply,
        continuousMultilinearCurryFin1_symm_apply, D]
    simpa only [symbolDerivative, heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.cast_one, sub_self, Real.rpow_zero, mul_one] using hb x hx ξ
  refine ⟨C * ‖split.symm.toContinuousLinearMap‖, by positivity, ?_⟩
  intro ξ x hx
  let ξ₀ : X := split.symm ((split ξ).1, 0)
  let v : X := split.symm (0, (split ξ).2)
  have hsum : ξ₀ + v = ξ := by
    dsimp only [ξ₀, v]
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, split.symm_apply_apply]
  have hvnorm : ‖v‖ ≤ ‖split.symm.toContinuousLinearMap‖ * ‖(split ξ).2‖ := by
    simpa only [v, ContinuousLinearEquiv.coe_coe, Prod.norm_mk, norm_zero,
      max_eq_right (norm_nonneg _)] using
      split.symm.toContinuousLinearMap.le_opNorm (0, (split ξ).2)
  let g : ℝ → X → V := fun t y ↦ D y (ξ₀ + t • v) v
  have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
    (hD.comp (contDiff_snd.prodMk
      (contDiff_const.add (contDiff_fst.smul contDiff_const)))).clm_apply contDiff_const
  -- Exact integration starts from the assumed zero on the same horizontal covector.
  have hFTC (y : X) : a y ξ = ∫ t : Icc (0 : ℝ) 1, g t y := by
    have hfreq : ContDiff ℝ ∞ (a y) := hs.comp (contDiff_const.prodMk contDiff_id)
    have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ a y (ξ₀ + s • v)) (g t y) t := by
      apply (hfreq.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add ξ₀
    have hi : IntervalIntegrable (fun t : ℝ ↦ g t y) volume 0 1 :=
      (hg.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi
    have hz : a y ξ₀ = 0 := hzero y (split ξ).1
    simp only [one_smul, zero_smul, add_zero, hsum, hz, sub_zero] at h
    have he := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc) (fun t ↦ g t y)
    rw [integral_Icc_eq_integral_Ioc] at he
    rw [intervalIntegral.integral_of_le zero_le_one] at h
    exact h.symm.trans he.symm
  -- Compact integration preserves every spatial jet; only one frequency derivative is bounded.
  have hjet : iteratedFDeriv ℝ i (fun y ↦ a y ξ) x =
      ∫ t : Icc (0 : ℝ) 1, iteratedFDeriv ℝ i (g t) x := by
    have heq : (fun y ↦ a y ξ) = (fun y ↦ ∫ t : Icc (0 : ℝ) 1, g t y) := funext hFTC
    rw [heq]
    apply iteratedFDeriv_integral_of_continuous_jets volume isOpen_univ
      (fun t ↦ (hg.comp (contDiff_const.prodMk contDiff_id)).contDiffOn) _ i (mem_univ x)
    intro k
    exact ((hparam g hg k).continuous.comp
      (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)).continuousOn
  have hgBound (t : Icc (0 : ℝ) 1) : ‖iteratedFDeriv ℝ i (g t) x‖ ≤ ‖v‖ * C := by
    have hd : ContDiff ℝ ∞ (fun y ↦ D y (ξ₀ + (t : ℝ) • v)) :=
      hD.comp (contDiff_id.prodMk contDiff_const)
    exact (norm_iteratedFDeriv_clm_apply_const hd.contDiffAt (by simp)).trans
      (mul_le_mul_of_nonneg_left (hDbound _ x hx) (norm_nonneg v))
  rw [hjet]
  have hint : ‖∫ t : Icc (0 : ℝ) 1, iteratedFDeriv ℝ i (g t) x‖ ≤ ‖v‖ * C := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := volume) (Filter.Eventually.of_forall hgBound)
  calc
    _ ≤ ‖v‖ * C := hint
    _ ≤ (‖split.symm.toContinuousLinearMap‖ * ‖(split ξ).2‖) * C :=
      mul_le_mul_of_nonneg_right hvnorm hC
    _ ≤ (C * ‖split.symm.toContinuousLinearMap‖) * (1 + ‖(split ξ).2‖) := by
      nlinarith [norm_nonneg split.symm.toContinuousLinearMap]

end AtiyahSinger
