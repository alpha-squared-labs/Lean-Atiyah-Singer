/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Poincaré lemma in every positive degree on Euclidean space

Public module ID: M1221.

The radial integral contracts the actual smooth alternating tensors, using
mathlib's unnormalized exterior derivative. Differentiation under the compact
interval integral and the fundamental theorem of calculus prove exactness of
every closed positive-degree form. This is the Euclidean input to localization
of the original sphere de Rham quotient, with no de Rham comparison theorem.

Source: the standard radial-homotopy proof of the Poincaré lemma, as used in
Bott--Tu, Differential Forms in Algebraic Topology, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

set_option maxHeartbeats 1500000 in
-- Keep the actual alternating tensors, radial derivative and compact integral together.
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every closed smooth positive-degree form on Euclidean space has a smooth primitive. -/
theorem exists_smooth_euclideanFormPrimitive (p : ℕ)
    (α : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ)
    (hα : ContDiff ℝ ∞ α) (hclosed : ∀ x, extDeriv α x = 0) :
    ∃ η : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ,
      ContDiff ℝ ∞ η ∧ ∀ x, extDeriv η x = α x := by
  let V := EuclideanSpace ℝ (Fin n)
  let W := V [⋀^Fin p]→L[ℝ] ℂ
  let Z := V [⋀^Fin (p + 1)]→L[ℝ] ℂ
  let C : Z →L[ℝ] (V →L[ℝ] W) := ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap
  let B (x : V) : Z →L[ℝ] W := (ContinuousLinearMap.apply ℝ W x).comp C
  let F (t : ℝ) (x : V) : W := t ^ p • (α (t • x)).curryLeft x
  let D (t : ℝ) (x : V) : V →L[ℝ] W := fderiv ℝ (F t) x
  let η (x : V) : W := ∫ t : unitInterval, F t x
  -- The radial integrand and its spatial derivative are jointly smooth.
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    exact (contDiff_fst.pow p).smul
      ((C.contDiff.comp (hα.comp (contDiff_fst.smul contDiff_snd))).clm_apply contDiff_snd)
  have hD : ContDiff ℝ ∞ (fun z : ℝ × V ↦ D z.1 z.2) := by
    have h : ContDiff ℝ ∞ (fun z : (ℝ × V) × V ↦ F z.1.1 z.2) :=
      hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact h.fderiv contDiff_snd (by simp)
  have hη : ContDiff ℝ ∞ η := by
    have hparam : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, V)) 𝓘(ℝ, W) ∞
        (fun z : unitInterval × V ↦ F z.1 z.2) :=
      hF.contMDiff.comp
        ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space contMDiff_snd)
    exact contDiffOn_univ.mp (contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
      (volume : Measure unitInterval) isOpen_univ hparam.contMDiffOn)
  -- Insertion and alternation cancel all terms except the radial directional derivative.
  have hinsert (x : V) (L : V →L[ℝ] Z) :
      ContinuousAlternatingMap.alternatizeUncurryFin ((B x).comp L) +
        (ContinuousAlternatingMap.alternatizeUncurryFin L).curryLeft x = L x := by
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    change (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) •
      L (v i) (Fin.cons x (i.removeNth v))) +
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        L ((Fin.cons x v : Fin (p + 2) → V) i)
          (i.removeNth (Fin.cons x v : Fin (p + 2) → V))) = L x v
    rw [Fin.sum_univ_succ (f := fun i : Fin (p + 2) ↦ (-1 : ℤ) ^ (i : ℕ) •
      L ((Fin.cons x v : Fin (p + 2) → V) i)
        (i.removeNth (Fin.cons x v : Fin (p + 2) → V)))]
    have hremove (i : Fin (p + 1)) :
        i.succ.removeNth (Fin.cons x v : Fin (p + 2) → V) =
          (Fin.cons x (i.removeNth v) : Fin (p + 1) → V) :=
      Fin.cons_comp_succ_succAbove x v i
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero,
      Fin.tail_cons, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one,
      neg_smul, hremove, Finset.sum_neg_distrib]
    abel
  have hdiffF (t : ℝ) (x : V) :
      D t x = t ^ p • ((α (t • x)).curryLeft + t • (B x).comp (fderiv ℝ α (t • x))) := by
    have hpath : HasFDerivAt (fun y : V ↦ t • y)
        (t • ContinuousLinearMap.id ℝ V) x := (hasFDerivAt_id x).const_smul t
    have h := ((C.hasFDerivAt.comp x
      ((hα.differentiable (by simp) (t • x)).hasFDerivAt.comp x hpath)).clm_apply
        (hasFDerivAt_id x)).const_smul (t ^ p)
    change fderiv ℝ (t ^ p • fun y ↦ ((C ∘ α ∘ fun y ↦ t • y) y) (id y)) x = _
    rw [h.fderiv]
    congr 2
    apply ContinuousLinearMap.ext
    intro v
    simp [B, C, ContinuousLinearMap.comp_apply]
  have hextF (t : ℝ) (x : V) :
      extDeriv (F t) x = t ^ p •
        ((p + 1) • α (t • x) + t • fderiv ℝ α (t • x) x) := by
    change ContinuousAlternatingMap.alternatizeUncurryFin (D t x) = _
    rw [hdiffF, ContinuousAlternatingMap.alternatizeUncurryFin_smul,
      ContinuousAlternatingMap.alternatizeUncurryFin_add,
      ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft,
      ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    have hc := hinsert x (fderiv ℝ α (t • x))
    rw [show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ α (t • x)) = 0
      from hclosed (t • x), ContinuousAlternatingMap.curryLeft_zero,
      zero_apply, add_zero] at hc
    rw [hc]
  -- The compact parameter gives a uniform bound on every small spatial ball.
  have hderivη (x : V) : fderiv ℝ η x = ∫ t : unitInterval, D t x := by
    have hFc : Continuous (fun z : unitInterval × V ↦ F z.1 z.2) :=
      hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
    have hDc : Continuous (fun z : unitInterval × V ↦ D z.1 z.2) :=
      hD.continuous.comp (continuous_subtype_val.prodMap continuous_id)
    have hFi (y : V) : Integrable (fun t : unitInterval ↦ F t y) :=
      (hFc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hDi (y : V) : Integrable (fun t : unitInterval ↦ D t y) :=
      (hDc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    obtain ⟨K, hK⟩ := (isCompact_univ.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
      hDc.continuousOn
    have hd : HasFDerivAt η (∫ t : unitInterval, D t x) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun y t ↦ D t y) (bound := fun _ : unitInterval ↦ K)
        (Metric.closedBall_mem_nhds x zero_lt_one)
      · exact Eventually.of_forall fun y ↦ (hFi y).1
      · exact hFi x
      · exact (hDi x).1
      · exact Eventually.of_forall fun t y hy ↦ hK (t, y) ⟨mem_univ t, hy⟩
      · exact integrable_const K
      · apply Eventually.of_forall
        intro t y _
        exact ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable
          (by simp) y).hasFDerivAt
    exact hd.fderiv
  refine ⟨η, hη, ?_⟩
  intro x
  have hDc : Continuous (fun t : unitInterval ↦ D t x) :=
    hD.continuous.comp (continuous_subtype_val.prodMk continuous_const)
  have hDi : Integrable (fun t : unitInterval ↦ D t x) :=
    hDc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomm := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ).integral_comp_comm hDi
  change (∫ t : unitInterval, extDeriv (F t) x) =
    ContinuousAlternatingMap.alternatizeUncurryFin (∫ t : unitInterval, D t x) at hcomm
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) = α x
  rw [hderivη, ← hcomm]
  -- The integrated spatial derivative is the derivative of t^(p+1) times the same form.
  have hradial (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ s ^ (p + 1) • α (s • x)) (extDeriv (F t) x) t := by
    have hpath : HasDerivAt (fun s : ℝ ↦ s • x) x t :=
      by simpa using (hasDerivAt_id t).smul_const x
    have h := ((hasDerivAt_id t).pow (p + 1)).smul
      ((hα.differentiable (by simp) (t • x)).hasFDerivAt.comp_hasDerivAt t hpath)
    convert h using 1
    · rfl
    · rw [hextF]
      simp only [Function.comp_apply, Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one]
      rw [← Nat.cast_smul_eq_nsmul ℝ (p + 1) (α (t • x))]
      simp only [smul_add, smul_smul, pow_succ]
      module
  have hExt : Continuous (fun t : ℝ ↦ extDeriv (F t) x) :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ).continuous.comp
      (hD.continuous.comp (continuous_id.prodMk continuous_const))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) ↦ hradial t)
    (hExt.intervalIntegrable 0 1)
  have hInterval : (∫ t : unitInterval, extDeriv (F t) x) =
      ∫ t in (0 : ℝ)..1, extDeriv (F t) x := by
    have h := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc) (fun t : ℝ ↦ extDeriv (F t) x)
    rw [integral_Icc_eq_integral_Ioc] at h
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact h
  rw [hInterval, hFTC]
  simp

end AtiyahSinger
