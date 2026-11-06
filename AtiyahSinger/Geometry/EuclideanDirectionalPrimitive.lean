/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanPoincareLemma

/-!
# Directional integration of a compactly supported closed Euclidean form

Public module ID: M1217.

Integration from a hyperplane below the original support produces a smooth
primitive with an explicit one-coordinate integral. The integration endpoint
depending on the base point lies below the support, where the form vanishes
on a full neighborhood. This is the directional homotopy used in compact-support
de Rham induction. Its primitive need not have compact support: the positive
direction tail is the remaining lower-dimensional obstruction.

Source: the compact-support de Rham proof by integration along one coordinate,
as in Bott--Tu, Chapter I.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
-- Retain the full integral homotopy and its support control in one mathematical proof.
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A closed compactly supported form has the smooth primitive given by integration
in a specified nonzero coordinate direction from a hyperplane below its support. -/
theorem exists_smooth_euclideanDirectionalPrimitive (p : ℕ)
    (e : EuclideanSpace ℝ (Fin n)) (l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hle : l e = 1)
    (α : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ)
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α)
    (hclosed : ∀ x, extDeriv α x = 0) :
    ∃ R : ℝ, 0 < R ∧ (∀ x, α x ≠ 0 → |l x| < R) ∧
      ∃ η : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ,
        ContDiff ℝ ∞ η ∧ (∀ x, extDeriv η x = α x) ∧
        (∀ x, η x = ∫ t in (0 : ℝ)..R + l x, (α (x - t • e)).curryLeft e) ∧
        (∀ x, l x ≤ -R → η x = 0) ∧
        (∀ (x : EuclideanSpace ℝ (Fin n)) (v : Fin p → EuclideanSpace ℝ (Fin n))
          (i : Fin p), v i = e → η x v = 0) ∧
        ∀ x, R ≤ l x → η x =
          ∫ t : ℝ, (α (x - l x • e + t • e)).curryLeft e := by
  let V := EuclideanSpace ℝ (Fin n)
  let W := V [⋀^Fin p]→L[ℝ] ℂ
  let Z := V [⋀^Fin (p + 1)]→L[ℝ] ℂ
  let B : Z →L[ℝ] W := (ContinuousLinearMap.apply ℝ W e).comp
    ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap
  let F (T t : ℝ) (x : V) : W := T • B (α (x - (t * T) • e))
  let H (T : ℝ) (x : V) : W := ∫ t : unitInterval, F T t x
  -- Normalizing every finite segment to the compact unit interval keeps both variables smooth.
  have hF : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × V) ↦ F z.2.1 z.1 z.2.2) := by
    exact contDiff_snd.fst.smul (B.contDiff.comp (hα.comp
      (contDiff_snd.snd.sub ((contDiff_fst.mul contDiff_snd.fst).smul contDiff_const))))
  have hH : ContDiff ℝ ∞ (Function.uncurry H) := by
    have hparam : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, ℝ × V)) 𝓘(ℝ, W) ∞
        (fun z : unitInterval × (ℝ × V) ↦ F z.2.1 z.1 z.2.2) :=
      hF.contMDiff.comp
        ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space contMDiff_snd)
    exact contDiffOn_univ.mp (contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
      (volume : Measure unitInterval) isOpen_univ hparam.contMDiffOn)
  have hunit (g : ℝ → W) : (∫ t : unitInterval, g t) = ∫ t in (0 : ℝ)..1, g t := by
    have h := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc) g
    rw [integral_Icc_eq_integral_Ioc] at h
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact h
  have hHinterval (T : ℝ) (x : V) :
      H T x = ∫ t in (0 : ℝ)..T, B (α (x - t • e)) := by
    change (∫ t : unitInterval, T • B (α (x - ((t : ℝ) * T) • e))) = _
    rw [integral_smul, hunit (fun t : ℝ ↦ B (α (x - (t * T) • e)))]
    simpa only [zero_mul, one_mul] using
      (intervalIntegral.smul_integral_comp_mul_right
        (fun t : ℝ ↦ B (α (x - t • e))) (a := 0) (b := 1) T)
  -- The constant-direction Cartan identity uses precisely the integer signs in extDeriv.
  have hinsert (L : V →L[ℝ] Z) :
      ContinuousAlternatingMap.alternatizeUncurryFin (B.comp L) +
        (ContinuousAlternatingMap.alternatizeUncurryFin L).curryLeft e = L e := by
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    change (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) •
      L (v i) (Fin.cons e (i.removeNth v))) +
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        L ((Fin.cons e v : Fin (p + 2) → V) i)
          (i.removeNth (Fin.cons e v : Fin (p + 2) → V))) = L e v
    rw [Fin.sum_univ_succ (f := fun i : Fin (p + 2) ↦ (-1 : ℤ) ^ (i : ℕ) •
      L ((Fin.cons e v : Fin (p + 2) → V) i)
        (i.removeNth (Fin.cons e v : Fin (p + 2) → V)))]
    have hremove (i : Fin (p + 1)) :
        i.succ.removeNth (Fin.cons e v : Fin (p + 2) → V) =
          (Fin.cons e (i.removeNth v) : Fin (p + 1) → V) :=
      Fin.cons_comp_succ_succAbove e v i
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero,
      Fin.tail_cons, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one,
      neg_smul, hremove, Finset.sum_neg_distrib]
    abel
  have hstatic (T : ℝ) (x : V) :
      extDeriv (H T) x = α x - α (x - T • e) := by
    let D (t : ℝ) (x : V) : V →L[ℝ] W := fderiv ℝ (F T t) x
    have hFT : ContDiff ℝ ∞ (fun z : ℝ × V ↦ F T z.1 z.2) :=
      (B.contDiff.comp (hα.comp
        (contDiff_snd.sub ((contDiff_fst.mul contDiff_const).smul contDiff_const)))).const_smul T
    have hdiffF (t : ℝ) (y : V) :
        D t y = T • B.comp (fderiv ℝ α (y - (t * T) • e)) := by
      have hp : HasFDerivAt (fun z : V ↦ z - (t * T) • e)
          (ContinuousLinearMap.id ℝ V) y := (hasFDerivAt_id y).sub_const _
      have h := (B.hasFDerivAt.comp y
        ((hα.differentiable (by simp) _).hasFDerivAt.comp y hp)).const_smul T
      change fderiv ℝ (T • B ∘ α ∘ fun z ↦ z - (t * T) • e) y = _
      rw [h.fderiv]
      simp
    have hD : ContDiff ℝ ∞ (fun z : ℝ × V ↦ D z.1 z.2) := by
      simp_rw [hdiffF]
      exact (contDiff_const.clm_comp ((hα.fderiv_right (by simp)).comp
        (contDiff_snd.sub ((contDiff_fst.mul contDiff_const).smul contDiff_const)))).const_smul T
    have hextF (t : ℝ) :
        extDeriv (F T t) x = T • fderiv ℝ α (x - (t * T) • e) e := by
      change ContinuousAlternatingMap.alternatizeUncurryFin (D t x) = _
      rw [hdiffF, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
      have h := hinsert (fderiv ℝ α (x - (t * T) • e))
      rw [show ContinuousAlternatingMap.alternatizeUncurryFin
          (fderiv ℝ α (x - (t * T) • e)) = 0 from hclosed _,
        ContinuousAlternatingMap.curryLeft_zero, zero_apply, add_zero] at h
      rw [h]
    -- A compact interval times a small spatial ball bounds the original differentiated integrand.
    let includeInterval (z : unitInterval × V) : ℝ × V := (z.1, z.2)
    have hinclude : Continuous includeInterval :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hFc : Continuous (fun z : unitInterval × V ↦ F T z.1 z.2) :=
      Continuous.comp (f := includeInterval)
        (g := fun z : ℝ × V ↦ F T z.1 z.2) hFT.continuous hinclude
    have hDc : Continuous (fun z : unitInterval × V ↦ D z.1 z.2) :=
      Continuous.comp (f := includeInterval)
        (g := fun z : ℝ × V ↦ D z.1 z.2) hD.continuous hinclude
    have hFi (y : V) : Integrable (fun t : unitInterval ↦ F T t y) :=
      (hFc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hDi (y : V) : Integrable (fun t : unitInterval ↦ D t y) :=
      (hDc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    obtain ⟨K, hK⟩ := (isCompact_univ.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
      hDc.continuousOn
    have hdH : HasFDerivAt (H T) (∫ t : unitInterval, D t x) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun y t ↦ D t y) (bound := fun _ : unitInterval ↦ K)
        (Metric.closedBall_mem_nhds x zero_lt_one)
      · exact Eventually.of_forall fun y ↦ (hFi y).1
      · exact hFi x
      · exact (hDi x).1
      · exact Eventually.of_forall fun t y hy ↦ hK (t, y) ⟨mem_univ t, hy⟩
      · exact integrable_const K
      · exact Eventually.of_forall fun t y _ ↦
          ((hFT.comp (contDiff_const.prodMk contDiff_id)).differentiable
            (by simp) y).hasFDerivAt
    have hcomm := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ).integral_comp_comm
      (hDi x)
    change (∫ t : unitInterval, extDeriv (F T t) x) =
      ContinuousAlternatingMap.alternatizeUncurryFin (∫ t : unitInterval, D t x) at hcomm
    change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (H T) x) = _
    rw [hdH.fderiv, ← hcomm]
    -- The integrand is the derivative of the same translated form with reversed sign.
    have hpath (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x - (s * T) • e) (-T • e) t := by
      have h := (hasDerivAt_const t x).sub
        (((hasDerivAt_id t).mul_const T).smul_const e)
      convert! h using 1
      simp
    have hradial (t : ℝ) : HasDerivAt (fun s : ℝ ↦ -α (x - (s * T) • e))
        (extDeriv (F T t) x) t := by
      have h := ((hα.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hpath t)).neg
      convert h using 1
      · rfl
      · rw [hextF]
        simp
    have hDs : Continuous (fun t : ℝ ↦ D t x) :=
      Continuous.comp (f := fun t : ℝ ↦ (t, x)) (g := fun z : ℝ × V ↦ D z.1 z.2)
        hD.continuous (continuous_id.prodMk continuous_const)
    have hExt : Continuous (fun t : ℝ ↦ extDeriv (F T t) x) :=
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ).continuous.comp hDs
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ uIcc (0 : ℝ) 1) ↦ hradial t) (hExt.intervalIntegrable 0 1)
    have hunitZ : (∫ t : unitInterval, extDeriv (F T t) x) =
        ∫ t in (0 : ℝ)..1, extDeriv (F T t) x := by
      have h := unitInterval.measurePreserving_coe.integral_comp
        (MeasurableEmbedding.subtype_coe measurableSet_Icc) (fun t : ℝ ↦ extDeriv (F T t) x)
      rw [integral_Icc_eq_integral_Ioc] at h
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact h
    rw [hunitZ, hFTC]
    simp [sub_eq_add_neg, add_comm]
  -- Choose an actual hyperplane strictly outside the compact support.
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn l.continuous.continuousOn
  let R := max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound (x : V) (hx : α x ≠ 0) : |l x| < R := by
    have h := hC x (subset_tsupport α hx)
    rw [Real.norm_eq_abs] at h
    dsimp [R]
    linarith [le_max_left C 0]
  have hzero (x : V) (hx : l x ≤ -R) : α x = 0 := by
    by_contra hx0
    have h := hbound x hx0
    linarith [neg_le_abs (l x)]
  let η (x : V) : W := H (R + l x) x
  have hη : ContDiff ℝ ∞ η :=
    hH.comp ((contDiff_const.add l.contDiff).prodMk contDiff_id)
  have hdη (x : V) : extDeriv η x = α x := by
    let T := R + l x + 1
    -- Near x, the variable starting hyperplane can be replaced by one fixed translation.
    have hnear : ∀ᶠ y in 𝓝 x, R + l y < T :=
      (isOpen_lt (continuous_const.add l.continuous) continuous_const).mem_nhds (by
        dsimp [T]
        linarith)
    have heq : η =ᶠ[𝓝 x] H T := by
      filter_upwards [hnear] with y hy
      rw [show η y = H (R + l y) y from rfl, hHinterval, hHinterval]
      have hc : Continuous (fun t : ℝ ↦ B (α (y - t • e))) :=
        B.continuous.comp (hα.continuous.comp (continuous_const.sub
          (continuous_id.smul continuous_const)))
      have hz : (∫ t in R + l y..T, B (α (y - t • e))) = 0 := by
        calc
          (∫ t in R + l y..T, B (α (y - t • e))) = ∫ _ in R + l y..T, (0 : W) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le hy.le] at ht
            have htzero : α (y - t • e) = 0 := by
              apply hzero
              rw [map_sub, map_smul, hle, smul_eq_mul, mul_one]
              linarith [ht.1]
            change B (α (y - t • e)) = 0
            rw [htzero, map_zero]
          _ = 0 := intervalIntegral.integral_zero
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hc.intervalIntegrable 0 (R + l y)) (hc.intervalIntegrable (R + l y) T)
      rwa [hz, add_zero] at hadd
    have hend : α (x - T • e) = 0 := by
      apply hzero
      rw [map_sub, map_smul, hle, smul_eq_mul, mul_one]
      dsimp [T]
      linarith
    change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) = _
    rw [heq.fderiv_eq]
    exact (hstatic T x).trans (by rw [hend, sub_zero])
  have hηinterval (x : V) :
      η x = ∫ t in (0 : ℝ)..R + l x, B (α (x - t • e)) := hHinterval (R + l x) x
  have hηzero (x : V) (hx : l x ≤ -R) : η x = 0 := by
    rw [hηinterval]
    calc
      (∫ t in (0 : ℝ)..R + l x, B (α (x - t • e))) =
          ∫ _ in (0 : ℝ)..R + l x, (0 : W) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge (show R + l x ≤ 0 by linarith)] at ht
        have hz : α (x - t • e) = 0 := by
          apply hzero
          rw [map_sub, map_smul, hle, smul_eq_mul, mul_one]
          linarith [ht.1]
        change B (α (x - t • e)) = 0
        rw [hz, map_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hhorizontal (x : V) (v : Fin p → V) (i : Fin p) (hi : v i = e) : η x v = 0 := by
    -- Inserting the integration direction twice annihilates the original alternating tensor.
    let ev : W →L[ℝ] ℂ := ContinuousAlternatingMap.apply ℝ V ℂ v
    have hc : Continuous (fun t : ℝ ↦ B (α (x - t • e))) :=
      B.continuous.comp (hα.continuous.comp (continuous_const.sub
        (continuous_id.smul continuous_const)))
    have heval := ev.intervalIntegral_comp_comm (μ := volume)
      (hc.intervalIntegrable 0 (R + l x))
    change (∫ t in (0 : ℝ)..R + l x, B (α (x - t • e)) v) =
      (∫ t in (0 : ℝ)..R + l x, B (α (x - t • e))) v at heval
    rw [hηinterval, ← heval]
    calc
      (∫ t in (0 : ℝ)..R + l x, B (α (x - t • e)) v) =
          ∫ _ in (0 : ℝ)..R + l x, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _
        change α (x - t • e) (Fin.cons e v) = 0
        exact (α (x - t • e)).map_eq_zero_of_eq (Fin.cons e v)
          (by simpa only [Fin.cons_zero, Fin.cons_succ] using hi.symm)
          (Fin.succ_ne_zero i).symm
      _ = 0 := intervalIntegral.integral_zero
  have htail (x : V) (hx : R ≤ l x) :
      η x = ∫ t : ℝ, B (α (x - l x • e + t • e)) := by
    -- Above the support, the finite segment includes the entire one-coordinate integral.
    let g (t : ℝ) : W := B (α (x - l x • e + t • e))
    have hchange : (∫ t in (0 : ℝ)..R + l x, B (α (x - t • e))) =
        ∫ t in -R..l x, g t := by
      have hvalue (t : ℝ) : B (α (x - t • e)) = g (l x - 1 * t) := by
        apply congrArg (fun y ↦ B (α y))
        module
      calc
        (∫ t in (0 : ℝ)..R + l x, B (α (x - t • e))) =
            ∫ t in (0 : ℝ)..R + l x, g (l x - 1 * t) :=
          intervalIntegral.integral_congr (fun t _ ↦ hvalue t)
        _ = ∫ t in -R..l x, g t := by
          have h := intervalIntegral.integral_comp_sub_mul g (a := 0) (b := R + l x)
            (one_ne_zero : (1 : ℝ) ≠ 0) (l x)
          simpa only [inv_one, one_smul, one_mul, sub_zero,
            show l x - (R + l x) = -R by ring] using h
    rw [hηinterval, hchange, intervalIntegral.integral_of_le (by linarith : -R ≤ l x)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hcoord : l (x - l x • e + t • e) = t := by
      simp [map_sub, map_add, map_smul, hle]
    have hz : α (x - l x • e + t • e) = 0 := by
      by_contra hne
      have h := hbound _ hne
      rw [hcoord] at h
      exact ht ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le.trans hx⟩
    change B (α (x - l x • e + t • e)) = 0
    rw [hz, map_zero]
  exact ⟨R, hR, hbound, η, hη, hdη, hηinterval, hηzero, hhorizontal, htail⟩

end AtiyahSinger
