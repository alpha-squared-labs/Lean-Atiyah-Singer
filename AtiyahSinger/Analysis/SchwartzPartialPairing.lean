/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzCompactParameter
public import AtiyahSinger.Analysis.SchwartzSliceContinuity

import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Partial distribution pairing on a common compact support

Public module ID: M0949.

Apply a continuous Schwartz functional in the second variable of an actual
joint Schwartz function. On a common compact product support, the result is
a Schwartz function in the first variable and depends continuously on the
original function. The parameter space is arbitrary. Coordinate derivatives
pass through the same functional, and finite derivative fields recover the
full Schwartz topology without imposing a norm on that space.

This is the local analytic input for commuting the original horizontal and
vertical PDOs. The later application must retain their original cutoffs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set LineDeriv
open scoped ContDiff SchwartzMap

variable {n : ℕ} {Y P : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [TopologicalSpace P]

local notation "X" => Fin n → ℝ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Partial pairing gives a continuous Schwartz family with its original pointwise values. -/
theorem exists_continuous_schwartzPartialPairing
    (F : P → 𝓢(X × Y, ℂ)) (hF : Continuous F)
    (K : Set X) (H : Set Y) (hK : IsCompact K) (hH : IsCompact H)
    (hsupport : ∀ p, tsupport (F p) ⊆ K ×ˢ H)
    (L : 𝓢(Y, ℂ) →L[ℂ] ℂ) :
    ∃ G : P → 𝓢(X, ℂ), Continuous G ∧
      (∀ p x, G p x = L (schwartzSliceCLM x (F p))) ∧
      ∀ p, tsupport (G p) ⊆ K := by
  classical
  -- Differentiate the actual joint input only in first-variable coordinate directions.
  let D : List (Fin n) → P → 𝓢(X × Y, ℂ) :=
    List.rec F (fun i _ f p ↦
      lineDerivOpCLM ℂ 𝓢(X × Y, ℂ) ((Pi.single i (1 : ℝ) : X), (0 : Y)) (f p))
  have hD (a : List (Fin n)) : Continuous (D a) := by
    induction a with
    | nil => exact hF
    | cons i a ih => exact (lineDerivOpCLM ℂ 𝓢(X × Y, ℂ) _).continuous.comp ih
  have hDsupp (a : List (Fin n)) (p : P) : tsupport (D a p) ⊆ K ×ˢ H := by
    induction a with
    | nil => exact hsupport p
    | cons i a ih => exact (tsupport_fderiv_apply_subset ℝ (Pi.single i 1, 0)).trans ih
  let U (a : List (Fin n)) (p : P) (x : X) : 𝓢(Y, ℂ) :=
    schwartzSliceCLM x (D a p)
  have hU (a : List (Fin n)) : Continuous (fun p : P × X ↦ U a p.1 p.2) :=
    continuous_schwartzSlice_of_common_compact_support (D a) (hD a) H hH
      (fun p z hz ↦ (hDsupp a p hz).2)
  have hline (a : List (Fin n)) (p : P) (x v : X) (t : ℝ) (y : Y) :
      HasDerivAt (fun u ↦ U a p (x + u • v) y)
        (∑ i : Fin n, v i • U (i :: a) p (x + t • v) y) t := by
    have hpath : HasDerivAt (fun u : ℝ ↦ (x + u • v, y)) (v, 0) t := by
      simpa only [one_smul, id_eq] using
        HasDerivAt.prodMk (((hasDerivAt_id t).smul_const v).const_add x)
          (hasDerivAt_const t y)
    have h := ((D a p).hasFDerivAt (x + t • v, y)).comp_hasDerivAt t hpath
    have hv : (v, (0 : Y)) = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ), (0 : Y)) := by
      apply Prod.ext
      · change v = (ContinuousLinearMap.fst ℝ X Y) _
        rw [map_sum]
        ext i
        simp [Pi.single_apply]
      · change (0 : Y) = (ContinuousLinearMap.snd ℝ X Y) _
        rw [map_sum]
        simp
    have hderiv : fderiv ℝ (D a p) (x + t • v, y) (v, 0) =
        ∑ i : Fin n, v i • U (i :: a) p (x + t • v) y := by
      rw [hv, map_sum]
      simp only [map_smul]
      rfl
    rw [hderiv] at h
    exact h
  let g (a : List (Fin n)) (p : P) (x : X) : ℂ := L (U a p x)
  have hg (a : List (Fin n)) : Continuous (fun p : P × X ↦ g a p.1 p.2) :=
    L.continuous.comp (hU a)
  let B (i : Fin n) : ℂ →L[ℝ] X →L[ℝ] ℂ :=
    ContinuousLinearMap.smulRightL ℝ X ℂ (ContinuousLinearMap.proj i)
  let d (a : List (Fin n)) (p : P) (x : X) : X →L[ℝ] ℂ :=
    ∑ i : Fin n, B i (g (i :: a) p x)
  have hd (a : List (Fin n)) : Continuous (fun p : P × X ↦ d a p.1 p.2) := by
    apply continuous_finsetSum
    intro i _
    exact (B i).continuous.comp (hg (i :: a))
  -- The continuous finite derivative field passes the same functional through each derivative.
  have hderiv (a : List (Fin n)) (p : P) (x : X) :
      HasFDerivAt (g a p) (d a p x) x := by
    let J (z v : X) : 𝓢(Y, ℂ) := ∑ i : Fin n, v i • U (i :: a) p z
    have hp : Continuous (fun z : X ↦ (p, z)) := continuous_const.prodMk continuous_id
    have hdp := (hd a).comp hp
    change Continuous (d a p) at hdp
    change HasFDerivAt (fun z ↦ L (U a p z)) (d a p x) x
    apply hasFDerivAt_schwartzMap (U a p) J ?_ ?_ L (d a p) hdp ?_ x
    · apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp continuous_snd).smul
        ((hU (i :: a)).comp (show Continuous (fun z : X × X ↦ (p, z.1)) from
          continuous_const.prodMk continuous_fst))
    · intro z v t y
      simpa only [J, sum_apply, smul_apply] using hline a p z v t y
    · intro z v
      change (L.restrictScalars ℝ) (∑ i : Fin n, v i • U (i :: a) p z) = d a p z v
      rw [map_sum]
      simp only [map_smul, d, B, sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.coe_restrictScalars']
      rfl
  have hsmooth (a : List (Fin n)) (p : P) : ContDiff ℝ ∞ (g a p) := by
    have hfinite (j : ℕ) : ∀ a : List (Fin n), ContDiff ℝ j (g a p) := by
      induction j with
      | zero =>
        intro a
        exact contDiff_zero.mpr ((hg a).comp
          (show Continuous (fun z : X ↦ (p, z)) from continuous_const.prodMk continuous_id))
      | succ j ih =>
        intro a
        rw [show ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 from rfl,
          contDiff_succ_iff_fderiv]
        refine ⟨fun x ↦ (hderiv a p x).differentiableAt, by simp, ?_⟩
        rw [show fderiv ℝ (g a p) = d a p from funext (fun x ↦ (hderiv a p x).fderiv)]
        apply ContDiff.sum
        intro i _
        exact (B i).contDiff.comp (ih (i :: a))
    exact contDiff_infty.mpr (fun j ↦ hfinite j a)
  -- Every spatial jet is a finite continuous combination of the next coordinate images.
  have hjets (j : ℕ) : ∀ a : List (Fin n),
      Continuous (fun p : P × X ↦ iteratedFDeriv ℝ j (g a p.1) p.2) := by
    induction j with
    | zero =>
      intro a
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact (continuousMultilinearCurryFin0 ℝ X ℂ).symm.continuous.comp (hg a)
    | succ j ih =>
      intro a
      let C := (continuousMultilinearCurryRightEquiv' ℝ j X ℂ).symm
      have hcont : Continuous (fun p : P × X ↦ C (∑ i : Fin n,
          (B i).compContinuousMultilinearMap (iteratedFDeriv ℝ j (g (i :: a) p.1) p.2))) := by
        apply C.continuous.comp
        apply continuous_finsetSum
        intro i _
        exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
          (fun _ : Fin j ↦ X) ℂ (X →L[ℝ] ℂ) (B i)).continuous.comp (ih (i :: a))
      convert hcont using 1
      funext p
      rw [iteratedFDeriv_succ_eq_comp_right]
      change C (iteratedFDeriv ℝ j (fderiv ℝ (g a p.1)) p.2) = _
      rw [show fderiv ℝ (g a p.1) = d a p.1 from
        funext (fun x ↦ (hderiv a p.1 x).fderiv)]
      congr 1
      rw [show d a p.1 = fun x ↦ ∑ i : Fin n, B i (g (i :: a) p.1 x) from rfl]
      have hsm (i : Fin n) : ContDiffAt ℝ j (fun x ↦ B i (g (i :: a) p.1 x)) p.2 :=
        (((B i).contDiff.comp (hsmooth (i :: a) p.1)).of_le (by simp)).contDiffAt
      rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ hsm i)]
      apply Finset.sum_congr rfl
      intro i _
      exact (B i).iteratedFDeriv_comp_left (hsmooth (i :: a) p.1).contDiffAt (by simp)
  have hgsupport (p : P) : tsupport (g [] p) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hz : U [] p x = 0 := by
      ext y
      change F p (x, y) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hxy
      exact hxK (hsupport p hxy).1
    exact hx (by change L (U [] p x) = 0; rw [hz, map_zero])
  let G (p : P) : 𝓢(X, ℂ) := HasCompactSupport.toSchwartzMap
    (hK.of_isClosed_subset (isClosed_tsupport _) (hgsupport p)) (hsmooth [] p)
  refine ⟨G, ?_, fun _ _ ↦ rfl, hgsupport⟩
  exact continuous_schwartzMap_of_common_compact_support G K hK hgsupport (fun j ↦ hjets j [])

end AtiyahSinger
