/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzDirectionalParameter

/-!
# Smooth finite-dimensional parameters through a Schwartz operator

A jointly continuous Schwartz family of all coordinate derivatives remains
smooth after a continuous map to a Banach space. Directional derivatives are
the actual finite coordinate sums, and the derivative field is a bounded
linear map with that exact sum. No weak-to-strong smoothness assumption or
norm on Schwartz space is introduced.

The coordinate derivative tower is the local input for parameter-dependent
operator lifts in SG III.13.6. Its construction from the specified local
section and its mixed jets remains a separate application.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {n : ℕ}

/-- All continuous coordinate Schwartz derivatives give a smooth Banach-valued image. -/
theorem contDiff_schwartzMap_of_coordinate_derivatives
    (F : List (Fin n) → (Fin n → ℝ) → 𝓢(E, ℂ))
    (hF : ∀ a : List (Fin n), Continuous (F a))
    (hderiv : ∀ (a : List (Fin n)) (x v : Fin n → ℝ) (t : ℝ) (y : E),
      HasDerivAt (fun u ↦ F a (x + u • v) y)
        (∑ i : Fin n, v i • F (i :: a) (x + t • v) y) t)
    (L : 𝓢(E, ℂ) →L[ℂ] V) : ContDiff ℝ ∞ (fun x ↦ L (F [] x)) := by
  let d (a : List (Fin n)) (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] V :=
    ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (L (F (i :: a) x))
  have hd (a : List (Fin n)) : Continuous (d a) := by
    apply continuous_finsetSum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) V
      (ContinuousLinearMap.proj i)).continuous.comp (L.continuous.comp (hF (i :: a)))
  have hD (a : List (Fin n)) (x : Fin n → ℝ) :
      HasFDerivAt (fun z ↦ L (F a z)) (d a x) x := by
    let G (z v : Fin n → ℝ) : 𝓢(E, ℂ) := ∑ i : Fin n, v i • F (i :: a) z
    apply hasFDerivAt_schwartzMap (F a) G ?_ ?_ L (d a) (hd a) ?_ x
    · apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp continuous_snd).smul
        ((hF (i :: a)).comp continuous_fst)
    · intro z v t y
      simpa only [G, sum_apply, smul_apply] using hderiv a z v t y
    · intro z v
      change (L.restrictScalars ℝ) (∑ i : Fin n, v i • F (i :: a) z) = d a z v
      rw [map_sum]
      simp only [map_smul, d, sum_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.coe_restrictScalars']
  -- Each coefficient of the derivative is the image of the next original coordinate derivative.
  have hfinite (k : ℕ) : ∀ a : List (Fin n), ContDiff ℝ k (fun x ↦ L (F a x)) := by
    induction k with
    | zero =>
      intro a
      exact contDiff_zero.mpr (L.continuous.comp (hF a))
    | succ k ih =>
      intro a
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 from rfl, contDiff_succ_iff_fderiv]
      refine ⟨fun x ↦ (hD a x).differentiableAt, by simp, ?_⟩
      have heq : fderiv ℝ (fun x ↦ L (F a x)) = d a := funext fun x ↦ (hD a x).fderiv
      rw [heq]
      apply ContDiff.sum
      intro i _
      exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) V
        (ContinuousLinearMap.proj i)).contDiff.comp (ih (i :: a))
  exact contDiff_infty.mpr (fun k ↦ hfinite k [])

end AtiyahSinger
