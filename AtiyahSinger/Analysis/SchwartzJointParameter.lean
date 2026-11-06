/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzCompactParameter

import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Joint smoothness after applying a Schwartz operator

Public module ID: M0943.

A continuous operator on Schwartz space preserves joint smoothness of a
parameterized compactly supported input. Parameter derivatives pass through
the same operator; output derivatives compose that operator with the actual
Schwartz differentiation maps. Continuous partial derivative fields give the
full derivative on the product, and induction supplies every order.

This is the local smoothness input for the associated-bundle operator lift.
Bundle transition covariance and the global operator construction are separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set LineDeriv
open scoped ContDiff SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A Schwartz coordinate derivative tower stays jointly smooth after a continuous operator. -/
theorem contDiff_schwartzOperator_of_coordinate_derivatives
    (F : List (Fin n) → (Fin n → ℝ) → 𝓢(E, ℂ))
    (hF : ∀ a : List (Fin n), Continuous (F a))
    (hderiv : ∀ (a : List (Fin n)) (x v : Fin n → ℝ) (t : ℝ) (y : E),
      HasDerivAt (fun u ↦ F a (x + u • v) y)
        (∑ i : Fin n, v i • F (i :: a) (x + t • v) y) t)
    (T : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ T (F [] p.1) p.2) := by
  classical
  let B : 𝓢((Fin m → ℝ), ℂ) →L[ℂ] BoundedContinuousFunction (Fin m → ℝ) ℂ :=
    SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin m → ℝ) ℂ
  let derivOp (j : Fin m) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)) :
      𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ) :=
    (lineDerivOpCLM ℂ 𝓢((Fin m → ℝ), ℂ)
      (Pi.single j (1 : ℝ) : Fin m → ℝ)).comp A
  have hc (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)) :
      Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ A (F a p.1) p.2) :=
    continuous_eval.comp
      (((B.continuous.comp (A.continuous.comp (hF a))).comp continuous_fst).prodMk
        continuous_snd)
  let d₁ (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ))
      (p : (Fin n → ℝ) × (Fin m → ℝ)) : (Fin n → ℝ) →L[ℝ] ℂ :=
    ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (A (F (i :: a) p.1) p.2)
  let d₂ (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ))
      (p : (Fin n → ℝ) × (Fin m → ℝ)) : (Fin m → ℝ) →L[ℝ] ℂ :=
    ∑ j : Fin m, (ContinuousLinearMap.proj j).smulRight (derivOp j A (F a p.1) p.2)
  have hc₁ (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)) :
      Continuous (d₁ a A) := by
    apply continuous_finsetSum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℂ
      (ContinuousLinearMap.proj i)).continuous.comp (hc (i :: a) A)
  have hc₂ (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)) :
      Continuous (d₂ a A) := by
    apply continuous_finsetSum
    intro j _
    exact (ContinuousLinearMap.smulRightL ℝ (Fin m → ℝ) ℂ
      (ContinuousLinearMap.proj j)).continuous.comp (hc a (derivOp j A))
  -- The first partial derivative passes the actual coordinate sum through A and evaluation.
  have h₁ (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ))
      (x : Fin n → ℝ) (y : Fin m → ℝ) :
      HasFDerivAt (fun z ↦ A (F a z) y) (d₁ a A (x, y)) x := by
    let L := ((BoundedContinuousFunction.evalCLM ℂ y).comp B).comp A
    let G (z v : Fin n → ℝ) : 𝓢(E, ℂ) := ∑ i : Fin n, v i • F (i :: a) z
    apply hasFDerivAt_schwartzMap (F a) G ?_ ?_ L (fun z ↦ d₁ a A (z, y))
      ((hc₁ a A).comp (continuous_id.prodMk continuous_const)) ?_ x
    · apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp continuous_snd).smul
        ((hF (i :: a)).comp continuous_fst)
    · intro z v t w
      simpa only [G, sum_apply, smul_apply] using hderiv a z v t w
    · intro z v
      change (L.restrictScalars ℝ) (∑ i : Fin n, v i • F (i :: a) z) = d₁ a A (z, y) v
      rw [map_sum]
      simp only [map_smul, d₁, sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_restrictScalars']
      rfl
  -- The second partial derivative is the actual derivative of the output Schwartz function.
  have h₂ (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ))
      (x : Fin n → ℝ) (y : Fin m → ℝ) :
      HasFDerivAt (fun z ↦ A (F a x) z) (d₂ a A (x, y)) y := by
    have heq : fderiv ℝ (A (F a x)) y = d₂ a A (x, y) := by
      ext v
      have hv : v = ∑ j : Fin m, v j • Pi.single j (1 : ℝ) := by
        ext j
        simp [Pi.single_apply]
      change fderiv ℝ (A (F a x)) y v =
        (∑ j : Fin m, (ContinuousLinearMap.proj j).smulRight
          (derivOp j A (F a x) y)) v
      rw [hv, map_sum]
      simp only [map_smul, sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.proj_apply]
      rw [← hv]
      rfl
    rw [← heq]
    exact (A (F a x)).hasFDerivAt y
  have htotal (a : List (Fin n)) (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ))
      (p : (Fin n → ℝ) × (Fin m → ℝ)) :
      HasFDerivAt (fun z : (Fin n → ℝ) × (Fin m → ℝ) ↦ A (F a z.1) z.2)
        ((d₁ a A p).coprod (d₂ a A p)) p :=
    (hasStrictFDerivAt_uncurry_coprod
      (u := p) (f := fun x y ↦ A (F a x) y)
      (f₁ := fun x y ↦ d₁ a A (x, y)) (f₂ := fun x y ↦ d₂ a A (x, y))
      (Filter.Eventually.of_forall (fun z ↦ h₁ a A z.1 z.2))
      (Filter.Eventually.of_forall (fun z ↦ h₂ a A z.1 z.2))
      (hc₁ a A).continuousAt (hc₂ a A).continuousAt).hasFDerivAt
  -- Every derivative coefficient has the same form, with a next input jet or output derivative.
  have hfinite (k : ℕ) : ∀ (a : List (Fin n))
      (A : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)),
      ContDiff ℝ k (fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ A (F a p.1) p.2) := by
    induction k with
    | zero =>
      intro a A
      exact contDiff_zero.mpr (hc a A)
    | succ k ih =>
      intro a A
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 from rfl, contDiff_succ_iff_fderiv]
      refine ⟨fun p ↦ (htotal a A p).differentiableAt, by simp, ?_⟩
      have heq : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ A (F a p.1) p.2) =
          (fun p ↦ (d₁ a A p).coprod (d₂ a A p)) :=
        funext fun p ↦ (htotal a A p).fderiv
      rw [heq]
      have hd₁ : ContDiff ℝ k (d₁ a A) := by
        apply ContDiff.sum
        intro i _
        exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℂ
          (ContinuousLinearMap.proj i)).contDiff.comp (ih (i :: a) A)
      have hd₂ : ContDiff ℝ k (d₂ a A) := by
        apply ContDiff.sum
        intro j _
        exact (ContinuousLinearMap.smulRightL ℝ (Fin m → ℝ) ℂ
          (ContinuousLinearMap.proj j)).contDiff.comp (ih a (derivOp j A))
      change ContDiff ℝ k (fun p ↦
        (d₁ a A p).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin m → ℝ)) +
        (d₂ a A p).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin m → ℝ)))
      exact (hd₁.clm_comp contDiff_const).add (hd₂.clm_comp contDiff_const)
  exact contDiff_infty.mpr (fun k ↦ hfinite k [] T)

/-- A continuous Schwartz operator preserves joint smoothness for a common compact input support. -/
theorem contDiff_schwartzOperator_of_common_compact_support
    (F : (Fin n → ℝ) → 𝓢(E, ℂ))
    (hF : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × E ↦ F p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupport : ∀ x, tsupport (F x) ⊆ K)
    (T : 𝓢(E, ℂ) →L[ℂ] 𝓢((Fin m → ℝ), ℂ)) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ T (F p.1) p.2) := by
  obtain ⟨G, hbase, _, hG, hderiv⟩ :=
    exists_schwartz_derivative_tower_of_common_compact_support F hF K hK hsupport
  simpa only [hbase] using contDiff_schwartzOperator_of_coordinate_derivatives G hG hderiv T

end AtiyahSinger
