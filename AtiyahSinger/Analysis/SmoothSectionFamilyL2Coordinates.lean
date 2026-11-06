/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothSectionSobolevFamily

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for the original fiber Sobolev-zero coordinates

Public module ID: M0980.

The L² norm of a native section family with values in its original Sobolev-zero
space is exactly the finite sum of its joint coordinate L² norms. The same
native presentation, section values and chart cutoffs occur on both sides.
Only the actual joint Schwartz coordinate identities and family membership
are required; no separated expansion or replacement Hilbert norm is used.

This is the norm-comparison step from compact whole-fiber families to the
actual associated product-chart coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff Topology SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 600000 in

/-- The original fiber H⁰ family norm is the finite sum of its joint coordinate L² norms. -/
theorem norm_sobolevZero_family_sq {m : ℕ}
    (L : SmoothBundlePresentation (n := n) (r := r) E)
    (u : (Fin m → ℝ) → smoothSections (n := n) (r := r) E)
    (hu : MemLp (fun x ↦ L.smoothToSobolev 0 (u x)) 2 (volume : Measure (Fin m → ℝ)))
    (f : Fin L.size → 𝓢((Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
      EuclideanSpace ℂ (Fin r)))
    (hf : ∀ j x y, f j (x, y) = L.localize j (u x) y) :
    letI : Measure.IsAddHaarMeasure
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
      Measure.prod.instIsAddHaarMeasure _ _
    ‖hu.toLp (fun x ↦ L.smoothToSobolev 0 (u x))‖ ^ 2 =
      ∑ j, ‖(f j).toLp 2 ((volume : Measure (Fin m → ℝ)).prod volume)‖ ^ 2 := by
  classical
  let X := Fin m → ℝ
  let Y := EuclideanSpace ℝ (Fin n)
  let W := EuclideanSpace ℂ (Fin r)
  let : Measure.IsAddHaarMeasure ((volume : Measure X).prod (volume : Measure Y)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  -- Work with the exact L² representatives before applying Fubini to the original values.
  have hFamily : ‖hu.toLp (fun x ↦ L.smoothToSobolev 0 (u x))‖ ^ 2 =
      ∫ x : X, ‖L.smoothToSobolev 0 (u x)‖ ^ 2 := by
    let : InnerProductSpace ℝ (L.SobolevSpace 0) :=
      InnerProductSpace.rclikeToReal ℂ (L.SobolevSpace 0)
    let g := hu.toLp (fun x ↦ L.smoothToSobolev 0 (u x))
    calc
      ‖g‖ ^ 2 = inner ℝ g g := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x : X, ‖g x‖ ^ 2 := by
        simp only [L2.inner_def, real_inner_self_eq_norm_sq]
        rfl
      _ = ∫ x : X, ‖L.smoothToSobolev 0 (u x)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hu.coeFn_toLp] with x hx
        exact congrArg (fun v ↦ ‖v‖ ^ 2) hx
  have hcoord (v : 𝓢(Y, W)) :
      ‖schwartzSobolevCoordinate 0 v‖ ^ 2 = ∫ y, ‖v y‖ ^ 2 := by
    have hz : schwartzSobolevCoordinate 0 v = v.toLp 2 := by
      simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
        SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
    rw [hz]
    rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact integral_nonneg fun y ↦ sq_nonneg _
  have hpoint (x : X) : ‖L.smoothToSobolev 0 (u x)‖ ^ 2 =
      ∑ j, ∫ y : Y, ‖f j (x, y)‖ ^ 2 := by
    rw [L.norm_smoothToSobolev_sq]
    apply Finset.sum_congr rfl
    intro j _
    rw [hcoord]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y ↦ congrArg (fun v ↦ ‖v‖ ^ 2) (hf j x y).symm)
  -- Joint Schwartz coordinates have integrable squared norms, so every finite sum is legitimate.
  have hInt (j : Fin L.size) :
      Integrable (fun p : X × Y ↦ ‖f j p‖ ^ 2) ((volume : Measure X).prod volume) := by
    have h := ((f j).memLp 2 ((volume : Measure X).prod volume)).norm_rpow
      (by norm_num) (by norm_num)
    exact memLp_one_iff_integrable.mp (by simpa using h)
  have hIter (j : Fin L.size) : Integrable (fun x : X ↦ ∫ y : Y, ‖f j (x, y)‖ ^ 2) :=
    (hInt j).integral_prod_left
  calc
    ‖hu.toLp (fun x ↦ L.smoothToSobolev 0 (u x))‖ ^ 2 =
        ∫ x : X, ‖L.smoothToSobolev 0 (u x)‖ ^ 2 := hFamily
    _ = ∫ x : X, ∑ j, ∫ y : Y, ‖f j (x, y)‖ ^ 2 := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ j, ∫ x : X, ∫ y : Y, ‖f j (x, y)‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun j _ ↦ hIter j)
    _ = ∑ j, ‖(f j).toLp 2 ((volume : Measure (Fin m → ℝ)).prod volume)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_prod _ (hInt j)]
      symm
      rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
      exact integral_nonneg fun x ↦ sq_nonneg _

end SmoothBundlePresentation

end AtiyahSinger
