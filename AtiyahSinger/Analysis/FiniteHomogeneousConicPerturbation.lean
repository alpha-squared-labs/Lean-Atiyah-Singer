/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteHomogeneousConicInvertibility
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Uniformly bounded remainders in a homogeneous elliptic cone

A finite real weighted sum of degree-one symbols remains invertible in one
cone at large horizontal frequency after adding any operator with the given
uniform norm bound. The remainder need not be continuous in its parameters.
The original finite-dimensional operator ball is compact. Multiplying its
parameter by one additional transverse scalar makes the complete family
homogeneous, so the existing conic theorem supplies both the cone and radius.

This permits actual order-zero chart remainders in the associated-sphere
comparison. A zeroth-order estimate on the original compact chart supports
must supply the bound; it is not inferred from formal principal-class equality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Topology

variable {Z X Y E F ι : Type*} [TopologicalSpace Z] [CompactSpace Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [Fintype ι]

/-- One cone and one radius tolerate every original remainder with the specified norm bound. -/
theorem exists_bijective_weightedHomogeneousSum_add_of_bound
    (a : ι → Z → X → Y → E →L[ℂ] F) (w : ι → Z → ℝ)
    (hw : ∀ i, Continuous (w i))
    (ha : ∀ i z ξ, ξ ≠ 0 →
      ContinuousAt (fun u : Z × X × Y ↦ a i u.1 u.2.1 u.2.2) (z, ξ, 0))
    (hhom : ∀ i z ξ η (s : ℝ), 0 < s → a i z (s • ξ) (s • η) = (s : ℂ) • a i z ξ η)
    (haxis : ∀ z ξ, ξ ≠ 0 → Function.Bijective
      (∑ i, (w i z : ℂ) • a i z ξ 0 : E →L[ℂ] F)) (D : ℝ) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ z ξ η (r : E →L[ℂ] F),
      R ≤ ‖ξ‖ → ‖η‖ < δ * ‖ξ‖ → ‖r‖ ≤ D →
        Function.Bijective ((∑ i, (w i z : ℂ) • a i z ξ η) + r : E →L[ℂ] F) := by
  classical
  let : ProperSpace (E →L[ℂ] F) := FiniteDimensional.proper ℂ (E →L[ℂ] F)
  let B := Metric.closedBall (0 : E →L[ℂ] F) D
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : E →L[ℂ] F) D)
  let P (_ : Unit) (z : Z × B) (ξ : X) (η : Y × ℝ) : E →L[ℂ] F :=
    (∑ i, (w i z.1 : ℂ) • a i z.1 ξ η.1) + (η.2 : ℂ) • z.2.val
  -- Keep the bounded remainder as an independent compact parameter.
  have hcontinuous (i : Unit) (z : Z × B) (ξ : X) (hξ : ξ ≠ 0) :
      ContinuousAt (fun u : (Z × B) × X × (Y × ℝ) ↦ P i u.1 u.2.1 u.2.2)
        (z, ξ, 0) := by
    apply ContinuousAt.add
    · apply tendsto_finsetSum
      intro j _
      have hweight : ContinuousAt
          (fun u : (Z × B) × X × (Y × ℝ) ↦ (w j u.1.1 : ℂ)) (z, ξ, 0) := by
        fun_prop
      have hterm : ContinuousAt
          (fun u : (Z × B) × X × (Y × ℝ) ↦ a j u.1.1 u.2.1 u.2.2.1)
          (z, ξ, 0) := (ha j z.1 ξ hξ).comp
            (f := fun u : (Z × B) × X × (Y × ℝ) ↦ (u.1.1, u.2.1, u.2.2.1))
            (x := (z, ξ, 0)) (by fun_prop)
      exact hweight.smul hterm
    · fun_prop
  have hscale (i : Unit) (z : Z × B) (ξ : X) (η : Y × ℝ) (s : ℝ) (hs : 0 < s) :
      P i z (s • ξ) (s • η) = ((s ^ (1 : ℝ) : ℝ) : ℂ) • P i z ξ η := by
    simp only [P, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hhom _ _ _ _ _ hs,
      Real.rpow_one, Complex.ofReal_mul, smul_add, Finset.smul_sum, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have haxisP (z : Z × B) (ξ : X) (hξ : ξ ≠ 0) :
      Function.Bijective (∑ i : Unit, ((1 : ℝ) : ℂ) • P i z ξ 0 : E →L[ℂ] F) := by
    simpa [P] using haxis z.1 ξ hξ
  obtain ⟨ε, hε, hcone⟩ := exists_bijective_weightedHomogeneousSum_in_cone
    P (fun _ _ ↦ 1) 1 (fun _ ↦ continuous_const) hcontinuous hscale haxisP
  -- The slice with extra scalar equal to one becomes a large-frequency condition.
  refine ⟨ε / 2, 2 / ε, half_pos hε, div_pos (by norm_num) hε, ?_⟩
  intro z ξ η r hlarge hη hr
  let b : B := ⟨r, by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hr⟩
  have htwo : 2 ≤ ε * ‖ξ‖ := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have hξ : ξ ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, mul_zero] at htwo
    linarith
  have hη' : ‖η‖ < ε * ‖ξ‖ := by
    nlinarith [norm_nonneg ξ]
  have hpair : ‖(η, (1 : ℝ))‖ < ε * ‖ξ‖ := by
    rw [Prod.norm_def, norm_one, max_lt_iff]
    exact ⟨hη', by linarith⟩
  have h := hcone (z, b) ξ (η, 1) hξ hpair
  simpa [P, b] using h

end AtiyahSinger
