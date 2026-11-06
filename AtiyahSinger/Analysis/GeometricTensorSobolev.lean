/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Analysis.IntegerSobolevDerivatives
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# First Sobolev coordinates and the full derivative graph

Public module ID: M0666.

The first Bessel coordinate is isometric to the closed graph containing the
original function and all its first derivatives. The derivatives are scaled by
the period-one Fourier normalization. This concrete graph is used to compare
the two partial derivative families in product charts, and to integrate local
Fourier reconstruction in a Banach space.

This is a local functional-analytic supplement to SG III.2.2; it retains the
existing Bessel multiplier and the actual coordinate derivatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped SchwartzMap

set_option maxSynthPendingDepth 30

variable (n r : ℕ)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "L" => Lp V 2 (volume : Measure X)

/-- The function and all its first coordinate derivatives, with the Fourier scaling. -/
def schwartzH1Jet : 𝓢(X, V) →ₗ[ℂ] PiLp 2 (fun _ : Option (Fin n) ↦ L) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp (LinearMap.pi fun a ↦
    match a with
    | none => (SchwartzMap.toLpCLM ℂ _ 2 volume).toLinearMap
    | some i => (((2 * Real.pi)⁻¹ : ℂ) •
        ((SchwartzMap.toLpCLM ℂ _ 2 volume).comp
          (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, V)
            (EuclideanSpace.single i (1 : ℝ))))).toLinearMap)

set_option maxHeartbeats 1000000 in
-- The norm identity unfolds finite Hilbert coordinates and their complex scalar maps.
/-- The original first Bessel norm is precisely the norm of the scaled derivative graph. -/
theorem norm_schwartzH1Jet (u : 𝓢(X, V)) :
    ‖schwartzH1Jet n r u‖ = ‖schwartzSobolevCoordinate 1 u‖ := by
  -- At order zero the Bessel multiplier is the identity on the original Schwartz function.
  have hzero (v : 𝓢(X, V)) : schwartzSobolevCoordinate 0 v = v.toLp 2 := by
    unfold schwartzSobolevCoordinate
    congr 1
    rw [SchwartzMap.fourierMultiplierCLM_apply]
    have heq : SchwartzMap.smulLeftCLM V
        (fun ξ : X ↦ ((1 + ‖ξ‖ ^ 2) ^ ((0 : ℝ) / 2) : ℝ)) (FourierTransform.fourier v) =
        FourierTransform.fourier v := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp
    rw [heq, FourierTransform.fourierInv_fourier_eq]
  -- Plancherel's derivative identity includes exactly the same period-one scaling.
  have h := norm_schwartzSobolevCoordinate_add_one_sq n r 0 u
  simp only [zero_add, hzero] at h
  have hc : ‖((2 * Real.pi)⁻¹ : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have hj : ‖schwartzH1Jet n r u‖ ^ 2 = ‖schwartzSobolevCoordinate 1 u‖ ^ 2 := by
    have heval (a : Option (Fin n)) : (schwartzH1Jet n r u).ofLp a =
        match a with
        | none => u.toLp 2
        | some i => ((2 * Real.pi)⁻¹ : ℂ) •
            (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u).toLp 2 := by
      cases a <;> rfl
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [heval, Fintype.sum_option, norm_smul, hc, mul_pow]
    rw [← Finset.mul_sum]
    exact h.symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hj

/-- The completed first-derivative graph in the actual finite Hilbert sum of L2 spaces. -/
abbrev EuclideanH1Graph : Type := (schwartzH1Jet n r).range.topologicalClosure

/-- The original smooth function together with its actual first derivatives in the closed graph. -/
def schwartzToH1Graph : 𝓢(X, V) →ₗ[ℂ] EuclideanH1Graph n r :=
  (Submodule.inclusion (schwartzH1Jet n r).range.le_topologicalClosure).comp
    (schwartzH1Jet n r).rangeRestrict

/-- Smooth coordinate functions are dense in the closed first-derivative graph. -/
theorem denseRange_schwartzToH1Graph : DenseRange (schwartzToH1Graph n r) := by
  have h : DenseRange
      (Set.inclusion (schwartzH1Jet n r).range.le_topologicalClosure) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact h.comp (schwartzH1Jet n r).surjective_rangeRestrict.denseRange
    (continuous_inclusion _)

/-- The actual L2 function underlying a completed first-derivative graph vector. -/
def euclideanH1GraphValue : EuclideanH1Graph n r →L[ℂ] L :=
  (PiLp.proj 2 _ none).comp (schwartzH1Jet n r).range.topologicalClosure.subtypeL

/-- A completed first-derivative graph vector is determined by its actual L2 function. -/
theorem euclideanH1GraphValue_injective : Function.Injective (euclideanH1GraphValue n r) := by
  let D := Lp.toTemperedDistributionCLM V (volume : Measure X) 2
  have hD : Function.Injective D :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  -- Integration by parts identifies every completed derivative with the distribution derivative.
  have hderiv (a : Fin n) (u : EuclideanH1Graph n r) :
      D (u.val (some a)) = ((2 * Real.pi)⁻¹ : ℂ) •
        LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ))
          (D (euclideanH1GraphValue n r u)) := by
    let P : EuclideanH1Graph n r →L[ℂ] L :=
      (PiLp.proj 2 _ (some a)).comp (schwartzH1Jet n r).range.topologicalClosure.subtypeL
    let R := (((2 * Real.pi)⁻¹ : ℂ) •
      LineDeriv.lineDerivOpCLM ℂ 𝓢'(X, V) (EuclideanSpace.single a (1 : ℝ))).comp
        (D.comp (euclideanH1GraphValue n r))
    have heq : D.comp P = R := by
      apply DFunLike.coe_injective
      apply (denseRange_schwartzToH1Graph n r).equalizer (D.comp P).continuous R.continuous
      funext v
      have hPv : P (schwartzToH1Graph n r v) = ((2 * Real.pi)⁻¹ : ℂ) •
          (LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) v).toLp 2 := rfl
      have hVv : euclideanH1GraphValue n r (schwartzToH1Graph n r v) = v.toLp 2 := rfl
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, R, smul_apply, hPv, hVv]
      rw [map_smul]
      congr 1
      simpa only [D, Lp.toTemperedDistributionCLM_apply,
        Lp.toTemperedDistribution_toLp_eq, LineDeriv.lineDerivOpCLM_apply] using
        (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq v
          (EuclideanSpace.single a (1 : ℝ))).symm
    exact congrArg (fun T : EuclideanH1Graph n r →L[ℂ] 𝓢'(X, V) ↦ T u) heq
  intro u v huv
  apply Subtype.ext
  apply PiLp.ext
  intro a
  cases a with
  | none => exact huv
  | some a =>
    apply hD
    rw [hderiv, hderiv, huv]

/-- The original first Bessel completion and the full L2 derivative graph are isometric.
The equality on Schwartz inputs specifies the actual identification, including its scale. -/
theorem existsUnique_euclideanH1GraphEquiv :
    let e : 𝓢(X, V) →ₗ[ℂ] (schwartzSobolevCoordinateLinearMap n r 1).range.topologicalClosure :=
      (Submodule.inclusion
        (schwartzSobolevCoordinateLinearMap n r 1).range.le_topologicalClosure).comp
        (schwartzSobolevCoordinateLinearMap n r 1).rangeRestrict
    let j : 𝓢(X, V) →ₗ[ℂ] EuclideanH1Graph n r :=
      (Submodule.inclusion (schwartzH1Jet n r).range.le_topologicalClosure).comp
        (schwartzH1Jet n r).rangeRestrict
    ∃! T : (schwartzSobolevCoordinateLinearMap n r 1).range.topologicalClosure ≃ₗᵢ[ℂ]
        EuclideanH1Graph n r,
      ∀ u, T (e u) = j u := by
  intro e j
  -- Both maps have dense range in the closures defining the two completions.
  have hdense {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (f : 𝓢(X, V) →ₗ[ℂ] W) : DenseRange
        ((Submodule.inclusion f.range.le_topologicalClosure).comp f.rangeRestrict) := by
    have h : DenseRange (Set.inclusion f.range.le_topologicalClosure) :=
      (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
    exact h.comp f.surjective_rangeRestrict.denseRange (continuous_inclusion _)
  have he : DenseRange e := hdense _
  have hj : DenseRange j := hdense _
  have hn (u : 𝓢(X, V)) : ‖j u‖ = ‖e u‖ := norm_schwartzH1Jet n r u
  -- The identity on smooth inputs extends isometrically to both complete graph closures.
  let T := (LinearEquiv.refl ℂ 𝓢(X, V)).extendOfIsometry e j he hj hn
  refine ⟨T, ?_, ?_⟩
  · intro u
    exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u
  · intro S hS
    apply DFunLike.coe_injective
    apply he.equalizer S.continuous T.continuous
    funext u
    exact (hS u).trans
      (LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ 𝓢(X, V)) e j he hj hn u).symm

end AtiyahSinger
