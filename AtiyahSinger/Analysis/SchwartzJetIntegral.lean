/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzTensorDensity
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Integrable weighted jets of Schwartz families

Public module ID: M0942.

Global bounded weighted jets realize each original Schwartz seminorm in a
Banach space. They allow absolutely integrable Schwartz families to be handled
through normed targets while retaining every spatial weight and derivative,
without imposing a fictitious norm on Schwartz space itself.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set Topology
open scoped BoundedContinuousFunction ContDiff SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The global weighted jet, as a bounded continuous function on the original space. -/
def schwartzWeightedJet (k j : ℕ) : 𝓢(E, ℂ) →L[ℂ] E →ᵇ E [×j]→L[ℝ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun f ↦ BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x ↦ ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
      ((continuous_norm.pow k).smul
        ((f.smooth ⊤).continuous_iteratedFDeriv (by simp)))
      (SchwartzMap.seminorm ℂ k j f)
      (fun x ↦ by
        simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using
          SchwartzMap.le_seminorm ℂ k j f x))
    (by
      intro f g
      apply BoundedContinuousFunction.ext
      intro x
      change ‖x‖ ^ k • iteratedFDeriv ℝ j ((f : E → ℂ) + (g : E → ℂ)) x =
        ‖x‖ ^ k • iteratedFDeriv ℝ j f x + ‖x‖ ^ k • iteratedFDeriv ℝ j g x
      rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt,
        smul_add])
    (by
      intro a f
      apply BoundedContinuousFunction.ext
      intro x
      change ‖x‖ ^ k • iteratedFDeriv ℝ j (a • (f : E → ℂ)) x =
        a • (‖x‖ ^ k • iteratedFDeriv ℝ j f x)
      rw [iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt]
      exact smul_comm _ _ _)
    (by
      refine ⟨{(k, j)}, 1, zero_le_one, ?_⟩
      intro f
      simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply, one_mul]
      apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
      intro x
      change ‖‖x‖ ^ k • iteratedFDeriv ℝ j f x‖ ≤ _
      simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using
        SchwartzMap.le_seminorm ℂ k j f x)

/-- The bounded-jet norm equals its original Schwartz seminorm, without a support restriction. -/
theorem norm_schwartzWeightedJet (k j : ℕ) (f : 𝓢(E, ℂ)) :
    ‖schwartzWeightedJet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
    intro x
    change ‖‖x‖ ^ k • iteratedFDeriv ℝ j f x‖ ≤ _
    simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using
      SchwartzMap.le_seminorm ℂ k j f x
  · apply SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _)
    intro x
    have h := BoundedContinuousFunction.norm_coe_le_norm (schwartzWeightedJet k j f) x
    change ‖‖x‖ ^ k • iteratedFDeriv ℝ j f x‖ ≤ _ at h
    simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using h

/-- Integrability of every Schwartz seminorm allows every spatial derivative to
pass through the actual pointwise integral. No compact parameter space is assumed. -/
theorem iteratedFDeriv_integral_of_integrable_schwartz_seminorms
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)
    (F : Y → 𝓢(E, ℂ)) (hF : Continuous F)
    (hI : ∀ k j : ℕ, Integrable (fun y ↦ SchwartzMap.seminorm ℂ k j (F y)) μ)
    (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fun z ↦ ∫ y, F y z ∂μ) x =
      ∫ y, iteratedFDeriv ℝ j (F y) x ∂μ := by
  have hcont (k : ℕ) (x : E) : Continuous (fun y ↦ iteratedFDeriv ℝ k (F y) x) := by
    have h := ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (schwartzWeightedJet (E := E) 0 k)).continuous.comp hF
    change Continuous (fun y ↦ ‖x‖ ^ 0 • iteratedFDeriv ℝ k (F y) x) at h
    simpa only [pow_zero, one_smul] using h
  have hint (k : ℕ) (x : E) : Integrable (fun y ↦ iteratedFDeriv ℝ k (F y) x) μ :=
    (hI 0 k).mono' (hcont k x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (F y) k x)
  -- One more integrable seminorm dominates the derivative uniformly on the spatial domain.
  have hderiv (k : ℕ) (x : E) :
      HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (F y) z ∂μ)
        ((∫ y, iteratedFDeriv ℝ (k + 1) (F y) x ∂μ).curryLeft) x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) ℂ
    let d (y : Y) (z : E) : E →L[ℝ] E [×k]→L[ℝ] ℂ :=
      C (iteratedFDeriv ℝ (k + 1) (F y) z)
    have hD : HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (F y) z ∂μ)
        (∫ y, d y x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun z y ↦ d y z) (bound := fun y ↦ SchwartzMap.seminorm ℂ 0 (k + 1) (F y))
        (s := univ) Filter.univ_mem
      · exact Filter.Eventually.of_forall (fun z ↦ (hint k z).1)
      · exact hint k x
      · exact (C.continuous.comp (hcont (k + 1) x)).aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro y z _
        change ‖C (iteratedFDeriv ℝ (k + 1) (F y) z)‖ ≤ _
        rw [C.norm_map]
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (F y) (k + 1) z
      · exact hI 0 (k + 1)
      · apply Filter.Eventually.of_forall
        intro y z _
        have hdiff := ((F y).smooth ⊤).contDiffAt.differentiableAt_iteratedFDeriv (m := k) (x := z)
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
        exact hdiff.hasFDerivAt
    have hcomm := C.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (hint (k + 1) x)
    change (∫ y, d y x ∂μ) =
      (∫ y, iteratedFDeriv ℝ (k + 1) (F y) x ∂μ).curryLeft at hcomm
    rwa [hcomm] at hD
  -- The integrated jets form the full derivative tower of the pointwise integral.
  have hseries : HasFTaylorSeriesUpToOn ∞ (fun z ↦ ∫ y, F y z ∂μ)
      (fun z k ↦ ∫ y, iteratedFDeriv ℝ k (F y) z ∂μ) univ := by
    constructor
    · intro z _
      let C := continuousMultilinearCurryFin0 ℝ E ℂ
      have hcomm := C.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hint 0 z)
      change (∫ y, (iteratedFDeriv ℝ 0 (F y) z).curry0 ∂μ) =
        (∫ y, iteratedFDeriv ℝ 0 (F y) z ∂μ).curry0 at hcomm
      simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply] using hcomm.symm
    · intro k _ z _
      exact (hderiv k z).hasFDerivWithinAt
    · intro k _
      exact (continuous_iff_continuousAt.mpr (fun z ↦ (hderiv k z).continuousAt)).continuousOn
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := j)
    (by simp) uniqueDiffOn_univ (mem_univ x)
  rw [iteratedFDerivWithin_univ] at heq
  exact heq.symm

/-- Every continuous scalar functional commutes with a pointwise Schwartz integral
whose original seminorms are integrable. The proof factors that functional through
finitely many Banach-valued jets and applies the ordinary Hahn–Banach theorem there. -/
theorem schwartz_integral_apply
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)
    (F : Y → 𝓢(E, ℂ)) (hF : Continuous F)
    (hI : ∀ k j : ℕ, Integrable (fun y ↦ SchwartzMap.seminorm ℂ k j (F y)) μ)
    (f : 𝓢(E, ℂ)) (hf : ∀ x, f x = ∫ y, F y x ∂μ)
    (L : 𝓢(E, ℂ) →L[ℂ] ℂ) : L f = ∫ y, L (F y) ∂μ := by
  classical
  let p := (normSeminorm ℂ ℂ).comp L.toLinearMap
  have hp : Continuous p := continuous_norm.comp L.continuous
  obtain ⟨s, C, _, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) p hp
  let B := ∀ i : s, E →ᵇ E [×i.val.2]→L[ℝ] ℂ
  let J : 𝓢(E, ℂ) →L[ℂ] B :=
    ContinuousLinearMap.pi (fun i ↦ schwartzWeightedJet i.val.1 i.val.2)
  have hJnorm (g : 𝓢(E, ℂ)) :
      (s.sup (schwartzSeminormFamily ℂ E ℂ)) g ≤ ‖J g‖ := by
    rw [Seminorm.finset_sup_apply]
    apply NNReal.coe_le_coe.mpr
    apply Finset.sup_le
    intro i hi
    change SchwartzMap.seminorm ℂ i.1 i.2 g ≤ ‖J g‖
    rw [← norm_schwartzWeightedJet i.1 i.2 g]
    exact norm_le_pi_norm (J g) ⟨i, hi⟩
  have hLbound (g : 𝓢(E, ℂ)) : ‖L g‖ ≤ (C : ℝ) * ‖J g‖ := by
    have h := Seminorm.le_def.mp hC g
    change ‖L g‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ E ℂ)) g at h
    exact h.trans (mul_le_mul_of_nonneg_left (hJnorm g) C.coe_nonneg)
  -- The chosen jets determine L, even when their range is not closed.
  let S := LinearMap.range J.toLinearMap
  let R : 𝓢(E, ℂ) →ₗ[ℂ] S := J.toLinearMap.rangeRestrict
  have hR : Function.Surjective R := LinearMap.surjective_rangeRestrict _
  have hker : LinearMap.ker R ≤ LinearMap.ker L.toLinearMap := by
    intro g hg
    have hzero := congrArg Subtype.val (LinearMap.mem_ker.mp hg)
    change J g = 0 at hzero
    have h := hLbound g
    rw [hzero, norm_zero, mul_zero] at h
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  let l : S →ₗ[ℂ] ℂ := R.liftOfSurjective hR ⟨L.toLinearMap, hker⟩
  have hl (g : 𝓢(E, ℂ)) : l (R g) = L g := LinearMap.equivOfSurjective_apply hR hker
  have hlbound (z : S) : ‖l z‖ ≤ (C : ℝ) * ‖z‖ := by
    obtain ⟨g, rfl⟩ := hR z
    rw [hl]
    exact hLbound g
  let lC : S →L[ℂ] ℂ := l.mkContinuous C hlbound
  obtain ⟨Q, hQ, _⟩ := exists_extension_norm_eq S lC
  have hQJ (g : 𝓢(E, ℂ)) : Q (J g) = L g := (hQ (R g)).trans (hl g)
  -- All finite weighted-jet coordinates are genuine Bochner integrable functions.
  have hJF : Integrable (fun y ↦ J (F y)) μ := by
    apply integrable_pi_iff.mpr
    intro i
    have hmeas : AEStronglyMeasurable
        (fun y ↦ schwartzWeightedJet i.val.1 i.val.2 (F y)) μ :=
      ((schwartzWeightedJet (E := E) i.val.1 i.val.2).continuous.comp hF).aestronglyMeasurable
    apply (integrable_norm_iff hmeas).mp
    change Integrable (fun y ↦ ‖schwartzWeightedJet i.val.1 i.val.2 (F y)‖) μ
    simpa only [norm_schwartzWeightedJet] using hI i.val.1 i.val.2
  have hderiv (j : ℕ) (x : E) :
      iteratedFDeriv ℝ j f x = ∫ y, iteratedFDeriv ℝ j (F y) x ∂μ := by
    rw [show (f : E → ℂ) = (fun z ↦ ∫ y, F y z ∂μ) from funext hf]
    exact iteratedFDeriv_integral_of_integrable_schwartz_seminorms μ F hF hI j x
  have hJintegral : (∫ y, J (F y) ∂μ) = J f := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    let e : B →L[ℂ] E [×i.val.2]→L[ℝ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ x).comp (ContinuousLinearMap.proj i)
    have he := e.integral_comp_comm hJF
    change (∫ y, ‖x‖ ^ i.val.1 • iteratedFDeriv ℝ i.val.2 (F y) x ∂μ) =
      (∫ y, J (F y) ∂μ) i x at he
    rw [← he, integral_smul]
    change ‖x‖ ^ i.val.1 • (∫ y, iteratedFDeriv ℝ i.val.2 (F y) x ∂μ) =
      ‖x‖ ^ i.val.1 • iteratedFDeriv ℝ i.val.2 f x
    rw [hderiv]
  have hcomm := Q.integral_comp_comm hJF
  simpa only [hQJ, hJintegral] using hcomm.symm

end AtiyahSinger
