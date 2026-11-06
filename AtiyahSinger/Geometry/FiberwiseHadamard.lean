/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hadamard division in a vector variable with parameters

Public module ID: M1232.

The mean derivative along the segment from `(x,0)` to `(x,v)` expresses the
difference of a smooth function as a linear map applied to `v`. For finite-
dimensional parameter and vector spaces and a complete normed target, this
linear map varies smoothly. The original segment must remain in the prescribed open smooth domain.
This gives the parameter-uniform division by the scale in tubular rescaling,
including its value at scale zero; pointwise differentiability is insufficient
for that use.

This is the standard integral proof of Hadamard's lemma, applied only in the
vector variable and retaining the other variable as a parameter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set Topology
open scoped ContDiff Manifold

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The mean derivative in the second variable along its original radial segment. -/
def fiberwiseMeanDerivative (f : E × F → G) (x : E) (v : F) : F →L[ℝ] G :=
  ∫ t in (0 : ℝ)..1,
    (fderiv ℝ f (x, t • v)).comp (ContinuousLinearMap.inr ℝ E F)

/-- At zero the mean derivative is the actual partial derivative, with no scale factor. -/
theorem fiberwiseMeanDerivative_zero (f : E × F → G) (x : E) :
    fiberwiseMeanDerivative f x 0 =
      (fderiv ℝ f (x, 0)).comp (ContinuousLinearMap.inr ℝ E F) := by
  simp [fiberwiseMeanDerivative]

/-- Integrating the derivative in the vector variable recovers its exact finite difference. -/
theorem fiberwiseMeanDerivative_apply (f : E × F → G) {s : Set (E × F)}
    (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s) (x : E) (v : F)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (x, t • v) ∈ s) :
    fiberwiseMeanDerivative f x v v = f (x, v) - f (x, 0) := by
  let D (t : ℝ) : F →L[ℝ] G :=
    (fderiv ℝ f (x, t • v)).comp (ContinuousLinearMap.inr ℝ E F)
  have hc : ContinuousOn D (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.clm_comp
    · exact (hf.continuousOn_fderiv_of_isOpen hs (by simp)).comp
        (continuous_const.prodMk (continuous_id.smul continuous_const)).continuousOn hseg
    · exact continuousOn_const
  have hD : IntervalIntegrable D volume 0 1 := hc.intervalIntegrable_of_Icc zero_le_one
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun a : ℝ ↦ f (x, a • v)) (D t v) t := by
    have ht' : (x, t • v) ∈ s := hseg t (by simpa using ht)
    have hf' := (hf.contDiffAt (hs.mem_nhds ht')).differentiableAt (by simp)
    have hpath : HasDerivAt (fun a : ℝ ↦ (x, a • v)) (0, v) t :=
      by simpa using (hasDerivAt_const t x).prodMk ((hasDerivAt_id t).smul_const v)
    simpa only [D, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using
      hf'.hasFDerivAt.comp_hasDerivAt t hpath
  -- Evaluation commutes with the integrable operator-valued mean derivative.
  rw [fiberwiseMeanDerivative, ContinuousLinearMap.intervalIntegral_apply hD]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hc.clm_apply continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
  simpa using h

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The mean derivative is smooth wherever all its radial segments stay in the smooth domain. -/
theorem contDiffOn_fiberwiseMeanDerivative (f : E × F → G) {s W : Set (E × F)}
    (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s) (hW : IsOpen W)
    (hseg : ∀ z ∈ W, ∀ t ∈ Icc (0 : ℝ) 1, (z.1, t • z.2) ∈ s) :
    ContDiffOn ℝ ∞ (fun z : E × F ↦ fiberwiseMeanDerivative f z.1 z.2) W := by
  let I := Set.Icc (0 : ℝ) 1
  let H : I × (E × F) → F →L[ℝ] G := fun p ↦
    (fderiv ℝ f (p.2.1, (p.1 : ℝ) • p.2.2)).comp (ContinuousLinearMap.inr ℝ E F)
  -- The entire segment parameter is compact, including both endpoints.
  have ht : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E × F)) 𝓘(ℝ) ∞
      (fun p : I × (E × F) ↦ (p.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hpath : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞
      (fun p : I × (E × F) ↦ (p.2.1, (p.1 : ℝ) • p.2.2)) := by
    exact (contDiff_fst.contMDiff.comp contMDiff_snd).prodMk_space
      (ht.smul (contDiff_snd.contMDiff.comp contMDiff_snd))
  have hH : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, F →L[ℝ] G) ∞
      H (univ ×ˢ W) := by
    intro p hp
    have hmem := hseg p.2 hp.2 (p.1 : ℝ) p.1.property
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) (p.2.1, (p.1 : ℝ) • p.2.2) :=
      (hf.contDiffAt (hs.mem_nhds hmem)).fderiv_right (by simp)
    exact ((hd.contMDiffAt.comp p (hpath p)).clm_comp contMDiffAt_const).contMDiffWithinAt
  -- Lift the two normed spaces to a common universe for the existing integral theorem.
  -- These linear equivalences change no vector, derivative, or integral value.
  let a : ULift.{w} (E × F) ≃L[ℝ] E × F := ContinuousLinearEquiv.ulift
  let b : ULift.{u} (F →L[ℝ] G) ≃L[ℝ] (F →L[ℝ] G) := ContinuousLinearEquiv.ulift
  have hHl : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, ULift.{w} (E × F)))
      𝓘(ℝ, ULift.{u} (F →L[ℝ] G)) ∞
      (fun p ↦ b.symm (H (p.1, a p.2))) (univ ×ˢ (a ⁻¹' W)) := by
    apply b.symm.contDiff.contMDiff.comp_contMDiffOn
    apply hH.comp
      (contMDiff_fst.prodMk (a.contDiff.contMDiff.comp contMDiff_snd)).contMDiffOn
    intro p hp
    exact ⟨hp.1, hp.2⟩
  have hintl := contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
    (volume : Measure I) (hW.preimage a.continuous) hHl
  have hint : ContDiffOn ℝ ∞ (fun z ↦ ∫ t : I, H (t, z)) W := by
    have hl := b.contDiff.comp_contDiffOn
      (hintl.comp a.symm.contDiff.contDiffOn (fun z hz ↦ by simpa using hz))
    convert hl using 1
    funext z
    simp only [Function.comp_apply, a.apply_symm_apply]
    rw [← b.integral_comp_comm]
    simp
  -- The interval subtype measure is exactly the restricted Lebesgue measure.
  convert hint using 1
  funext z
  have he := unitInterval.measurePreserving_coe.integral_comp
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)
    (fun t : ℝ ↦ (fderiv ℝ f (z.1, t • z.2)).comp (ContinuousLinearMap.inr ℝ E F))
  rw [integral_Icc_eq_integral_Ioc] at he
  rw [fiberwiseMeanDerivative, intervalIntegral.integral_of_le zero_le_one]
  exact he.symm

end AtiyahSinger
