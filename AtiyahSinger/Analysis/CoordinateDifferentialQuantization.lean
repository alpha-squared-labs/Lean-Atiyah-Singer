/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateDifferentialIntegral
public import AtiyahSinger.Analysis.QuantizationJetDomination

/-!
# Passing the actual differential expression through the quantization integral

Public module ID: M0409.

The original local symbol estimates dominate all spatial derivatives of the Fourier
integrand. This permits the specified coordinate differential operator to act under
the integral, retaining the SG normalization and requiring no spatial support condition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open Filter MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 25

set_option maxHeartbeats 2000000 in

/-- The original coordinate differential operator passes through the Fourier integral of
any local symbol on Schwartz inputs, at every point of the open symbol domain. -/
theorem integrable_apply_quantization_integrand_and_apply_quantize
    {n r s q d : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n s q d U)
    (m : ℝ) (a : SymbolFunction n r s) (ha : IsSymbol U m a)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) ↦ P.apply
      (fun y : EuclideanSpace ℝ (Fin n) ↦
        Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) • a y ξ (fourierSG u ξ)) x) ∧
      P.apply (quantize a u) x = ((2 * Real.pi) ^ n)⁻¹ •
        ∫ ξ : EuclideanSpace ℝ (Fin n), P.apply
          (fun y : EuclideanSpace ℝ (Fin n) ↦
            Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) • a y ξ (fourierSG u ξ)) x := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin s)
  let f : X → X → W := fun ξ y ↦
    Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) • a y ξ (fourierSG u ξ)
  -- The same Fourier integrand is jointly smooth on the original open spatial domain.
  have hphase : ContDiff ℝ ∞
      (fun z : X × X ↦ Complex.exp (Complex.I * (inner ℝ z.1 z.2 : ℂ))) := by
    simpa [Function.comp_def, mul_comm] using
      Complex.hasTemperateGrowth_exp_mul_I.1.comp (contDiff_inner (𝕜 := ℝ))
  have hFourier : ContDiff ℝ ∞ (fourierSG u) :=
    ((FourierTransform.fourier u).smooth ⊤).comp
      ((2 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ X).contDiff
  have hmatrix : ContDiffOn ℝ ∞
      (fun z : X × X ↦ Complex.exp (Complex.I * (inner ℝ z.1 z.2 : ℂ)) • a z.1 z.2)
      (U ×ˢ univ) := hphase.contDiffOn.smul ha.1
  have hspatial : ContDiffOn ℝ ∞ (fun z : X × X ↦ f z.2 z.1) (U ×ˢ univ) :=
    (((ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.contDiffOn).comp hmatrix
      (mapsTo_univ _ _)).clm_apply ((hFourier.comp contDiff_snd).contDiffOn)
  have hjoint : ContDiffOn ℝ ∞ (Function.uncurry f) (univ ×ˢ U) :=
    hspatial.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz ↦ ⟨hz.2, hz.1⟩)
  have hf (ξ : X) : ContDiffOn ℝ ∞ (f ξ) U :=
    hjoint.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy ↦ ⟨mem_univ _, hy⟩)
  -- Actual spatial jets retain smooth dependence on their frequency parameter.
  have hjet (k : ℕ) : ContDiffOn ℝ ∞
      (fun z : X × X ↦ iteratedFDeriv ℝ k (f z.1) z.2) (univ ×ˢ U) := by
    intro z hz
    have hs : ContDiffAt ℝ ∞ (Function.uncurry f) z :=
      hjoint.contDiffAt ((isOpen_univ.prod hU).mem_nhds hz)
    have hj : ContDiffAt ℝ ∞
        (fun z : X × X ↦ iteratedFDeriv ℝ k (f z.1) z.2) z := by
      induction k with
      | zero =>
        exact hs.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ X W).symm : _ →L[ℝ] X [×0]→L[ℝ] W)
      | succ k ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun p : X × X ↦ fun y : X ↦
              iteratedFDeriv ℝ k (f p.1) y)) (z, z.2) :=
          ih.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun p : X × X ↦ fderiv ℝ (iteratedFDeriv ℝ k (f p.1)) p.2) z :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) W).symm :
            _ →L[ℝ] X [×(k + 1)]→L[ℝ] W)
    exact hj.contDiffWithinAt
  have hmeas (k : ℕ) (y : X) (hy : y ∈ U) :
      AEStronglyMeasurable (fun ξ ↦ iteratedFDeriv ℝ k (f ξ) y) volume := by
    have hsmooth : ContDiff ℝ ∞ (fun ξ ↦ iteratedFDeriv ℝ k (f ξ) y) := by
      rw [← contDiffOn_univ]
      exact (hjet k).comp (contDiffOn_id.prodMk contDiffOn_const)
        (fun ξ _ ↦ ⟨mem_univ ξ, hy⟩)
    exact hsmooth.continuous.aestronglyMeasurable
  -- Choose a compact closed ball inside U, then use its common integrable majorant.
  have hdom (k : ℕ) (y : X) (hy : y ∈ U) :
      ∃ t : Set X, t ∈ 𝓝 y ∧ t ⊆ U ∧ ∃ B : X → ℝ, Integrable B ∧
        ∀ᵐ ξ, ∀ z ∈ t, ‖iteratedFDeriv ℝ k (f ξ) z‖ ≤ B ξ := by
    obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hy)
    obtain ⟨B, hB, hbound⟩ := exists_integrable_bound_quantization_base_jet U hU m a ha
      (Metric.closedBall y ε) hεU (isCompact_closedBall _ _) k u
    exact ⟨Metric.closedBall y ε, Metric.closedBall_mem_nhds y hε, hεU, B, hB,
      Eventually.of_forall (fun ξ z hz ↦ hbound z hz ξ)⟩
  obtain ⟨hint, heq⟩ := integrable_apply_and_apply_integral volume hU P f hf hmeas hdom x hx
  refine ⟨hint, ?_⟩
  -- Pull out only the constant SG normalization, through the original finite expression.
  let G : X → W := fun y ↦ ∫ ξ, f ξ y
  let c : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hG : ContDiffOn ℝ ∞ G U :=
    contDiffOn_integral_of_locally_dominated_jets volume hU hf hmeas hdom
  have hder (k : ℕ) : iteratedFDeriv ℝ k (fun y ↦ c • G y) x =
      c • iteratedFDeriv ℝ k G x :=
    iteratedFDeriv_const_smul_apply' ((hG.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
  have hscale : P.apply (fun y ↦ c • G y) x = c • P.apply G x := by
    simp only [apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro α _
    rw [hder k.val, smul_apply, smul_comm ((-Complex.I) ^ k.val) c,
      ContinuousLinearMap.map_smul_of_tower]
  change P.apply (fun y ↦ c • G y) x = c • ∫ ξ, P.apply (f ξ) x
  rw [hscale, heq]

end AtiyahSinger.CoordinateDifferentialOperator
