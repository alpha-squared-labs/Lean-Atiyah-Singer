/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianPowers

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Fractional inverse powers of the specified connection Laplacian

Public module ID: M0397.

The bounded operator `B * (t + B)⁻¹`, for the original inverse B of 1 + Delta,
is exactly the inverse of 1 + t (1 + Delta) on the original closed graph.
Its norm is at most 1 / (1 + t). The CFC integral representation consequently
expresses the same fractional inverse power and its specified smooth action
as a Bochner integral of these resolvents, with one integrable scalar bound.

The parameter measure is the normalization supplied by mathlib's real-power
integral theorem. The manifold measure, metrics, connection, Hilbert space and
closed graph remain the original ones. No spectral gap for the compact inverse
at zero is assumed. This is an analytic prerequisite for real-order PDO
recognition; it supplies no parameter-dependent symbol estimates.

Source: the standard resolvent integral for fractional positive powers, as
formalized in mathlib's `Rpow.IntegralRepresentation`; the identification with
the specified connection-Laplacian graph is the project's same-object bridge.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

local notation "H" => h.L2SectionSpace μ
local notation "B" => connectionLaplacianInverse μ g h cov hcov hcomplex
local notation "L" => connectionLaplacianRealization μ g h cov hcov hcomplex

/-- The bounded scaled resolvent of the original positive connection Laplacian. -/
def connectionLaplacianScaledResolvent (t : ℝ) : H →L[ℂ] H :=
  B * Ring.inverse (t • (1 : H →L[ℂ] H) + B)

/-- The scaled resolvent inverts the same closed graph and has its uniform contraction bound. -/
theorem connectionLaplacianScaledResolvent_properties (t : ℝ) (ht : 0 < t) :
    (∀ x y : H,
      connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t y = x ↔
        ∃ z : H, (x, z) ∈ (L).graph ∧ x + t • z = y) ∧
      ‖connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t‖ ≤ (1 + t)⁻¹ := by
  obtain ⟨hB, _, _, _, hnorm, _⟩ :=
    connectionLaplacianInverse_properties μ g h cov hcov hcomplex
  have hself : IsSelfAdjoint B := .of_nonneg hB
  let D : H →L[ℂ] H := t • (1 : H →L[ℂ] H) + B
  have hnonzero (x : ℝ) (hx : x ∈ spectrum ℝ B) : t + x ≠ 0 :=
    (add_pos_of_pos_of_nonneg ht (spectrum_nonneg_of_nonneg hB hx)).ne'
  have hden : cfc (fun x : ℝ ↦ t + x) B = D := by
    rw [cfc_const_add t (fun x : ℝ ↦ x) B continuousOn_id hself,
      cfc_id' ℝ B hself, Algebra.algebraMap_eq_smul_one]
  have hunit : IsUnit D := by
    rw [← hden]
    exact (isUnit_cfc_iff (fun x : ℝ ↦ t + x) B
      (continuousOn_const.add continuousOn_id) hself).mpr hnonzero
  have hleft : D * Ring.inverse D = 1 := Ring.mul_inverse_cancel D hunit
  have hright : Ring.inverse D * D = 1 := Ring.inverse_mul_cancel D hunit
  constructor
  · -- Algebraic inversion uses the original graph, including its actual domain.
    intro x y
    constructor
    · intro hxy
      let z : H := Ring.inverse D y
      have hBx : B z = x := hxy
      have hz : D z = y := by
        have heq := congrArg (fun T : H →L[ℂ] H ↦ T y) hleft
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using heq
      refine ⟨z, (connectionLaplacianInverse_graph μ g h cov hcov hcomplex x z).mpr hBx, ?_⟩
      change t • z + B z = y at hz
      simpa only [hBx, add_comm] using hz
    · rintro ⟨z, hz, hzy⟩
      have hBx : B z = x :=
        (connectionLaplacianInverse_graph μ g h cov hcov hcomplex x z).mp hz
      have hDz : D z = y := by
        change t • z + B z = y
        simpa only [hBx, add_comm] using hzy
      have hinverse : Ring.inverse D (D z) = z := by
        have heq := congrArg (fun T : H →L[ℂ] H ↦ T z) hright
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using heq
      change B (Ring.inverse D y) = x
      rw [← hDz, hinverse, hBx]
  · -- On the spectrum of the same positive contraction B, x / (t + x) ≤ 1 / (1 + t).
    rcases subsingleton_or_nontrivial H with hH | hH
    · let := hH
      have hzero : connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t = 0 :=
        Subsingleton.elim _ _
      rw [hzero, norm_zero]
      positivity
    let := hH
    have hratio : cfc (fun x : ℝ ↦ x / (t + x)) B =
        connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t := by
      rw [cfc_map_div (fun x : ℝ ↦ x) (fun x : ℝ ↦ t + x) B hnonzero
        continuousOn_id (continuousOn_const.add continuousOn_id) hself,
        cfc_id' ℝ B hself, hden]
      rfl
    rw [← hratio]
    apply norm_cfc_le (inv_nonneg.mpr (by positivity))
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hB hx
    have hx1 : x ≤ 1 := (le_abs_self x).trans
      ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
    rw [Real.norm_of_nonneg (div_nonneg hx0 (by positivity)), ← one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < t + x) (by positivity : 0 < 1 + t)).mpr
    nlinarith

/-- Fractional inverse powers and their original smooth action are exact resolvent integrals. -/
theorem connectionLaplacianInverse_rpow_eq_resolvent_integral
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : Measure ℝ,
      IntegrableOn (fun t : ℝ ↦ t ^ (p - 1) / (1 + t)) (Ioi 0) ν ∧
      IntegrableOn (fun t : ℝ ↦ t ^ (p - 1) •
        connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t) (Ioi 0) ν ∧
      CFC.rpow B p = ∫ t in Ioi 0, t ^ (p - 1) •
        connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t ∂ν ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        h.smoothToL2 μ (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p) u) =
          ∫ t in Ioi 0, t ^ (p - 1) •
            connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t
              (h.smoothToL2 μ u) ∂ν := by
  classical
  -- A zero Hilbert space needs no nonempty-base or positive-rank assumption.
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨0, by simp [IntegrableOn], by simp [IntegrableOn], ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · intro u
      exact Subsingleton.elim _ _
  let := hH
  have hB : 0 ≤ B :=
    (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
  let p' : NNReal := ⟨p, hp.le⟩
  have hp' : p' ∈ Ioo 0 1 := ⟨hp, hp1⟩
  -- One measure represents powers of every positive operator; use it for both B and the identity.
  obtain ⟨ν, hν⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (H →L[ℂ] H) hp'
  have hkernel (a : H →L[ℂ] H) (ha : 0 ≤ a) (t : ℝ) (ht : 0 < t) :
      cfcₙ (Real.rpowIntegrand₀₁ p t) a =
        t ^ (p - 1) • (a * Ring.inverse (t • (1 : H →L[ℂ] H) + a)) := by
    have hself : IsSelfAdjoint a := .of_nonneg ha
    have hnonzero (x : ℝ) (hx : x ∈ spectrum ℝ a) : t + x ≠ 0 :=
      (add_pos_of_pos_of_nonneg ht (spectrum_nonneg_of_nonneg ha hx)).ne'
    have hcont : ContinuousOn (Real.rpowIntegrand₀₁ p t) (quasispectrum ℝ a) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici ⟨hp, hp1⟩ ht).mono
        (fun x hx ↦ quasispectrum_nonneg_of_nonneg a ha x hx)
    rw [cfcₙ_eq_cfc (hf := hcont) (hf0 := Real.rpowIntegrand₀₁_zero_right)]
    calc
      _ = cfc (fun x : ℝ ↦ t ^ (p - 1) * (x / (t + x))) a := by
        apply cfc_congr
        intro x hx
        rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp, hp1⟩ ht.le
          (spectrum_nonneg_of_nonneg ha hx)]
        ring
      _ = _ := by
        rw [cfc_const_mul (t ^ (p - 1)) (fun x : ℝ ↦ x / (t + x)) a
          (continuousOn_id.div (continuousOn_const.add continuousOn_id) hnonzero),
          cfc_map_div (fun x : ℝ ↦ x) (fun x : ℝ ↦ t + x) a hnonzero
            continuousOn_id (continuousOn_const.add continuousOn_id) hself,
          cfc_id' ℝ a hself,
          cfc_const_add t (fun x : ℝ ↦ x) a continuousOn_id hself,
          cfc_id' ℝ a hself, Algebra.algebraMap_eq_smul_one]
  have hsame : (fun t : ℝ ↦ cfcₙ (Real.rpowIntegrand₀₁ p t) B) =ᵐ[ν.restrict (Ioi 0)]
      (fun t : ℝ ↦ t ^ (p - 1) •
        connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hkernel B hB t ht
  have hweight : IntegrableOn (fun t : ℝ ↦ t ^ (p - 1) / (1 + t)) (Ioi 0) ν := by
    -- Evaluating the same integral theorem at identity gives the scalar majorant's integrability.
    have hone : (0 : H →L[ℂ] H) ≤ 1 := zero_le_one
    apply (hν (1 : H →L[ℂ] H) hone).1.norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖cfcₙ (Real.rpowIntegrand₀₁ p t) (1 : H →L[ℂ] H)‖ = _
    have hcont : ContinuousOn (Real.rpowIntegrand₀₁ p t)
        (quasispectrum ℝ (1 : H →L[ℂ] H)) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici ⟨hp, hp1⟩ ht).mono
        (fun x hx ↦ quasispectrum_nonneg_of_nonneg _ hone x hx)
    rw [cfcₙ_eq_cfc (hf := hcont) (hf0 := Real.rpowIntegrand₀₁_zero_right), cfc_apply_one,
      Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one,
      Real.norm_of_nonneg (Real.rpowIntegrand₀₁_nonneg hp ht.le zero_le_one),
      Real.rpowIntegrand₀₁_eq_pow_div ⟨hp, hp1⟩ ht.le zero_le_one, mul_one, add_comm t 1]
  have hint := (hν B hB).1.congr hsame
  have hpower : CFC.rpow B p = ∫ t in Ioi 0, t ^ (p - 1) •
      connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t ∂ν := by
    have hraw := (hν B hB).2
    rw [CFC.nnrpow_eq_rpow (show 0 < p' from hp)] at hraw
    exact hraw.trans (integral_congr_ae hsame)
  refine ⟨ν, hweight, hint, hpower, ?_⟩
  intro u
  -- The specified smooth action lies on this bounded spectral graph at negative order.
  have hgraph := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex (-2 * p) u
  rw [connectionLaplacianSpectralPower, ite_eq_left (by linarith : -2 * p ≤ 0)] at hgraph
  have hdegree : -(-2 * p) / 2 = p := by ring
  rw [hdegree] at hgraph
  obtain ⟨x, hx, hvalue⟩ := (LinearPMap.mem_graph_iff _).mp hgraph
  change (x : H) = h.smoothToL2 μ u at hx
  change CFC.rpow B p (x : H) =
    h.smoothToL2 μ (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p) u) at hvalue
  rw [hx] at hvalue
  rw [← hvalue, hpower, ContinuousLinearMap.integral_apply hint]
  rfl

end AtiyahSinger
