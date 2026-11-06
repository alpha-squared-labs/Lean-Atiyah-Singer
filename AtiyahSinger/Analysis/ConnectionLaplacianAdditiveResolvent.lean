/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianResolventSobolev
public import AtiyahSinger.Analysis.NormalizedResolventIntegral
public import AtiyahSinger.Analysis.ResolventIntegralInversion

/-!
# The actual additive resolvent and its normalized spectral integral

Public module ID: M0380.

The same positive inverse B defines B(1+tB)^{-1}. Its graph acts as the
resolvent of the original closed connection Laplacian plus t, including when
zero belongs to the spectrum of B. The normalized Lebesgue integral realizes
the original negative fractional smooth spectral action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
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

/-- The additive resolvent of the original positive connection Laplacian. -/
def connectionLaplacianResolvent (t : ℝ) : h.L2SectionSpace μ →L[ℂ] h.L2SectionSpace μ :=
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  B * Ring.inverse (1 + t • B)

/-- The additive resolvent retains the original closed graph and its uniform norm estimate. -/
theorem connectionLaplacianResolvent_properties (t : ℝ) (ht : 0 < t) :
    connectionLaplacianResolvent μ g h cov hcov hcomplex t =
      t⁻¹ • connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t⁻¹ ∧
    ‖connectionLaplacianResolvent μ g h cov hcov hcomplex t‖ ≤ (1 + t)⁻¹ ∧
    ∀ x y : h.L2SectionSpace μ,
      (x, y) ∈ (connectionLaplacianRealization μ g h cov hcov hcomplex).graph →
      connectionLaplacianResolvent μ g h cov hcov hcomplex t (y + t • x) = x := by
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  -- Rescaling the total ring inverse uses only a nonzero scalar, not an inverse of B.
  have hscale (A : H →L[ℂ] H) (c : ℝ) (hc : c ≠ 0) :
      Ring.inverse (c • A) = c⁻¹ • Ring.inverse A := by
    have hunit : IsUnit (algebraMap ℝ (H →L[ℂ] H) c) :=
      (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ (H →L[ℂ] H))
    calc
      Ring.inverse (c • A) =
          Ring.inverse (algebraMap ℝ (H →L[ℂ] H) c * A) := by rw [Algebra.smul_def]
      _ = Ring.inverse A * Ring.inverse (algebraMap ℝ (H →L[ℂ] H) c) :=
        Ring.inverse_mul (Or.inl hunit)
      _ = c⁻¹ • Ring.inverse A := by
        rw [← map_inv_eq_ringInverse_map (algebraMap ℝ (H →L[ℂ] H)) c,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hden : t⁻¹ • (1 : H →L[ℂ] H) + B = t⁻¹ • (1 + t • B) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hscaled : connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t⁻¹ =
      t • connectionLaplacianResolvent μ g h cov hcov hcomplex t := by
    change B * Ring.inverse (t⁻¹ • (1 : H →L[ℂ] H) + B) =
      t • (B * Ring.inverse (1 + t • B))
    rw [hden, hscale _ _ (inv_ne_zero ht.ne'), inv_inv, mul_smul_comm]
  have hs : connectionLaplacianResolvent μ g h cov hcov hcomplex t =
      t⁻¹ • connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t⁻¹ := by
    rw [hscaled, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  refine ⟨hs, ?_, ?_⟩
  · -- The already established scaled contraction yields exactly the additive resolvent bound.
    rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    calc
      _ ≤ t⁻¹ * (1 + t⁻¹)⁻¹ := mul_le_mul_of_nonneg_left
        (connectionLaplacianScaledResolvent_properties μ g h cov hcov hcomplex
          t⁻¹ (inv_pos.mpr ht)).2 (inv_nonneg.mpr ht.le)
      _ = (1 + t)⁻¹ := by
        have h₁ : 1 + t ≠ 0 := (add_pos zero_lt_one ht).ne'
        have h₂ : 1 + t⁻¹ ≠ 0 := (add_pos zero_lt_one (inv_pos.mpr ht)).ne'
        field_simp
        ring
  · intro x y hxy
    have hR : connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t⁻¹
        (t⁻¹ • (y + t • x)) = x := by
      apply ((connectionLaplacianScaledResolvent_properties μ g h cov hcov hcomplex
        t⁻¹ (inv_pos.mpr ht)).1 x _).mpr
      refine ⟨y, hxy, ?_⟩
      rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      exact add_comm _ _
    rw [ContinuousLinearMap.map_smul_of_tower] at hR
    rw [hs]
    exact hR

/-- The normalized additive-resolvent integral gives the original fractional smooth action. -/
theorem connectionLaplacianInverse_rpow_eq_normalized_integral
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let C : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    0 < C ∧
      IntegrableOn (fun t : ℝ ↦ t ^ (-p) •
        connectionLaplacianResolvent μ g h cov hcov hcomplex t) (Set.Ioi 0) ∧
      CFC.rpow (connectionLaplacianInverse μ g h cov hcov hcomplex) p =
        C⁻¹ • (∫ t in Set.Ioi (0 : ℝ), t ^ (-p) •
          connectionLaplacianResolvent μ g h cov hcov hcomplex t) ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        h.smoothToL2 μ (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p) u) =
          C⁻¹ • (∫ t in Set.Ioi (0 : ℝ), t ^ (-p) •
            connectionLaplacianResolvent μ g h cov hcov hcomplex t (h.smoothToL2 μ u)) := by
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let C : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  obtain ⟨hB, _, _, _, hnorm, _⟩ :=
    connectionLaplacianInverse_properties μ g h cov hcov hcomplex
  obtain ⟨hC, hi, heq⟩ := cfc_rpow_eq_normalized_resolvent_integral B hB hnorm p hp hp1
  have hinv := resolvent_integral_inv_parameter B p
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (-p) •
      connectionLaplacianResolvent μ g h cov hcov hcomplex t) (Set.Ioi 0) := hinv.1.mp hi
  have hpower : CFC.rpow B p = C⁻¹ •
      (∫ t in Set.Ioi (0 : ℝ), t ^ (-p) •
        connectionLaplacianResolvent μ g h cov hcov hcomplex t) := by
    rw [heq, hinv.2]
    rfl
  refine ⟨hC, hint, hpower, ?_⟩
  intro u
  -- The original bounded negative-order graph specifies precisely this same L2 action.
  have hgraph := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex (-2 * p) u
  rw [connectionLaplacianSpectralPower, ite_eq_left (by linarith : -2 * p ≤ 0)] at hgraph
  have hdegree : -(-2 * p) / 2 = p := by ring
  rw [hdegree] at hgraph
  obtain ⟨x, hx, hvalue⟩ := (LinearPMap.mem_graph_iff _).mp hgraph
  change (x : H) = h.smoothToL2 μ u at hx
  change CFC.rpow B p (x : H) =
    h.smoothToL2 μ (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p) u) at hvalue
  rw [hx] at hvalue
  rw [← hvalue, hpower, smul_apply, ContinuousLinearMap.integral_apply hint]
  rfl

end AtiyahSinger
