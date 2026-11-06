/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianResolventSobolevFamily
public import AtiyahSinger.Analysis.ScalarResolventNormalization

/-!
# Sobolev remainders of the specified fractional spectral action

Public module ID: M0389.

An exact finite parametrix identity and a uniformly bounded continuous Sobolev
remainder give a bounded Sobolev realization of the difference between the
original fractional spectral power and the integrated finite parametrix.
The proof uses the same closed graph and the same normalized Lebesgue integral.
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

set_option maxHeartbeats 2000000 in
-- The extended limit accommodates the uniform Sobolev remainder and integrated fractional
-- parametrix.
/-- A finite parametrix with a uniform Sobolev remainder identifies the fractional remainder. -/
theorem exists_connectionLaplacian_integrated_remainder_sobolev
    (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) (k : ℕ)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (S : ℝ → (smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := r) E))
    (Q : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := r) E)
    (hQ : ∀ u : smoothSections (n := n) (r := r) E,
      IntegrableOn (fun t : ℝ ↦ t ^ (-p) • h.smoothToL2 μ (S t u)) (Set.Ioi 0) ∧
        h.smoothToL2 μ (Q u) =
          (∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1)⁻¹ •
            (∫ t in Set.Ioi (0 : ℝ), t ^ (-p) • h.smoothToL2 μ (S t u)))
    (R : ℝ → (A.SobolevSpace s →L[ℂ] A.SobolevSpace (2 * (k : ℝ))))
    (hRcont : ContinuousOn R (Set.Ioi 0))
    (hRbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖R t‖ ≤ C)
    (hR : ∀ t : ℝ, 0 < t → ∀ u : smoothSections (n := n) (r := r) E,
      R t (A.smoothToSobolev s u) = A.smoothToSobolev (2 * (k : ℝ))
        ((connectionLaplacian μ g h cov hcov hcomplex).toLinearMap (S t u) +
          (1 + t : ℝ) • S t u - u)) :
    ∃ V : A.SobolevSpace s →L[ℂ] A.SobolevSpace (2 * (k : ℝ)),
      ∀ u : smoothSections (n := n) (r := r) E,
        V (A.smoothToSobolev s u) = A.smoothToSobolev (2 * (k : ℝ))
          (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p) u - Q u) := by
  classical
  let H := h.L2SectionSpace μ
  let f := h.smoothToL2 μ
  let d : ℝ := 2 * (k : ℝ)
  let C : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let : NormedSpace ℝ (A.SobolevSpace d) := NormedSpace.restrictScalars ℝ ℂ _
  let : NormedSpace ℝ (A.SobolevSpace s →L[ℂ] A.SobolevSpace d) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let : SecondCountableTopologyEither ℝ
      (A.SobolevSpace s →L[ℂ] A.SobolevSpace d) := ⟨Or.inl inferInstance⟩
  let F := connectionLaplacianResolvent μ g h cov hcov hcomplex
  let Δ := (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap
  obtain ⟨G, hG, D, hD, hGb, hGs⟩ :=
    exists_connectionLaplacianResolvent_sobolev_family μ g h cov hcov hcomplex A k
  obtain ⟨C₀, hC₀, hC₀b⟩ := hRbound
  let J (t : ℝ) : A.SobolevSpace s →L[ℂ] A.SobolevSpace d :=
    ((t ^ (-p) : ℝ) : ℂ) • (G t).comp (R t)
  -- The scalar resolvent weight dominates the full operator-valued remainder.
  have hweight : Integrable (fun t : ℝ ↦ t ^ (-p) / (1 + t)) ν :=
    (scalar_resolvent_integral_normalization p hp hp1 1 zero_lt_one).2.1
  have hJcont : ContinuousOn J (Set.Ioi 0) := by
    have hw : ContinuousOn (fun t : ℝ ↦ t ^ (-p)) (Set.Ioi 0) := by
      intro t ht
      exact (Real.continuousAt_rpow_const t (-p) (Or.inl (ne_of_gt ht))).continuousWithinAt
    exact (Complex.continuous_ofReal.comp_continuousOn hw).smul (hG.clm_comp hRcont)
  have hJ : Integrable J ν := by
    apply ((hweight.const_mul (D * C₀))).mono' (hJcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [J]
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    calc
      _ ≤ t ^ (-p) * (‖G t‖ * ‖R t‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (Real.rpow_nonneg ht.le _)
      _ ≤ t ^ (-p) * ((D / (1 + t)) * C₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hGb t ht) (hC₀b t ht)
          (norm_nonneg _) (div_nonneg hD (add_nonneg zero_le_one (le_of_lt ht))))
          (Real.rpow_nonneg ht.le _)
      _ = (D * C₀) * (t ^ (-p) / (1 + t)) := by ring
  let V : A.SobolevSpace s →L[ℂ] A.SobolevSpace d := -(((C⁻¹ : ℝ) : ℂ) • ∫ t, J t ∂ν)
  -- Keep the original Sobolev-to-metric-L2 embedding throughout the integral comparison.
  have hd : 0 ≤ d := mul_nonneg (by norm_num) (Nat.cast_nonneg k)
  let e : A.SobolevSpace d →L[ℂ] H :=
    (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
      (A.sobolevInclusion d 0 hd)
  have he (u : smoothSections (n := n) (r := r) E) :
      e (A.smoothToSobolev d u) = f u := by
    dsimp only [e, ContinuousLinearMap.comp_apply]
    rw [A.sobolevInclusion_smoothToSobolev]
    exact h.sobolevZeroEquivL2_smooth (μ := μ) A u
  have heinj : Function.Injective e :=
    (h.sobolevZeroEquivL2 (μ := μ) A).injective.comp (A.sobolevInclusion_injective d 0 hd)
  -- The graph equation gives the exact signed resolvent error on the same smooth section.
  have hactual (t : ℝ) (ht : 0 < t) (u : smoothSections (n := n) (r := r) E) :
      e (G t (R t (A.smoothToSobolev s u))) = f (S t u) - F t (f u) := by
    let v := Δ (S t u) + (1 + t : ℝ) • S t u - u
    obtain ⟨U, hU, hGU⟩ := hGs t ht
    rw [hR t ht u, hGU, he, hU]
    change F t (f v) = f (S t u) - F t (f u)
    have hgraph : (f (S t u), f (S t u + Δ (S t u))) ∈
        (connectionLaplacianRealization μ g h cov hcov hcomplex).graph := by
      let L := connectionLaplacianSmoothCore μ g h cov hcov hcomplex
      apply LinearPMap.le_graph_of_le L.le_closure
      let ef := LinearEquiv.ofInjective f (h.smoothToL2_injective μ)
      refine L.mem_graph_iff.mpr ⟨ef (S t u), rfl, ?_⟩
      change f (ef.symm (ef (S t u)) + Δ (ef.symm (ef (S t u)))) = _
      rw [ef.symm_apply_apply]
    have hres := (connectionLaplacianResolvent_properties μ g h cov hcov hcomplex t ht).2.2
      (f (S t u)) (f (S t u + Δ (S t u))) hgraph
    have hinput : f (S t u + Δ (S t u)) + t • f (S t u) = f u + f v := by
      dsimp only [v]
      simp only [map_add, map_sub, LinearMap.map_smul_of_tower, add_smul, one_smul]
      abel
    rw [hinput, map_add] at hres
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hres)
  obtain ⟨_, hFi, _, hpower⟩ :=
    connectionLaplacianInverse_rpow_eq_normalized_integral μ g h cov hcov hcomplex p hp hp1
  refine ⟨V, ?_⟩
  intro u
  apply heinj
  rw [he]
  have hJu : Integrable (fun t ↦ J t (A.smoothToSobolev s u)) ν :=
    (ContinuousLinearMap.apply ℂ (A.SobolevSpace d) (A.smoothToSobolev s u)).integrable_comp hJ
  have hFu : Integrable (fun t : ℝ ↦ t ^ (-p) • F t (f u)) ν := by
    exact (ContinuousLinearMap.apply ℂ H (f u)).integrable_comp hFi
  have hvalue : e (V (A.smoothToSobolev s u)) =
      -(C⁻¹ • ∫ t, (t ^ (-p) • f (S t u) - t ^ (-p) • F t (f u)) ∂ν) := by
    change e (-(((C⁻¹ : ℝ) : ℂ) • ((∫ t, J t ∂ν) (A.smoothToSobolev s u)))) = _
    rw [map_neg, map_smul, Complex.coe_smul, ContinuousLinearMap.integral_apply hJ,
      ← e.integral_comp_comm hJu]
    congr 2
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change e (((t ^ (-p) : ℝ) : ℂ) • G t (R t (A.smoothToSobolev s u))) = _
    rw [map_smul, Complex.coe_smul, hactual t ht u, smul_sub]
  rw [hvalue, integral_sub (hQ u).1 hFu, smul_sub, map_sub, (hQ u).2, hpower u]
  abel

end AtiyahSinger
