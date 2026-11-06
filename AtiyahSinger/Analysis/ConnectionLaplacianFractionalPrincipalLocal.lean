/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianIntegratedTerm
public import AtiyahSinger.Analysis.ScalarResolventNormalization

/-!
# The normalized first fractional symbol in the original coordinates

Public module ID: M0387.

The retained first joint inverse is exact above a radius on each compact base
window. A large horizontal frequency remains above that radius for every positive
parameter. Its integral therefore has exactly the metric principal value with
the same partition weight and the original fractional-power normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

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

/-- The normalized first integrated symbol has the exact metric principal value above
a compact-local frequency radius, with the original patch and partition weight. -/
theorem exists_radius_normalized_integratedSymbol_zero_eq
    (P : FiniteResolventPatch (connectionLaplacian μ g h cov hcov hcomplex))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKD : K ⊆ P.chart '' P.domain)
    (hK : IsCompact K) :
    let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ (Fin n), R ≤ ‖ξ‖ →
      C⁻¹ • P.integratedSymbol 0 p x ξ =
        (P.coordinateWeight x *
          g.length (P.chart.symm x) (covectorFromChart P.chart (P.chart.symm x) ξ) ^
            (-2 * p)) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r)) := by
  classical
  let := P.cutoff.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let V := EuclideanSpace ℂ (Fin r)
  let split : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let D := P.chart '' P.domain
  let W : Set Y := (fun z ↦ (split z).1) ⁻¹' D
  let ι : X → Y := fun x ↦ split.symm (x, 0)
  have hι : Continuous ι := split.symm.continuous.comp
    (continuous_id.prodMk continuous_const)
  have hKW : ι '' K ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    change (split (split.symm (x, 0))).1 ∈ D
    simpa only [split.apply_symm_apply] using hKD hx
  obtain ⟨R, hR, hfirst⟩ := P.firstInverse_eq (ι '' K) hKW (hK.image hι)
  refine ⟨R, hR, ?_⟩
  intro x hx ξ hξR
  have hxD : x ∈ D := hKD hx
  have hξ : ξ ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hξR
    exact (not_le_of_gt hR) hξR
  let b : ℝ := g.length (P.chart.symm x)
    (covectorFromChart P.chart (P.chart.symm x) ξ) ^ 2
  -- Recover the scalar principal symbol from the same global operator and frame.
  have hprincipal : P.coordinate.principalSymbol x ξ =
      b • ContinuousLinearMap.id ℂ V := by
    obtain ⟨y, hy, rfl⟩ := hxD
    have hyc : y ∈ P.chart.source := (P.hasCoordinateExpression.1 hy).1.1
    have hye : y ∈ P.cutoff.frame.baseSet := (P.hasCoordinateExpression.1 hy).1.2
    have hcoordinate := covectorInChart_covectorFromChart
      P.chart P.chart_mem_atlas y hyc ξ
    apply ContinuousLinearMap.ext
    intro v
    have hspec := LinearMap.congr_fun
      ((connectionLaplacian μ g h cov hcov hcomplex).hasPrincipalSymbol
        P.chart P.chart_mem_atlas P.cutoff.frame P.cutoff.frame P.domain P.isOpen_domain
        P.coordinate P.hasCoordinateExpression y hy (covectorFromChart P.chart y ξ))
      (P.cutoff.frame.symmL ℂ y v)
    change P.cutoff.frame.linearMapAt ℂ y
      ((connectionLaplacian μ g h cov hcov hcomplex).principalSymbol y
        (covectorFromChart P.chart y ξ) (P.cutoff.frame.symmL ℂ y v)) =
      P.coordinate.principalSymbol (P.chart y)
        (covectorInChart P.chart y (covectorFromChart P.chart y ξ))
        (P.cutoff.frame.linearMapAt ℂ y (P.cutoff.frame.symmL ℂ y v)) at hspec
    rw [hcoordinate, connectionLaplacian_principalSymbol μ g h cov hcov hcomplex] at hspec
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      P.cutoff.frame.symmL_apply hye, P.cutoff.frame.linearMapAt_symm hye] at hspec
    change P.coordinate.principalSymbol (P.chart y) ξ v = b • v
    dsimp only [b]
    rw [P.chart.left_inv hyc]
    simpa only [← Complex.coe_smul, Complex.ofReal_pow] using hspec.symm
  have hb : 0 < b := by
    obtain ⟨y, hy, hxy⟩ := hxD
    have hyc : y ∈ P.chart.source := (P.hasCoordinateExpression.1 hy).1.1
    have hne : covectorFromChart P.chart y ξ ≠ 0 := by
      intro heq
      have hc := covectorInChart_covectorFromChart P.chart P.chart_mem_atlas y hyc ξ
      rw [heq] at hc
      have hz : covectorInChart P.chart y 0 = 0 := by ext i; rfl
      exact hξ (hc.symm.trans hz)
    dsimp only [b]
    rw [← hxy, P.chart.left_inv hyc]
    exact pow_pos (g.length_pos y _ hne) 2
  -- Euclidean joint frequency dominates its horizontal component, including n = 0.
  have hnorm (η : EuclideanSpace ℝ (Fin 1)) : ‖ξ‖ ≤ ‖split.symm (ξ, η)‖ := by
    let e : Y ≃ₗᵢ[ℝ] WithLp 2 (X × EuclideanSpace ℝ (Fin 1)) :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
        (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin 1 ↦ ℝ))
    have hsq : ‖split.symm (ξ, η)‖ ^ 2 = ‖ξ‖ ^ 2 + ‖η‖ ^ 2 := by
      change ‖e.symm (WithLp.toLp 2 (ξ, η))‖ ^ 2 = _
      rw [e.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
      rfl
    nlinarith [norm_nonneg ξ, norm_nonneg (split.symm (ξ, η)), sq_nonneg ‖η‖]
  have hsource (t : ℝ) :
      jointFrequencySymbolSlice (finiteResolventSourceSymbol P.coordinateWeight) t x ξ =
        P.coordinateWeight x • ContinuousLinearMap.id ℂ V := by
    let ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) :=
      ⟨1, 2, by norm_num, by norm_num⟩
    have hρ : ρ 0 = 1 := ρ.eventuallyEq_one.eq_of_nhds
    change ((P.coordinateWeight (split (split.symm (x, 0))).1 *
      ρ (split (split.symm (x, 0))).2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V = _
    rw [split.apply_symm_apply, hρ, mul_one, Complex.coe_smul]
  have hslice (t : ℝ) (ht : 0 < t) :
      jointFrequencySymbolSlice (P.symbol 0) t x ξ =
        (P.coordinateWeight x / (b + t)) • ContinuousLinearMap.id ℂ V := by
    let ζ : Y := split.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt t))
    have hζR : R ≤ ‖ζ‖ := hξR.trans (hnorm _)
    have hζlast : ζ (Fin.last n) = Real.sqrt t := by
      change (split (split.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt t)))).2 0 = _
      rw [split.apply_symm_apply]
    have hjoint : P.coordinate.parameterLift.principalSymbol (ι x) ζ =
        (b + t) • ContinuousLinearMap.id ℂ V := by
      rw [CoordinateDifferentialOperator.parameterLift_principalSymbol, hζlast,
        Real.sq_sqrt ht.le]
      change P.coordinate.principalSymbol (split (split.symm (x, 0))).1
        (split (split.symm (ξ, _))).1 + _ = _
      rw [split.apply_symm_apply, split.apply_symm_apply, hprincipal, ← add_smul]
    have hinverse : ((b + t) • ContinuousLinearMap.id ℂ V).inverse =
        (b + t)⁻¹ • ContinuousLinearMap.id ℂ V := by
      apply ContinuousLinearMap.inverse_eq
      · ext1 v
        simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
          smul_smul, mul_inv_cancel₀ (add_pos hb ht).ne', one_smul]
      · ext1 v
        simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
          smul_smul, inv_mul_cancel₀ (add_pos hb ht).ne', one_smul]
    have hretained := hfirst (ι x) ⟨x, hx, rfl⟩ ζ hζR
    rw [hjoint, hinverse] at hretained
    rw [P.symbol_zero]
    change (P.firstInverse (ι x) ζ).comp
      (jointFrequencySymbolSlice (finiteResolventSourceSymbol P.coordinateWeight) t x ξ) = _
    rw [hretained, hsource]
    have hid (v : V) : (ContinuousLinearMap.id ℂ V) v = v := rfl
    ext1 v
    simp only [ContinuousLinearMap.comp_apply, smul_apply, hid, smul_smul]
    congr 1
    ring
  let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  obtain ⟨hC, _, hnormal⟩ := scalar_resolvent_integral_normalization p hp hp1 b hb
  have hintegral : P.integratedSymbol 0 p x ξ =
      (b ^ (-p) * C) • (P.coordinateWeight x • ContinuousLinearMap.id ℂ V) := by
    change (∫ t in Ioi (0 : ℝ),
      t ^ (-p) • jointFrequencySymbolSlice (P.symbol 0) t x ξ) = _
    calc
      _ = ∫ t in Ioi (0 : ℝ), (t ^ (-p) / (b + t)) •
          (P.coordinateWeight x • ContinuousLinearMap.id ℂ V) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [hslice t ht]
        simp only [smul_smul]
        congr 1
        ring
      _ = (∫ t in Ioi (0 : ℝ), t ^ (-p) / (b + t)) •
          (P.coordinateWeight x • ContinuousLinearMap.id ℂ V) := integral_smul_const _ _
      _ = _ := by rw [hnormal]
  have hpower : b ^ (-p) =
      g.length (P.chart.symm x) (covectorFromChart P.chart (P.chart.symm x) ξ) ^ (-2 * p) := by
    dsimp only [b]
    rw [← Real.rpow_natCast_mul (g.length_nonneg _ _) 2 (-p)]
    congr 1
    ring
  change C⁻¹ • P.integratedSymbol 0 p x ξ = _
  rw [hintegral, smul_smul, smul_smul, hpower]
  congr 1
  have hCne : C ≠ 0 := hC.ne'
  field_simp [hCne]

end AtiyahSinger
