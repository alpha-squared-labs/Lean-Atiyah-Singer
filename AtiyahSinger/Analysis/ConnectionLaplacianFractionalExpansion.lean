/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFiniteResolventIdentity
public import AtiyahSinger.Analysis.ConnectionLaplacianIntegratedRemainder
public import AtiyahSinger.Analysis.ConnectionLaplacianIntegratedTermL2
public import AtiyahSinger.Analysis.FiniteResolventPatchSobolev
public import AtiyahSinger.Analysis.SobolevAsymptoticRecognition

/-!
# The original fractional spectral action has the fixed parametrix expansion

Public module ID: M0384.

The terms use one fixed family of actual connection-Laplacian patches. Their
normalized integrals have the prescribed decreasing PDO orders. Arbitrarily deep
finite residuals give the required Sobolev remainders of the original spectral
power, and Sobolev asymptotic recognition recovers every finite PDO remainder.
No target symbol estimate, PDO certificate or resolvent identity is an input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set
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
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- The normalized j-th term retains the same integrated piece in every fixed patch. -/
def FiniteResolventPatch.fractionalTerm
    {L : DifferentialOperator (n := n) (r := r) (q := r) E E 2} {k : ℕ}
    (P : Fin k → FiniteResolventPatch L) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : ℕ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
  (((∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1)⁻¹ : ℝ) : ℂ) •
    ∑ i, ((P i).integratedTerm j p hp hp1).toLinearMap

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

/-- The original fractional smooth spectral power has the expansion of the same fixed patches. -/
theorem connectionLaplacianSmoothPower_has_fractional_expansion
    (A : SmoothBundlePresentation (n := n) (r := r) E) {k : ℕ}
    (P : Fin k → FiniteResolventPatch (connectionLaplacian μ g h cov hcov hcomplex))
    (hpartition : ∀ x : M, ∑ i, (P i).weight x = 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ N : ℕ, IsPseudodifferentialOperator E E μ (-2 * p - (N : ℝ))
      ((connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p)).toLinearMap -
        ∑ j ∈ Finset.range N, FiniteResolventPatch.fractionalTerm P p hp hp1 j) := by
  classical
  let C : ℝ := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  let orders (j : ℕ) : ℝ := -2 * p - (j : ℝ)
  let terms := FiniteResolventPatch.fractionalTerm P p hp hp1
  let Q (N : ℕ) := ∑ j ∈ Finset.range N, terms j
  let S (N : ℕ) (t : ℝ) :
      smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
    ∑ i, ∑ j ∈ Finset.range N, (P i).positiveTerm j t
  let T := (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p)).toLinearMap
  -- Every normalized term is already an actual finite sum of the original PDO pieces.
  have hterms (j : ℕ) : IsPseudodifferentialOperator E E μ (orders j) (terms j) := by
    have hsum : IsPseudodifferentialOperator E E μ (-2 * p - (j : ℝ))
        (∑ i, ((P i).integratedTerm j p hp hp1).toLinearMap) := by
      change (∑ i, ((P i).integratedTerm j p hp hp1).toLinearMap) ∈
        pseudodifferentialSpace E E μ (-2 * p - (j : ℝ))
      apply Submodule.sum_mem
      intro i _
      exact PseudodifferentialPiece.isPseudodifferentialOperator (μ := μ)
        (-2 * p - (j : ℝ)) ((P i).integratedTerm j p hp hp1)
    exact IsPseudodifferentialOperator.smul (-2 * p - (j : ℝ)) ((C⁻¹ : ℝ) : ℂ) _ hsum
  have horders : StrictAnti orders := by
    intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    dsimp only [orders]
    linarith
  have hlim : Tendsto orders atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (-2 * p - b)
    filter_upwards [eventually_ge_atTop N] with j hj
    have hcast : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    dsimp only [orders]
    linarith
  -- Finite sums preserve the already proved actual metric-L2 integrals of the same terms.
  have hQ (N : ℕ) (u : smoothSections (n := n) (r := r) E) :
      IntegrableOn (fun t : ℝ ↦ t ^ (-p) • h.smoothToL2 μ (S N t u)) (Ioi 0) ∧
        h.smoothToL2 μ (Q N u) = C⁻¹ •
          (∫ t in Ioi (0 : ℝ), t ^ (-p) • h.smoothToL2 μ (S N t u)) := by
    have hpart (i : Fin k) (j : ℕ) :=
      (P i).integrableOn_smul_term_smoothToL2_and_integratedTerm μ h A j p hp hp1 u
    have hweight (t : ℝ) : t ^ (-p) • h.smoothToL2 μ (S N t u) =
        ∑ i, ∑ j ∈ Finset.range N, t ^ (-p) • h.smoothToL2 μ ((P i).positiveTerm j t u) := by
      simp only [S, LinearMap.sum_apply, map_sum, Finset.smul_sum]
    have hint : IntegrableOn (fun t : ℝ ↦
        ∑ i, ∑ j ∈ Finset.range N, t ^ (-p) • h.smoothToL2 μ ((P i).positiveTerm j t u))
        (Ioi 0) :=
      integrable_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum (Finset.range N) (fun j _ ↦ (hpart i j).1))
    have hactual : (∫ t in Ioi (0 : ℝ), t ^ (-p) • h.smoothToL2 μ (S N t u)) =
        ∑ i, ∑ j ∈ Finset.range N,
          h.smoothToL2 μ (((P i).integratedTerm j p hp hp1).toLinearMap u) := by
      simp_rw [hweight]
      rw [integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum (Finset.range N) (fun j _ ↦ (hpart i j).1))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum (Finset.range N) (fun j _ ↦ (hpart i j).1)]
      apply Finset.sum_congr rfl
      intro j _
      exact (hpart i j).2.symm
    refine ⟨hint.congr (Filter.Eventually.of_forall (fun t ↦ (hweight t).symm)), ?_⟩
    rw [hactual]
    calc
      h.smoothToL2 μ (Q N u) = ∑ j ∈ Finset.range N, C⁻¹ •
          ∑ i, h.smoothToL2 μ (((P i).integratedTerm j p hp hp1).toLinearMap u) := by
        simp only [Q, LinearMap.sum_apply, map_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [terms, FiniteResolventPatch.fractionalTerm,
          LinearMap.smul_apply, LinearMap.sum_apply]
        rw [(h.smoothToL2 μ).map_smul, map_sum, Complex.coe_smul]
      _ = C⁻¹ • (∑ j ∈ Finset.range N,
          ∑ i, h.smoothToL2 μ (((P i).integratedTerm j p hp hp1).toLinearMap u)) := by
        rw [Finset.smul_sum]
      _ = _ := by rw [Finset.sum_comm]
  -- Choose one sufficiently deep remainder for each prescribed pair of Sobolev orders.
  have hremainder (s t : ℝ) : ∃ N : ℕ, orders N ≤ s - t ∧
      ∃ V : A.SobolevSpace s →L[ℂ] A.SobolevSpace t,
        ∀ u : smoothSections (n := n) (r := r) E,
          V (A.smoothToSobolev s u) =
            A.smoothToSobolev t ((T - ∑ j ∈ Finset.range N, terms j) u) := by
    obtain ⟨gain, hgain⟩ := exists_nat_gt (max s t)
    let d : ℝ := 2 * (gain : ℝ)
    have hsd : s ≤ d := by
      have h₁ := le_max_left s t
      have h₂ : (0 : ℝ) ≤ (gain : ℝ) := Nat.cast_nonneg gain
      dsimp only [d]
      linarith
    have htd : t ≤ d := by
      have h₁ := le_max_right s t
      have h₂ : (0 : ℝ) ≤ (gain : ℝ) := Nat.cast_nonneg gain
      dsimp only [d]
      linarith
    let l : ℝ := s - d
    have hl : l ≤ 0 := sub_nonpos.mpr hsd
    have hsl : s - l = d := by dsimp only [l]; ring
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 - l) (-2 * p - s + t))
    have hNl : 1 - (N : ℝ) ≤ l := by
      have h₁ := le_max_left (1 - l) (-2 * p - s + t)
      linarith
    have horder : orders N ≤ s - t := by
      have h₁ := le_max_right (1 - l) (-2 * p - s + t)
      dsimp only [orders]
      linarith
    have hfamily (i : Fin k) :
        ∃ R : ℝ → (A.SobolevSpace s →L[ℂ] A.SobolevSpace d),
          Continuous R ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 < τ → ‖R τ‖ ≤ B) ∧
          ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
            R τ (A.smoothToSobolev s u) =
              A.smoothToSobolev d ((P i).remainder N τ hτ u) := by
      let H (v : ℝ) : Prop :=
        ∃ R : ℝ → (A.SobolevSpace s →L[ℂ] A.SobolevSpace v),
          Continuous R ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 < τ → ‖R τ‖ ≤ B) ∧
          ∀ (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E),
            R τ (A.smoothToSobolev s u) =
              A.smoothToSobolev v ((P i).remainder N τ hτ u)
      have hsource : H (s - l) :=
        (P i).exists_continuous_uniform_sobolev_remainder A A N l s hl hNl
      exact (congrArg H hsl).mp hsource
    choose R hcontinuous hbounded haction using hfamily
    choose B hB hbound using hbounded
    let Rsum (τ : ℝ) : A.SobolevSpace s →L[ℂ] A.SobolevSpace d := ∑ i, R i τ
    have hRcontinuous : Continuous Rsum :=
      continuous_finsetSum _ (fun i _ ↦ hcontinuous i)
    have hRbound : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ τ : ℝ, 0 < τ → ‖Rsum τ‖ ≤ B₀ := by
      refine ⟨∑ i, B i, Finset.sum_nonneg (fun i _ ↦ hB i), ?_⟩
      intro τ hτ
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ hbound i τ hτ))
    have hRactual (τ : ℝ) (hτ : 0 < τ) (u : smoothSections (n := n) (r := r) E) :
        Rsum τ (A.smoothToSobolev s u) = A.smoothToSobolev d
          ((connectionLaplacian μ g h cov hcov hcomplex).toLinearMap (S N τ u) +
            (1 + τ : ℝ) • S N τ u - u) := by
      have hS : S N τ u = ∑ i, ∑ j ∈ Finset.range N, (P i).term j τ hτ u := by
        simp only [S, LinearMap.sum_apply, FiniteResolventPatch.positiveTerm, dite_eq_left hτ]
      have hid : (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap (S N τ u) +
          (1 + τ : ℝ) • S N τ u = u + ∑ i, (P i).remainder N τ hτ u := by
        simpa only [← hS, Complex.coe_smul] using
          FiniteResolventPatch.apply_sum_patches P hpartition N τ hτ u
      have herror : (connectionLaplacian μ g h cov hcov hcomplex).toLinearMap (S N τ u) +
          (1 + τ : ℝ) • S N τ u - u = ∑ i, (P i).remainder N τ hτ u := by
        rw [hid, add_sub_cancel_left]
      rw [herror]
      simp only [Rsum, sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact haction i τ hτ u
    obtain ⟨V, hV⟩ := exists_connectionLaplacian_integrated_remainder_sobolev
      μ g h cov hcov hcomplex A s gain p hp hp1 (S N) (Q N) (hQ N)
      Rsum hRcontinuous.continuousOn hRbound hRactual
    refine ⟨N, horder, (A.sobolevInclusion d t htd).comp V, ?_⟩
    intro u
    change A.sobolevInclusion d t htd (V (A.smoothToSobolev s u)) = _
    rw [hV u]
    change A.sobolevInclusion d t htd
      (A.smoothToSobolev d ((T - ∑ j ∈ Finset.range N, terms j) u)) = _
    exact A.sobolevInclusion_smoothToSobolev d t htd _
  exact has_pseudodifferential_expansion_of_sobolev_remainders μ A A orders horders hlim
    terms hterms T hremainder

/-- The original fractional spectral action is a PDO, without additional symbol-estimate inputs. -/
theorem isPseudodifferentialOperator_connectionLaplacianSmoothPower_fractional
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IsPseudodifferentialOperator E E μ (-2 * p)
      (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p)).toLinearMap := by
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨k, P, hpartition⟩ :=
    exists_connectionLaplacian_finite_resolvent_patches μ g h cov hcov hcomplex
  simpa only [Nat.cast_zero, sub_zero, Finset.range_zero, Finset.sum_empty] using
    connectionLaplacianSmoothPower_has_fractional_expansion μ g h cov hcov hcomplex
      A P hpartition p hp hp1 0

end AtiyahSinger
