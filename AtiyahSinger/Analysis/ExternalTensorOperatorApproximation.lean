/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSymbolPiece
public import AtiyahSinger.Analysis.ExternalTensorSmoothingApproximation
public import AtiyahSinger.Analysis.GeometricTensorFiniteApproximation

/-!
# Geometric tensor approximation with the original smooth remainder

Public module ID: M0616.

The positive-frequency cutoffs act on the original external tensor bundles.
Their bounded realizations converge in the fixed geometric Sobolev norms, and
the limiting operator is specified on actual pure smooth tensor sections.
The fixed input and output charts and frames are used in every comparison.

Source: the finite-atlas assembly in SG III.13.5, pp.249--250.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped ContDiff Manifold SchwartzMap TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := m) (r := s) F]

variable [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]

set_option maxHeartbeats 1800000 in
-- Finite sums, metric Sobolev equivalences and native tensor unitaries share fixed instances.
/-- A finite first-factor representation plus its order-zero remainder admits genuine
product PDO approximants. Their difference from the specified cutoff sum is smoothing. -/
theorem exists_externalTensor_finite_sum_approximation
    (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
    (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
    (k : SmoothHermitianMetric (n := m) (r := s) F)
    {ℓ : ℕ} (L : Fin ℓ → PseudodifferentialPiece (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (hL : ∀ i, HasCompactSupport (L i).symbol)
    (J : smoothSections (n := n) (r := r₀) E₀ →ₗ[ℂ] smoothSections (n := n) (r := r₁) E₁)
    (hJ : IsPseudodifferentialOperator E₀ E₁ μ 0 J)
    (Q : QuantizationPresentation (n := m) (r := s) (q := s) F F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
    letI := externalTensorTopology (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
    letI := externalTensorTopology (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let g₁ := externalTensorMetric h₁ k
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F))
      (D : SmoothBundlePresentation (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
        (∀ (u : smoothSections (n := n) (r := r₀) E₀)
          (v : smoothSections (n := m) (r := s) F),
          T (A.smoothToSobolev 1 (externalTensorSection E₀ F u v)) =
            g₁.smoothToL2 (μ.prod ν)
              (externalTensorSection E₁ F (((∑ i, (L i).toLinearMap) + J) u) v)) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
              (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1,
            IsSmoothingOperator (μ.prod ν) (P.toLinearMap - ∑ i, ∑ j,
              ((L i).productCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
                (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
            ‖(g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap.comp
              (P.sobolevRealization A D 1 0 (by norm_num)) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
  let := externalTensorTopology (r := r₀) (s := s) E₀ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
  let := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
  let := externalTensorTopology (r := r₁) (s := s) E₁ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  dsimp only
  let g₀ := externalTensorMetric h₀ k
  let g₁ := externalTensorMetric h₁ k
  intro A D
  -- Build the bounded factor action of the original order-zero remainder.
  let A₀ := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r₀) E₀)
  let A₁ := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r₁) E₁)
  let e₀ := h₀.sobolevZeroEquivL2 (μ := μ) A₀
  let e₁ := h₁.sobolevZeroEquivL2 (μ := μ) A₁
  let J₀ : PseudodifferentialOperator (n := n) (r := r₀) (q := r₁) E₀ E₁ μ 0 :=
    ⟨J, hJ⟩
  let S₀ := e₁.toContinuousLinearMap.comp
    ((J₀.sobolevRealization A₀ A₁ 0 0 (by norm_num)).comp e₀.symm.toContinuousLinearMap)
  have hS₀ (u : smoothSections (n := n) (r := r₀) E₀) :
      S₀ (h₀.smoothToL2 μ u) = h₁.smoothToL2 μ (J u) := by
    rw [← h₀.sobolevZeroEquivL2_smooth (μ := μ) A₀ u]
    change e₁ (J₀.sobolevRealization A₀ A₁ 0 0 (by norm_num)
      (e₀.symm (e₀ (A₀.smoothToSobolev 0 u)))) = _
    rw [e₀.symm_apply_apply, J₀.sobolevRealization_smoothToSobolev]
    exact h₁.sobolevZeroEquivL2_smooth (μ := μ) A₁ (J u)
  let U₀ := externalTensorL2Equiv μ ν h₀ k
  let U₁ := externalTensorL2Equiv μ ν h₁ k
  let Sprod := U₁.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((TensorProduct.mapL S₀ (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion.comp
      U₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let I := (g₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  have hI (u : smoothSections (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F)) :
      I (A.smoothToSobolev 1 u) = g₀.smoothToL2 (μ.prod ν) u := by
    change (g₀.sobolevZeroEquivL2 (μ := μ.prod ν) A)
      (A.sobolevInclusion 1 0 (by norm_num) (A.smoothToSobolev 1 u)) = _
    rw [A.sobolevInclusion_smoothToSobolev, g₀.sobolevZeroEquivL2_smooth]
  have hpure (u : smoothSections (n := n) (r := r₀) E₀)
      (v : smoothSections (n := m) (r := s) F) :
      Sprod (g₀.smoothToL2 (μ.prod ν) (externalTensorSection E₀ F u v)) =
        g₁.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F (J u) v) := by
    rw [← externalTensorL2Equiv_smooth μ ν h₀ k u v]
    change U₁ ((TensorProduct.mapL S₀ (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion
      (U₀.symm (U₀ _))) = _
    rw [U₀.symm_apply_apply]
    change U₁ ((TensorProduct.mapL S₀ (ContinuousLinearMap.id ℂ (k.L2SectionSpace ν))).completion
      (↑(h₀.smoothToL2 μ u ⊗ₜ[ℂ] k.smoothToL2 ν v))) = _
    simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
      ContinuousLinearMap.id_apply, hS₀]
    exact externalTensorL2Equiv_smooth μ ν h₁ k (J u) v
  -- Sum the original compact-symbol pieces in the same presentations.
  choose T hT c hc happ using fun i ↦ (L i).exists_externalTensor_approximation μ ν (hL i) Q A D
  let E := (g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap
  have hE (u : smoothSections (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F)) :
      E (D.smoothToSobolev 0 u) = g₁.smoothToL2 (μ.prod ν) u :=
    g₁.sobolevZeroEquivL2_smooth (μ := μ.prod ν) D u
  let R := E.comp (∑ i, T i) + Sprod.comp I
  refine ⟨R, ?_, ‖E‖ * (∑ i, c i) + 1,
    add_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ ↦ hc i))) zero_le_one, ?_⟩
  · intro u v
    have hsum : (∑ i, externalTensorSection E₁ F ((L i).toLinearMap u) v) +
        externalTensorSection E₁ F (J u) v =
          externalTensorSection E₁ F (((∑ i, (L i).toLinearMap) + J) u) v := by
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_sum, Finset.sum_apply]
      change (∑ i, ((L i).toLinearMap u).val x.1 ⊗ₜ[ℂ] v.val x.2) +
        (J u).val x.1 ⊗ₜ[ℂ] v.val x.2 = _
      rw [← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]
      congr 1
      simp only [LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
        Pi.add_apply, Submodule.coe_sum, Finset.sum_apply]
    change E ((∑ i, T i) (A.smoothToSobolev 1 (externalTensorSection E₀ F u v))) +
      Sprod (I (A.smoothToSobolev 1 (externalTensorSection E₀ F u v))) = _
    rw [hI, hpure]
    simp only [sum_apply, hT]
    rw [← map_sum, hE]
    change g₁.smoothToL2 (μ.prod ν)
        (∑ i, externalTensorSection E₁ F ((L i).toLinearMap u) v) +
      g₁.smoothToL2 (μ.prod ν) (externalTensorSection E₁ F (J u) v) = _
    rw [← map_add, hsum]
  · intro ε hε hε1
    choose P hPmap hPbound using fun i ↦ happ i ε hε hε1
    obtain ⟨Jε, hJε, Sε, hSε, herror⟩ :=
      exists_externalTensorL2_smoothing_approximation (μ := μ) (ν := ν)
        h₀ h₁ k J S₀ hS₀ ε hε A
    let PJ : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
        (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1 :=
      ⟨Jε, hJε.isPseudodifferentialOperator 1 Jε⟩
    let Pε := pseudodifferentialOperatorOfSpace ((∑ i, (P i).toSpace) + PJ.toSpace)
    have hPε : Pε.toLinearMap = (∑ i, (P i).toLinearMap) + Jε := by
      simp only [Pε, pseudodifferentialOperatorOfSpace, Submodule.coe_add, Submodule.coe_sum,
        PseudodifferentialOperator.toSpace, PJ]
    refine ⟨Pε, ?_, ?_⟩
    · have heq : Pε.toLinearMap - ∑ i, ∑ j,
          ((L i).productCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
            (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap = Jε := by
        rw [hPε]
        simp only [hPmap, add_sub_cancel_left]
      rwa [heq]
    · have hreal : E.comp (Pε.sobolevRealization A D 1 0 (by norm_num)) =
          E.comp (∑ i, (P i).sobolevRealization A D 1 0 (by norm_num)) + Sε.comp I := by
        apply DFunLike.ext'
        apply (A.denseRange_smoothToSobolev 1).equalizer
          (E.comp (Pε.sobolevRealization A D 1 0 (by norm_num))).continuous
          (E.comp (∑ i, (P i).sobolevRealization A D 1 0 (by norm_num)) + Sε.comp I).continuous
        funext u
        change E (Pε.sobolevRealization A D 1 0 (by norm_num) (A.smoothToSobolev 1 u)) =
          E ((∑ i, (P i).sobolevRealization A D 1 0 (by norm_num)) (A.smoothToSobolev 1 u)) +
            Sε (I (A.smoothToSobolev 1 u))
        rw [Pε.sobolevRealization_smoothToSobolev, hI, hSε]
        simp only [sum_apply, PseudodifferentialOperator.sobolevRealization_smoothToSobolev]
        rw [← map_sum, hE, hE]
        change g₁.smoothToL2 (μ.prod ν) (Pε.toLinearMap u) =
          g₁.smoothToL2 (μ.prod ν) (∑ i, (P i).toLinearMap u) +
            g₁.smoothToL2 (μ.prod ν) (Jε u)
        simp only [hPε, LinearMap.add_apply, LinearMap.sum_apply, map_add]
      have hdiff : E.comp (Pε.sobolevRealization A D 1 0 (by norm_num)) - R =
          E.comp (∑ i, ((P i).sobolevRealization A D 1 0 (by norm_num) - T i)) +
            (Sε.comp I - Sprod.comp I) := by
        rw [hreal]
        apply ContinuousLinearMap.ext
        intro u
        simp only [R, ContinuousLinearMap.comp_apply, add_apply, sub_apply,
          sum_apply, map_sub, map_sum, Finset.sum_sub_distrib]
        abel
      have hfirst : ‖E.comp (∑ i, ((P i).sobolevRealization A D 1 0 (by norm_num) - T i))‖ ≤
          (‖E‖ * ∑ i, c i) * ε := by
        apply (E.opNorm_comp_le _).trans
        calc
          ‖E‖ * ‖∑ i, ((P i).sobolevRealization A D 1 0 (by norm_num) - T i)‖ ≤
              ‖E‖ * ∑ i, ‖(P i).sobolevRealization A D 1 0 (by norm_num) - T i‖ := by
            gcongr
            exact norm_sum_le _ _
          _ ≤ ‖E‖ * ∑ i, c i * ε := by
            gcongr with i
            exact hPbound i
          _ = _ := by rw [← Finset.sum_mul]; ring
      have hsecond : ‖Sε.comp I - Sprod.comp I‖ ≤ ε := by
        rw [norm_sub_rev]
        exact le_of_lt herror
      rw [hdiff]
      exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

set_option maxHeartbeats 1000000 in
-- Compactification retains each original piece and the same full remainder.
/-- Every original first-order PDO has genuine tensor approximants in the fixed geometric
Sobolev norms, with an explicit cutoff representation modulo an actual smooth kernel. -/
theorem PseudodifferentialOperator.exists_externalTensor_approximation
    (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
    (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
    (k : SmoothHermitianMetric (n := m) (r := s) F)
    (P₀ : PseudodifferentialOperator (n := n) (r := r₀) (q := r₁) E₀ E₁ μ 1)
    (Q : QuantizationPresentation (n := m) (r := s) (q := s) F F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
    letI := externalTensorTopology (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
    letI := externalTensorTopology (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let g₁ := externalTensorMetric h₁ k
    ∃ (ℓ : ℕ) (L : Fin ℓ → PseudodifferentialPiece (n := n) (r := r₀) (q := r₁) E₀ E₁ 1),
      ∃ hL : ∀ i, HasCompactSupport (L i).symbol,
        IsSmoothingOperator μ (P₀.toLinearMap - ∑ i, (L i).toLinearMap) ∧
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F))
      (D : SmoothBundlePresentation (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] g₁.L2SectionSpace (μ.prod ν),
        (∀ (u : smoothSections (n := n) (r := r₀) E₀)
          (v : smoothSections (n := m) (r := s) F),
          T (A.smoothToSobolev 1 (externalTensorSection E₀ F u v)) =
            g₁.smoothToL2 (μ.prod ν)
              (externalTensorSection E₁ F (P₀.toLinearMap u) v)) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
              (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1,
            IsSmoothingOperator (μ.prod ν) (P.toLinearMap - ∑ i, ∑ j,
              ((L i).productCutoff (hL i) (Q.patch j).chart (Q.patch j).chart_mem_atlas
                (Q.patch j).input (Q.patch j).sameFrameOutput rfl ε hε).toLinearMap) ∧
            ‖(g₁.sobolevZeroEquivL2 (μ := μ.prod ν) D).toContinuousLinearMap.comp
              (P.sobolevRealization A D 1 0 (by norm_num)) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
  let := externalTensorTopology (r := r₀) (s := s) E₀ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
  let := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
  let := externalTensorTopology (r := r₁) (s := s) E₁ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  dsimp only
  obtain ⟨ℓ, L, hP⟩ := P₀.isPseudodifferentialOperator
  choose K hK hKmap _hKsymbol using fun i ↦ (L i).exists_compactSymbol
  have hsum : (∑ i, (K i).toLinearMap) = ∑ i, (L i).toLinearMap :=
    Finset.sum_congr rfl (fun i _ ↦ hKmap i)
  have hrep : IsSmoothingOperator μ (P₀.toLinearMap - ∑ i, (K i).toLinearMap) := by
    rw [hsum]
    exact hP
  refine ⟨ℓ, K, hK, hrep, ?_⟩
  intro A D
  obtain ⟨T, hT, happ⟩ := exists_externalTensor_finite_sum_approximation μ ν h₀ h₁ k K hK
    (P₀.toLinearMap - ∑ i, (K i).toLinearMap)
    (hrep.isPseudodifferentialOperator 0 _) Q A D
  refine ⟨T, ?_, happ⟩
  have heq : (∑ i, (K i).toLinearMap) + (P₀.toLinearMap - ∑ i, (K i).toLinearMap) =
      P₀.toLinearMap := by abel
  simpa only [heq] using hT

end AtiyahSinger
