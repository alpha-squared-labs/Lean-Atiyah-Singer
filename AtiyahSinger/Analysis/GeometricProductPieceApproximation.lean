/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricProductCutoffRealization

/-!
# Geometric norm approximation of a factorwise PDO piece

Public module ID: M0658.

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

set_option maxHeartbeats 1600000 in
-- The original tensor instances recur in both Sobolev extension identities.
/-- The actual tensor cutoff pieces converge in geometric H1-to-H0 norm to their
specified factorwise action on original smooth tensor sections. -/
theorem PseudodifferentialPiece.exists_productCutoff_approximation
    (L : PseudodifferentialPiece (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (hLK : HasCompactSupport L.symbol)
    (d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin m)) N)
    (B C : BundleChartCutoff (r := s) F d) (hCB : C.frame = B.frame) :
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
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F))
      (D : SmoothBundlePresentation (n := n + m) (r := r₁ * s) (externalTensorFiber E₁ F)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] D.SobolevSpace 0,
        (∀ (u : smoothSections (n := n) (r := r₀) E₀)
          (v : smoothSections (n := m) (r := s) F),
          T (A.smoothToSobolev 1 (externalTensorSection E₀ F u v)) =
            D.smoothToSobolev 0 (externalTensorSection E₁ F (L.toLinearMap u)
              (C.extend hd (SchwartzMap.smulLeftCLM _ C.cutoff (B.localize hd v))))) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
              (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1,
            P.toLinearMap = (L.productCutoff hLK d hd B C hCB ε hε).toLinearMap ∧
            ‖P.sobolevRealization A D 1 0 (by norm_num) - T‖ ≤ c * ε := by
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
  intro A D
  let K := L.productCutoff hLK d hd B C hCB 1 zero_lt_one
  let α : SymbolFunction n (r₀ * s) (r₁ * s) :=
    fun x ξ ↦ tensorIdentitySymbolMap r₀ r₁ s (L.symbol x ξ)
  have hα : IsSymbol Set.univ 1 α :=
    isSymbol_continuousLinearMap 1 L.symbol L.isSymbol
      ((tensorIdentitySymbolMap r₀ r₁ s).restrictScalars ℝ)
  have hαK : HasCompactSupport α := by
    apply hLK.of_isClosed_subset (isClosed_tsupport α)
    apply closure_minimal ?_ (isClosed_tsupport L.symbol)
    intro x hx
    by_contra h
    have hzero := image_eq_zero_of_notMem_tsupport h
    apply hx
    funext ξ
    change tensorIdentitySymbolMap r₀ r₁ s (L.symbol x ξ) = 0
    rw [hzero]
    exact (tensorIdentitySymbolMap r₀ r₁ s).map_zero
  obtain ⟨S, hS, c, hc, hbound⟩ :=
    exists_tensorProductSobolev_approximation L.symbol α hα hαK rfl
      C.cutoff C.smooth_cutoff C.compact_support
  -- Extend the fixed localization and extension maps to their same Bessel coordinates.
  let li := (schwartzSobolevCoordinateLinearMap (n + m) (r₀ * s) 1).comp
    (K.input.localizeLinearMap K.chart_mem_atlas)
  obtain ⟨ci, _, hci⟩ := K.input.exists_norm_localize_sobolev_le K.chart_mem_atlas A 1
  let I := li.extendOfNorm (A.smoothToSobolev 1)
  have hI (u : smoothSections (n := n + m) (r := r₀ * s) (externalTensorFiber E₀ F)) :
      I (A.smoothToSobolev 1 u) =
        schwartzSobolevCoordinate 1 (K.input.localize K.chart_mem_atlas u) :=
    li.extendOfNorm_eq (A.denseRange_smoothToSobolev 1) ⟨ci, hci⟩ u
  let lo := (D.smoothToSobolev 0).comp (K.output.extendLinearMap K.chart_mem_atlas)
  obtain ⟨co, _, hco⟩ := K.output.exists_norm_extend_sobolev_le K.chart_mem_atlas D 0
  let O := lo.extendOfNorm (schwartzSobolevCoordinateLinearMap (n + m) (r₁ * s) 0)
  have hO (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r₁ * s)))) :
      O (schwartzSobolevCoordinate 0 w) =
        D.smoothToSobolev 0 (K.output.extend K.chart_mem_atlas w) :=
    lo.extendOfNorm_eq (denseRange_schwartzSobolevCoordinate (n + m) (r₁ * s) 0) ⟨co, hco⟩ w
  let T := O.comp (S.comp I)
  refine ⟨T, ?_, ‖O‖ * c * ‖I‖, mul_nonneg (mul_nonneg (norm_nonneg _) hc) (norm_nonneg _), ?_⟩
  · intro u v
    let u₀ := L.input.localize L.chart_mem_atlas u
    let v₀ := B.localize hd v
    let w := K.input.localize K.chart_mem_atlas (externalTensorSection E₀ F u v)
    have hw (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
        (i : Fin r₀) (j : Fin s) :
        w (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (i, j)) =
          u₀ x i * v₀ y j :=
      externalTensorChartCutoff_localizedFunction L.input B u v (x, y) i j
    obtain ⟨z, hz, hSz⟩ := hS u₀ v₀ w hw
    change O (S (I (A.smoothToSobolev 1 (externalTensorSection E₀ F u v)))) = _
    rw [hI, hSz, hO]
    congr 1
    apply Subtype.ext
    funext p
    let u₁ := L.operator u₀
    let v₁ := SchwartzMap.smulLeftCLM _ C.cutoff v₀
    have hv₁ (y : EuclideanSpace ℝ (Fin m)) : v₁ y = C.cutoff y • v₀ y :=
      SchwartzMap.smulLeftCLM_apply_apply
        (C.compact_support.hasTemperateGrowth C.smooth_cutoff) v₀ y
    have hcoord (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
        (i : Fin r₁) (j : Fin s) :
        z (EuclideanSpace.finAddEquivProd.symm p) (finProdFinEquiv (i, j)) =
          u₁ p.1 i * v₁ p.2 j := by
      rw [hz, hv₁]
      change _ = L.operator u₀ p.1 i * ((C.cutoff p.2 : ℂ) * v₀ p.2 j)
      rw [L.operator_apply]
      ring
    exact externalTensorChartCutoff_extendedFunction L.output C u₁ v₁ z hcoord p.1 p.2
  · intro ε hε hε1
    let Kε := L.productCutoff hLK d hd B C hCB ε hε
    let P : PseudodifferentialOperator (n := n + m) (r := r₀ * s) (q := r₁ * s)
        (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) (μ.prod ν) 1 :=
      ⟨Kε.toLinearMap, Kε.isPseudodifferentialOperator 1⟩
    let Sε := productCutoffSobolevOperator α hα hαK
      C.cutoff C.smooth_cutoff C.compact_support ε hε
    refine ⟨P, rfl, ?_⟩
    have hreal : P.sobolevRealization A D 1 0 (by norm_num) = O.comp (Sε.comp I) := by
      apply DFunLike.ext'
      apply (A.denseRange_smoothToSobolev 1).equalizer
        (P.sobolevRealization A D 1 0 (by norm_num)).continuous (O.comp (Sε.comp I)).continuous
      funext u
      change P.sobolevRealization A D 1 0 (by norm_num) (A.smoothToSobolev 1 u) =
        O (Sε (I (A.smoothToSobolev 1 u)))
      rw [P.sobolevRealization_smoothToSobolev, hI]
      have hlocal := productCutoffSobolevOperator_apply α hα hαK
        C.cutoff C.smooth_cutoff C.compact_support ε hε
        (K.input.localize K.chart_mem_atlas u)
        (Kε.operator (K.input.localize K.chart_mem_atlas u))
        (fun x ↦ (Kε.operator_apply _ x).symm)
      rw [hlocal, hO]
      rfl
    have hdiff : O.comp (Sε.comp I) - T = O.comp ((Sε - S).comp I) := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [T, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [hreal, hdiff]
    calc
      ‖O.comp ((Sε - S).comp I)‖ ≤ ‖O‖ * (‖Sε - S‖ * ‖I‖) :=
        (O.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
          ((Sε - S).opNorm_comp_le I) (norm_nonneg _))
      _ ≤ ‖O‖ * ((c * ε) * ‖I‖) := by gcongr; exact hbound ε hε hε1
      _ = (‖O‖ * c * ‖I‖) * ε := by ring

end AtiyahSinger
