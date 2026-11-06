/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricRightProductCutoffRealization

/-!
# Geometric approximation of a right-factor PDO piece

Public module ID: M0660.

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

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space N] [T2Space M]
  {F₀ F₁ : N → Type*} {E : M → Type*}
  [∀ y, NormedAddCommGroup (F₀ y)] [∀ y, NormedSpace ℂ (F₀ y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  [∀ y, NormedAddCommGroup (F₁ y)] [∀ y, NormedSpace ℂ (F₁ y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [IsSmoothComplexBundle (n := m) (r := s₁) F₁]
  [∀ y, NormedAddCommGroup (E y)] [∀ y, NormedSpace ℂ (E y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

variable [SecondCountableTopology N] [SecondCountableTopology M]
  [CompactSpace N] [CompactSpace M]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := m) ν] [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1600000 in
-- The original tensor instances recur in both Sobolev extension identities.
/-- The actual tensor cutoff pieces converge in geometric H1-to-H0 norm to their
specified factorwise action on original smooth tensor sections. -/
theorem PseudodifferentialPiece.exists_rightProductCutoff_approximation
    (L : PseudodifferentialPiece (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (hLK : HasCompactSupport L.symbol)
    (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (B C : BundleChartCutoff (r := r) E d) (hCB : C.frame = B.frame) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
    letI := externalTensorTopology (r := r) (s := s₀) E F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
    letI := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
    letI := externalTensorTopology (r := r) (s := s₁) E F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r * s₀) (externalTensorFiber E F₀))
      (D : SmoothBundlePresentation (n := n + m) (r := r * s₁) (externalTensorFiber E F₁)),
      ∃ T : A.SobolevSpace 1 →L[ℂ] D.SobolevSpace 0,
        (∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := m) (r := s₀) F₀),
          T (A.smoothToSobolev 1 (externalTensorSection E F₀ u v)) =
            D.smoothToSobolev 0 (externalTensorSection E F₁
              (C.extend hd (SchwartzMap.smulLeftCLM _ C.cutoff (B.localize hd u)))
              (L.toLinearMap v))) ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
          ∃ P : PseudodifferentialOperator (n := n + m) (r := r * s₀) (q := r * s₁)
              (externalTensorFiber E F₀) (externalTensorFiber E F₁) (μ.prod ν) 1,
            P.toLinearMap = (L.rightProductCutoff hLK d hd B C hCB ε hε).toLinearMap ∧
            ‖P.sobolevRealization A D 1 0 (by norm_num) - T‖ ≤ c * ε := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
  let := externalTensorTopology (r := r) (s := s₀) E F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
  let := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
  let := externalTensorTopology (r := r) (s := s₁) E F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  intro A D
  let K := L.rightProductCutoff hLK d hd B C hCB 1 zero_lt_one
  let α : SymbolFunction m (s₀ * r) (s₁ * r) :=
    fun y ξ ↦ tensorIdentitySymbolMap s₀ s₁ r (L.symbol y ξ)
  have hα : IsSymbol Set.univ 1 α :=
    isSymbol_continuousLinearMap 1 L.symbol L.isSymbol
      ((tensorIdentitySymbolMap s₀ s₁ r).restrictScalars ℝ)
  have hαK : HasCompactSupport α := by
    apply hLK.of_isClosed_subset (isClosed_tsupport α)
    apply closure_minimal ?_ (isClosed_tsupport L.symbol)
    intro y hx
    by_contra h
    have hzero := image_eq_zero_of_notMem_tsupport h
    apply hx
    funext ξ
    change tensorIdentitySymbolMap s₀ s₁ r (L.symbol y ξ) = 0
    rw [hzero]
    exact (tensorIdentitySymbolMap s₀ s₁ r).map_zero
  obtain ⟨S, hS, c, hc, hbound⟩ :=
    exists_rightTensorProductSobolev_approximation L.symbol α hα hαK rfl
      C.cutoff C.smooth_cutoff C.compact_support
  -- Extend the fixed localization and extension maps to their same Bessel coordinates.
  let li := (schwartzSobolevCoordinateLinearMap (n + m) (r * s₀) 1).comp
    (K.input.localizeLinearMap K.chart_mem_atlas)
  obtain ⟨ci, _, hci⟩ := K.input.exists_norm_localize_sobolev_le K.chart_mem_atlas A 1
  let I := li.extendOfNorm (A.smoothToSobolev 1)
  have hI (v : smoothSections (n := n + m) (r := r * s₀) (externalTensorFiber E F₀)) :
      I (A.smoothToSobolev 1 v) =
        schwartzSobolevCoordinate 1 (K.input.localize K.chart_mem_atlas v) :=
    li.extendOfNorm_eq (A.denseRange_smoothToSobolev 1) ⟨ci, hci⟩ v
  let lo := (D.smoothToSobolev 0).comp (K.output.extendLinearMap K.chart_mem_atlas)
  obtain ⟨co, _, hco⟩ := K.output.exists_norm_extend_sobolev_le K.chart_mem_atlas D 0
  let O := lo.extendOfNorm (schwartzSobolevCoordinateLinearMap (n + m) (r * s₁) 0)
  have hO (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s₁)))) :
      O (schwartzSobolevCoordinate 0 w) =
        D.smoothToSobolev 0 (K.output.extend K.chart_mem_atlas w) :=
    lo.extendOfNorm_eq (denseRange_schwartzSobolevCoordinate (n + m) (r * s₁) 0) ⟨co, hco⟩ w
  let T := O.comp (S.comp I)
  refine ⟨T, ?_, ‖O‖ * c * ‖I‖, mul_nonneg (mul_nonneg (norm_nonneg _) hc) (norm_nonneg _), ?_⟩
  · intro u v
    let v₀ := L.input.localize L.chart_mem_atlas v
    let u₀ := B.localize hd u
    let w := K.input.localize K.chart_mem_atlas (externalTensorSection E F₀ u v)
    have hw (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
        (i : Fin r) (j : Fin s₀) :
        w (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (i, j)) =
          u₀ x i * v₀ y j :=
      externalTensorChartCutoff_localizedFunction B L.input u v (x, y) i j
    obtain ⟨z, hz, hSz⟩ := hS u₀ v₀ w hw
    change O (S (I (A.smoothToSobolev 1 (externalTensorSection E F₀ u v)))) = _
    rw [hI, hSz, hO]
    congr 1
    apply Subtype.ext
    funext p
    let v₁ := L.operator v₀
    let u₁ := SchwartzMap.smulLeftCLM _ C.cutoff u₀
    have hu₁ (x : EuclideanSpace ℝ (Fin n)) : u₁ x = C.cutoff x • u₀ x :=
      SchwartzMap.smulLeftCLM_apply_apply
        (C.compact_support.hasTemperateGrowth C.smooth_cutoff) u₀ x
    have hcoord (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
        (i : Fin r) (j : Fin s₁) :
        z (EuclideanSpace.finAddEquivProd.symm p) (finProdFinEquiv (i, j)) =
          u₁ p.1 i * v₁ p.2 j := by
      rw [hz, hu₁]
      change _ = ((C.cutoff p.1 : ℂ) * u₀ p.1 i) * L.operator v₀ p.2 j
      rw [L.operator_apply]
      ring
    exact externalTensorChartCutoff_extendedFunction C L.output u₁ v₁ z hcoord p.1 p.2
  · intro ε hε hε1
    let Kε := L.rightProductCutoff hLK d hd B C hCB ε hε
    let P : PseudodifferentialOperator (n := n + m) (r := r * s₀) (q := r * s₁)
        (externalTensorFiber E F₀) (externalTensorFiber E F₁) (μ.prod ν) 1 :=
      ⟨Kε.toLinearMap, Kε.isPseudodifferentialOperator 1⟩
    let Sε := rightProductCutoffSobolevOperator α hα hαK
      C.cutoff C.smooth_cutoff C.compact_support ε hε
    refine ⟨P, rfl, ?_⟩
    have hreal : P.sobolevRealization A D 1 0 (by norm_num) = O.comp (Sε.comp I) := by
      apply DFunLike.ext'
      apply (A.denseRange_smoothToSobolev 1).equalizer
        (P.sobolevRealization A D 1 0 (by norm_num)).continuous (O.comp (Sε.comp I)).continuous
      funext v
      change P.sobolevRealization A D 1 0 (by norm_num) (A.smoothToSobolev 1 v) =
        O (Sε (I (A.smoothToSobolev 1 v)))
      rw [P.sobolevRealization_smoothToSobolev, hI]
      have hlocal := rightProductCutoffSobolevOperator_apply α hα hαK
        C.cutoff C.smooth_cutoff C.compact_support ε hε
        (K.input.localize K.chart_mem_atlas v)
        (Kε.operator (K.input.localize K.chart_mem_atlas v))
        (fun y ↦ (Kε.operator_apply _ y).symm)
      rw [hlocal, hO]
      rfl
    have hdiff : O.comp (Sε.comp I) - T = O.comp ((Sε - S).comp I) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [T, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [hreal, hdiff]
    calc
      ‖O.comp ((Sε - S).comp I)‖ ≤ ‖O‖ * (‖Sε - S‖ * ‖I‖) :=
        (O.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
          ((Sε - S).opNorm_comp_le I) (norm_nonneg _))
      _ ≤ ‖O‖ * ((c * ε) * ‖I‖) := by gcongr; exact hbound ε hε hε1
      _ = (‖O‖ * c * ‖I‖) * ε := by ring

end AtiyahSinger
