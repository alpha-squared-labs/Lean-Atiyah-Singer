/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricRightTensorFiniteApproximation
public import AtiyahSinger.Analysis.QuantizationFrameTransport
public import AtiyahSinger.Analysis.RightTensorCoefficient
public import AtiyahSinger.Geometry.ProductCovectorCoordinates

/-!
# Exact global symbols of the canonical right tensor cutoffs

Public module ID: M0934.

The actual product PDO pieces have identity tensored with the prescribed
second-factor symbol, multiplied by their original scalar partition and frequency
weights. Both output cutoff factors are retained until the plateau identity
cancels them on the same input support. The equality holds before the principal
quotient and on the original external tensor bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
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

/-- The scalar weight contributed by two fixed canonical quantization patches.
The covectors use the same two tangent inclusions as the native cotangent splitting. -/
def QuantizationPatch.rightProductCutoffWeight
    (A : QuantizationPatch (n := m) (r := s₀) (q := s₁) F₀ F₁)
    (B : QuantizationPatch (n := n) (r := r) (q := r) E E)
    (ε : ℝ) (y : N) (x : M)
    (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) : ℝ :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  A.weight y * B.weight x * productFrequencyCutoff ε
    ‖covectorInChart A.chart y ((ξ.comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))‖
    ‖covectorInChart B.chart x ((ξ.comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))‖

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The two chosen tensor frames are compared with the same original fiber maps.
/-- A canonical product cutoff has the exact globally weighted pure-tensor symbol. -/
theorem QuantizationPatch.globalSymbolFunction_rightProductCutoff
    (A : QuantizationPatch (n := m) (r := s₀) (q := s₁) F₀ F₁)
    (B : QuantizationPatch (n := n) (r := r) (q := r) E E)
    (p : globalSymbolSpace (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (ε : ℝ) (hε : 0 < ε) :
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
    ∀ (y : N) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) (x, y) →L[ℝ] ℝ)
      (v : F₀ y) (u : E x),
      (((A.toPiece p).rightProductCutoff (A.hasCompactSupport_localSymbol p.val)
        B.chart B.chart_mem_atlas B.input B.sameFrameOutput rfl ε hε).globalSymbolFunction
          (x, y) ξ) (u ⊗ₜ[ℂ] v) =
      (A.rightProductCutoffWeight B ε y x ξ : ℂ) •
        (u ⊗ₜ[ℂ]
          p.val y ((ξ.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
              (EuclideanSpace ℝ (Fin m)))) v) := by
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
  intro y x ξ v u
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let q := (B.chart.prod A.chart).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
  let C := externalTensorChartCutoff B.input A.input
  let D := externalTensorChartCutoff B.sameFrameOutput A.output
  let L := (A.toPiece p).rightProductCutoff (A.hasCompactSupport_localSymbol p.val)
    B.chart B.chart_mem_atlas B.input B.sameFrameOutput rfl ε hε
  let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let η₁ := covectorInChart A.chart y ξ₁
  let η₂ := covectorInChart B.chart x ξ₂
  let τ := productFrequencyCutoff ε ‖η₁‖ ‖η₂‖
  let hC := (exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s₀)
    E F₀).choose_spec.choose_spec.2.1 B.input.frame B.input.frame_mem_atlas
      A.input.frame A.input.frame_mem_atlas
  let hD := (exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s₁)
    E F₁).choose_spec.choose_spec.2.1 B.sameFrameOutput.frame B.sameFrameOutput.frame_mem_atlas
      A.output.frame A.output.frame_mem_atlas
  let := A.input.frame_mem_atlas
  let := A.output.frame_mem_atlas
  let := B.input.frame_mem_atlas
  let := C.frame_mem_atlas
  let := D.frame_mem_atlas
  have hCbase : C.frame.baseSet = B.input.frame.baseSet ×ˢ A.input.frame.baseSet :=
    hC.choose_spec.2.1
  have hDbase : D.frame.baseSet = B.input.frame.baseSet ×ˢ A.output.frame.baseSet :=
    hD.choose_spec.2.1
  have hsrc : (x, y) ∈ q.source ↔ y ∈ A.chart.source ∧ x ∈ B.chart.source := by
    simp [q, mfld_simps, and_comm]
  have hq : q (x, y) = e.symm (B.chart x, A.chart y) := rfl
  have hCcut : C.cutoff (q (x, y)) = B.input.cutoff (B.chart x) *
      A.input.cutoff (A.chart y) := by
    change B.input.cutoff (e (q (x, y))).1 * A.input.cutoff (e (q (x, y))).2 = _
    rw [hq, e.apply_symm_apply]
  have hDcut : D.cutoff (q (x, y)) = B.output.cutoff (B.chart x) *
      A.output.cutoff (A.chart y) := by
    change B.output.cutoff (e (q (x, y))).1 * A.output.cutoff (e (q (x, y))).2 = _
    rw [hq, e.apply_symm_apply]
  change L.globalSymbolFunction (x, y) ξ (u ⊗ₜ[ℂ] v) = _
  have hL : L.globalSymbolFunction (x, y) ξ =
      if (x, y) ∈ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet then
        ((D.cutoff (q (x, y)) * C.cutoff (q (x, y)) : ℝ) : ℂ) •
          (D.frame.symmL ℂ (x, y)).comp
            ((L.symbol (q (x, y)) (covectorInChart q (x, y) ξ)).comp
              (C.frame.continuousLinearMapAt ℂ (x, y))) else 0 := rfl
  rw [hL]
  -- Outside either chart, or at a zero input weight, both actual symbols vanish.
  by_cases hy : y ∈ A.chart.source
  · by_cases hx : x ∈ B.chart.source
    · by_cases ha : A.input.cutoff (A.chart y) = 0
      · simp only [hCcut, ha, mul_zero, Complex.ofReal_zero, zero_smul,
          ite_self, zero_apply]
        simp [QuantizationPatch.rightProductCutoffWeight, QuantizationPatch.weight, hy, ha]
      by_cases hb : B.input.cutoff (B.chart x) = 0
      · simp only [hCcut, hb, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul,
          ite_self, zero_apply]
        simp [QuantizationPatch.rightProductCutoffWeight, QuantizationPatch.weight, hx, hb]
      have haS := subset_tsupport _ ha
      have hbS := subset_tsupport _ hb
      have ha₀ : y ∈ A.input.frame.baseSet := by
        simpa only [Set.mem_preimage, A.chart.left_inv hy] using (A.input.support_subset haS).2
      have ha₁ : y ∈ A.output.frame.baseSet := by
        simpa only [Set.mem_preimage, A.chart.left_inv hy] using
          A.input_support_in_output_frame haS
      have hb₀ : x ∈ B.input.frame.baseSet := by
        simpa only [Set.mem_preimage, B.chart.left_inv hx] using (B.input.support_subset hbS).2
      have hcF : (x, y) ∈ C.frame.baseSet := by rw [hCbase]; exact ⟨hb₀, ha₀⟩
      have hdF : (x, y) ∈ D.frame.baseSet := by rw [hDbase]; exact ⟨hb₀, ha₁⟩
      have hdomain : A.chart y ∈ symbolChartDomain F₀ F₁ A.chart A.input.frame
          A.output.frame := by
        exact ⟨⟨A.chart.map_source hy,
          by simpa only [Set.mem_preimage, A.chart.left_inv hy] using ha₀⟩,
          by simpa only [Set.mem_preimage, A.chart.left_inv hy] using ha₁⟩
      have hvalid : (x, y) ∈ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet :=
        ⟨⟨hsrc.mpr ⟨hy, hx⟩, hcF⟩, hdF⟩
      have hfreq : e (covectorInChart q (x, y) ξ) = (η₂, η₁) :=
        covectorInChart_product B.chart B.chart_mem_atlas A.chart A.chart_mem_atlas x y hx hy ξ
      have hlocal : A.localSymbol p.val (A.chart y) η₁ =
          (A.output.frame.continuousLinearMapAt ℂ y).comp
            ((p.val y ξ₁).comp (A.input.frame.symmL ℂ y)) := by
        dsimp only [QuantizationPatch.localSymbol, zeroExtendedSymbol]
        rw [ite_eq_left hdomain, A.output_eq_one _ haS, Complex.ofReal_one, one_smul]
        exact globalSymbolInChart_covectorInChart F₀ F₁ p.val A.chart A.chart_mem_atlas
          A.input.frame A.output.frame y hy ξ₁
      have hs : L.symbol (q (x, y)) (covectorInChart q (x, y) ξ) =
          (τ : ℂ) • identityTensorSymbolMap r s₀ s₁
            (A.localSymbol p.val (A.chart y) η₁) := by
        have hη : covectorInChart q (x, y) ξ = e.symm (η₂, η₁) := by
          apply e.injective
          rw [hfreq, e.apply_symm_apply]
        change rightProductCutoffSymbol
          (fun y η ↦ tensorIdentitySymbolMap s₀ s₁ r (A.localSymbol p.val y η))
          B.output.cutoff ε (q (x, y)) (covectorInChart q (x, y) ξ) = _
        rw [hq, hη, rightProductCutoffSymbol_eq, B.output_eq_one _ hbS]
        simp only [Complex.ofReal_one, one_smul, τ]
      -- The exact selected tensor frames conjugate the coefficient map to identity tensor p.
      have hmatrix : D.frame.symmL ℂ (x, y)
          (identityTensorSymbolMap r s₀ s₁ (A.localSymbol p.val (A.chart y) η₁)
            (C.frame.continuousLinearMapAt ℂ (x, y) (u ⊗ₜ[ℂ] v))) =
          u ⊗ₜ[ℂ] p.val y ξ₁ v := by
        have hw (i : Fin r) (j : Fin s₀) :
            (C.frame.continuousLinearMapAt ℂ (x, y) (u ⊗ₜ[ℂ] v))
              (finProdFinEquiv (i, j)) =
            (B.input.frame.continuousLinearMapAt ℂ x u) i *
              (A.input.frame.continuousLinearMapAt ℂ y v) j := by
          rw [C.frame.continuousLinearMapAt_apply_of_mem ℂ hcF]
          change (hC.choose ⟨(x, y), u ⊗ₜ[ℂ] v⟩).2 (finProdFinEquiv (i, j)) = _
          rw [hC.choose_spec.2.2 (x, y) ⟨hb₀, ha₀⟩]
          rw [A.input.frame.continuousLinearMapAt_apply_of_mem ℂ ha₀,
            B.input.frame.continuousLinearMapAt_apply_of_mem ℂ hb₀]
        apply (D.frame.linearEquivAt ℂ (x, y) hdF).injective
        change (D.frame ⟨(x, y), D.frame.symmL ℂ (x, y) _⟩).2 =
          (D.frame ⟨(x, y), u ⊗ₜ[ℂ] p.val y ξ₁ v⟩).2
        rw [D.frame.symmL_apply hdF, D.frame.apply_mk_symm hdF]
        apply PiLp.ext
        intro k
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        rw [identityTensorSymbolMap_apply _ _ _ _ hw]
        change _ = (hD.choose ⟨(x, y), u ⊗ₜ[ℂ] p.val y ξ₁ v⟩).2
          (finProdFinEquiv (i, j))
        rw [hD.choose_spec.2.2 (x, y) ⟨hb₀, ha₁⟩, hlocal]
        simp only [ContinuousLinearMap.comp_apply]
        rw [A.input.frame.symmL_continuousLinearMapAt ha₀]
        rw [A.output.frame.continuousLinearMapAt_apply_of_mem ℂ ha₁,
          B.input.frame.continuousLinearMapAt_apply_of_mem ℂ hb₀]
        rfl
      -- Both output cutoffs equal one on this very input support.
      simp only [ite_eq_left hvalid, hCcut, hDcut, A.output_eq_one _ haS,
        B.output_eq_one _ hbS, one_mul, hs, smul_apply, ContinuousLinearMap.comp_apply,
        map_smul, hmatrix]
      rw [smul_smul, ← Complex.ofReal_mul]
      simp only [QuantizationPatch.rightProductCutoffWeight, QuantizationPatch.weight,
        ite_eq_left hy, ite_eq_left hx]
      congr 1
      change ((B.input.cutoff (B.chart x) * A.input.cutoff (A.chart y) * τ : ℝ) : ℂ) =
        ((A.input.cutoff (A.chart y) * B.input.cutoff (B.chart x) * τ : ℝ) : ℂ)
      congr 1
      ring
    · have hnot : (x, y) ∉ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet :=
        fun h ↦ hx (hsrc.mp h.1.1).2
      simp only [ite_eq_right hnot, zero_apply]
      simp [QuantizationPatch.rightProductCutoffWeight, QuantizationPatch.weight, hx]
  · have hnot : (x, y) ∉ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet :=
      fun h ↦ hy (hsrc.mp h.1.1).1
    simp only [ite_eq_right hnot, zero_apply]
    simp [QuantizationPatch.rightProductCutoffWeight, QuantizationPatch.weight, hy]


/-- The canonical finite cutoff sum has one scalar atlas weight times the given symbol. -/
theorem QuantizationPresentation.globalSymbolFunction_sum_rightProductCutoff
    (A : QuantizationPresentation (n := m) (r := s₀) (q := s₁) F₀ F₁)
    (B : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (p : globalSymbolSpace (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (ε : ℝ) (hε : 0 < ε) :
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
    ∀ (y : N) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) (x, y) →L[ℝ] ℝ)
      (v : F₀ y) (u : E x),
      ((∑ j, ∑ i, (((A.patch j).toPiece p).rightProductCutoff
        ((A.patch j).hasCompactSupport_localSymbol p.val) (B.patch i).chart
        (B.patch i).chart_mem_atlas (B.patch i).input (B.patch i).sameFrameOutput
        rfl ε hε).globalSymbolFunction) (x, y) ξ) (u ⊗ₜ[ℂ] v) =
      ((∑ j, ∑ i, (A.patch j).rightProductCutoffWeight (B.patch i) ε y x ξ : ℝ) : ℂ) •
        (u ⊗ₜ[ℂ]
          p.val y ((ξ.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
              (EuclideanSpace ℝ (Fin m)))) v) := by
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
  intro y x ξ v u
  -- Every term recovers the same p; only its original scalar weight varies.
  simp only [Finset.sum_apply, sum_apply, QuantizationPatch.globalSymbolFunction_rightProductCutoff]
  simp only [Complex.ofReal_sum, Finset.sum_smul]

end AtiyahSinger
