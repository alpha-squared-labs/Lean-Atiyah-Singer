/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricTensorFiniteApproximation
public import AtiyahSinger.Analysis.QuantizationFrameTransport
public import AtiyahSinger.Geometry.ProductCovectorCoordinates

/-!
# Exact global symbols of the canonical tensor cutoffs

Public module ID: M1033.

The actual product PDO pieces have the prescribed first-factor symbol tensored
with the identity, multiplied by their original scalar partition and frequency
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

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
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

/-- The scalar weight contributed by two fixed canonical quantization patches.
The covectors use the same two tangent inclusions as the native cotangent splitting. -/
def QuantizationPatch.productCutoffWeight
    (A : QuantizationPatch (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPatch (n := m) (r := s) (q := s) F F)
    (ε : ℝ) (x : M) (y : N)
    (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) : ℝ :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  A.weight x * B.weight y * productFrequencyCutoff ε
    ‖covectorInChart A.chart x ((ξ.comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))‖
    ‖covectorInChart B.chart y ((ξ.comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))‖

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The two chosen tensor frames are compared with the same original fiber maps.
/-- A canonical product cutoff has the exact globally weighted pure-tensor symbol. -/
theorem QuantizationPatch.globalSymbolFunction_productCutoff
    (A : QuantizationPatch (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPatch (n := m) (r := s) (q := s) F F)
    (p : globalSymbolSpace (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (ε : ℝ) (hε : 0 < ε) :
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
    ∀ (x : M) (y : N)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) (x, y) →L[ℝ] ℝ)
      (u : E₀ x) (v : F y),
      (((A.toPiece p).productCutoff (A.hasCompactSupport_localSymbol p.val)
        B.chart B.chart_mem_atlas B.input B.sameFrameOutput rfl ε hε).globalSymbolFunction
          (x, y) ξ) (u ⊗ₜ[ℂ] v) =
      (A.productCutoffWeight B ε x y ξ : ℂ) •
        (p.val x ((ξ.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))) u
            ⊗ₜ[ℂ] v) := by
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
  intro x y ξ u v
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let q := (A.chart.prod B.chart).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
  let C := externalTensorChartCutoff A.input B.input
  let D := externalTensorChartCutoff A.output B.sameFrameOutput
  let L := (A.toPiece p).productCutoff (A.hasCompactSupport_localSymbol p.val)
    B.chart B.chart_mem_atlas B.input B.sameFrameOutput rfl ε hε
  let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let η₁ := covectorInChart A.chart x ξ₁
  let η₂ := covectorInChart B.chart y ξ₂
  let τ := productFrequencyCutoff ε ‖η₁‖ ‖η₂‖
  let hC := (exists_externalTensorBundle (n := n) (m := m) (r := r₀) (s := s)
    E₀ F).choose_spec.choose_spec.2.1 A.input.frame A.input.frame_mem_atlas
      B.input.frame B.input.frame_mem_atlas
  let hD := (exists_externalTensorBundle (n := n) (m := m) (r := r₁) (s := s)
    E₁ F).choose_spec.choose_spec.2.1 A.output.frame A.output.frame_mem_atlas
      B.sameFrameOutput.frame B.sameFrameOutput.frame_mem_atlas
  let := A.input.frame_mem_atlas
  let := A.output.frame_mem_atlas
  let := B.input.frame_mem_atlas
  let := C.frame_mem_atlas
  let := D.frame_mem_atlas
  have hCbase : C.frame.baseSet = A.input.frame.baseSet ×ˢ B.input.frame.baseSet :=
    hC.choose_spec.2.1
  have hDbase : D.frame.baseSet = A.output.frame.baseSet ×ˢ B.input.frame.baseSet :=
    hD.choose_spec.2.1
  have hsrc : (x, y) ∈ q.source ↔ x ∈ A.chart.source ∧ y ∈ B.chart.source := by
    simp [q, mfld_simps]
  have hq : q (x, y) = e.symm (A.chart x, B.chart y) := rfl
  have hCcut : C.cutoff (q (x, y)) = A.input.cutoff (A.chart x) *
      B.input.cutoff (B.chart y) := by
    change A.input.cutoff (e (q (x, y))).1 * B.input.cutoff (e (q (x, y))).2 = _
    rw [hq, e.apply_symm_apply]
  have hDcut : D.cutoff (q (x, y)) = A.output.cutoff (A.chart x) *
      B.output.cutoff (B.chart y) := by
    change A.output.cutoff (e (q (x, y))).1 * B.output.cutoff (e (q (x, y))).2 = _
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
  by_cases hx : x ∈ A.chart.source
  · by_cases hy : y ∈ B.chart.source
    · by_cases ha : A.input.cutoff (A.chart x) = 0
      · simp only [hCcut, ha, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul,
          ite_self, zero_apply]
        simp [QuantizationPatch.productCutoffWeight, QuantizationPatch.weight, hx, ha]
      by_cases hb : B.input.cutoff (B.chart y) = 0
      · simp only [hCcut, hb, mul_zero, Complex.ofReal_zero, zero_smul,
          ite_self, zero_apply]
        simp [QuantizationPatch.productCutoffWeight, QuantizationPatch.weight, hy, hb]
      have haS := subset_tsupport _ ha
      have hbS := subset_tsupport _ hb
      have ha₀ : x ∈ A.input.frame.baseSet := by
        simpa only [Set.mem_preimage, A.chart.left_inv hx] using (A.input.support_subset haS).2
      have ha₁ : x ∈ A.output.frame.baseSet := by
        simpa only [Set.mem_preimage, A.chart.left_inv hx] using
          A.input_support_in_output_frame haS
      have hb₀ : y ∈ B.input.frame.baseSet := by
        simpa only [Set.mem_preimage, B.chart.left_inv hy] using (B.input.support_subset hbS).2
      have hcF : (x, y) ∈ C.frame.baseSet := by rw [hCbase]; exact ⟨ha₀, hb₀⟩
      have hdF : (x, y) ∈ D.frame.baseSet := by rw [hDbase]; exact ⟨ha₁, hb₀⟩
      have hdomain : A.chart x ∈ symbolChartDomain E₀ E₁ A.chart A.input.frame
          A.output.frame := by
        exact ⟨⟨A.chart.map_source hx,
          by simpa only [Set.mem_preimage, A.chart.left_inv hx] using ha₀⟩,
          by simpa only [Set.mem_preimage, A.chart.left_inv hx] using ha₁⟩
      have hvalid : (x, y) ∈ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet :=
        ⟨⟨hsrc.mpr ⟨hx, hy⟩, hcF⟩, hdF⟩
      have hfreq : e (covectorInChart q (x, y) ξ) = (η₁, η₂) :=
        covectorInChart_product A.chart A.chart_mem_atlas B.chart B.chart_mem_atlas x y hx hy ξ
      have hlocal : A.localSymbol p.val (A.chart x) η₁ =
          (A.output.frame.continuousLinearMapAt ℂ x).comp
            ((p.val x ξ₁).comp (A.input.frame.symmL ℂ x)) := by
        dsimp only [QuantizationPatch.localSymbol, zeroExtendedSymbol]
        rw [ite_eq_left hdomain, A.output_eq_one _ haS, Complex.ofReal_one, one_smul]
        exact globalSymbolInChart_covectorInChart E₀ E₁ p.val A.chart A.chart_mem_atlas
          A.input.frame A.output.frame x hx ξ₁
      have hs : L.symbol (q (x, y)) (covectorInChart q (x, y) ξ) =
          (τ : ℂ) • tensorIdentitySymbolMap r₀ r₁ s
            (A.localSymbol p.val (A.chart x) η₁) := by
        change (productFrequencyCutoff ε ‖(e (covectorInChart q (x, y) ξ)).1‖
          ‖(e (covectorInChart q (x, y) ξ)).2‖ : ℂ) •
          ((B.output.cutoff (e (q (x, y))).2 : ℂ) •
            tensorIdentitySymbolMap r₀ r₁ s
              (A.localSymbol p.val (e (q (x, y))).1
                (e (covectorInChart q (x, y) ξ)).1)) = _
        rw [hfreq, hq, e.apply_symm_apply, B.output_eq_one _ hbS]
        simp only [Complex.ofReal_one, one_smul, τ]
      -- The exact selected tensor frames conjugate the coefficient map to p tensor identity.
      have hmatrix : D.frame.symmL ℂ (x, y)
          (tensorIdentitySymbolMap r₀ r₁ s (A.localSymbol p.val (A.chart x) η₁)
            (C.frame.continuousLinearMapAt ℂ (x, y) (u ⊗ₜ[ℂ] v))) =
          p.val x ξ₁ u ⊗ₜ[ℂ] v := by
        have hw (i : Fin r₀) (j : Fin s) :
            (C.frame.continuousLinearMapAt ℂ (x, y) (u ⊗ₜ[ℂ] v))
              (finProdFinEquiv (i, j)) =
            (A.input.frame.continuousLinearMapAt ℂ x u) i *
              (B.input.frame.continuousLinearMapAt ℂ y v) j := by
          rw [C.frame.continuousLinearMapAt_apply_of_mem ℂ hcF]
          change (hC.choose ⟨(x, y), u ⊗ₜ[ℂ] v⟩).2 (finProdFinEquiv (i, j)) = _
          rw [hC.choose_spec.2.2 (x, y) ⟨ha₀, hb₀⟩]
          rw [A.input.frame.continuousLinearMapAt_apply_of_mem ℂ ha₀,
            B.input.frame.continuousLinearMapAt_apply_of_mem ℂ hb₀]
        apply (D.frame.linearEquivAt ℂ (x, y) hdF).injective
        change (D.frame ⟨(x, y), D.frame.symmL ℂ (x, y) _⟩).2 =
          (D.frame ⟨(x, y), p.val x ξ₁ u ⊗ₜ[ℂ] v⟩).2
        rw [D.frame.symmL_apply hdF, D.frame.apply_mk_symm hdF]
        apply PiLp.ext
        intro k
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        rw [tensorIdentitySymbolMap_apply _ _ _ _ hw]
        change _ = (hD.choose ⟨(x, y), p.val x ξ₁ u ⊗ₜ[ℂ] v⟩).2
          (finProdFinEquiv (i, j))
        rw [hD.choose_spec.2.2 (x, y) ⟨ha₁, hb₀⟩, hlocal]
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
      simp only [QuantizationPatch.productCutoffWeight, QuantizationPatch.weight,
        ite_eq_left hx, ite_eq_left hy]
      rfl
    · have hnot : (x, y) ∉ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet :=
        fun h ↦ hy (hsrc.mp h.1.1).2
      simp only [ite_eq_right hnot, zero_apply]
      simp [QuantizationPatch.productCutoffWeight, QuantizationPatch.weight, hy]
  · have hnot : (x, y) ∉ q.source ∩ C.frame.baseSet ∩ D.frame.baseSet :=
      fun h ↦ hx (hsrc.mp h.1.1).1
    simp only [ite_eq_right hnot, zero_apply]
    simp [QuantizationPatch.productCutoffWeight, QuantizationPatch.weight, hx]


/-- The canonical finite cutoff sum has one scalar atlas weight times the given symbol. -/
theorem QuantizationPresentation.globalSymbolFunction_sum_productCutoff
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (p : globalSymbolSpace (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (ε : ℝ) (hε : 0 < ε) :
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
    ∀ (x : M) (y : N)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) (x, y) →L[ℝ] ℝ)
      (u : E₀ x) (v : F y),
      ((∑ i, ∑ j, (((A.patch i).toPiece p).productCutoff
        ((A.patch i).hasCompactSupport_localSymbol p.val) (B.patch j).chart
        (B.patch j).chart_mem_atlas (B.patch j).input (B.patch j).sameFrameOutput
        rfl ε hε).globalSymbolFunction) (x, y) ξ) (u ⊗ₜ[ℂ] v) =
      ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
        (p.val x ((ξ.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))) u
            ⊗ₜ[ℂ] v) := by
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
  intro x y ξ u v
  -- Every term recovers the same p; only its original scalar weight varies.
  simp only [Finset.sum_apply, sum_apply, QuantizationPatch.globalSymbolFunction_productCutoff]
  simp only [Complex.ofReal_sum, Finset.sum_smul]

end AtiyahSinger
