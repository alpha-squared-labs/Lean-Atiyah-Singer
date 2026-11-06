/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorH1Energy
public import AtiyahSinger.Analysis.MetricSobolevParametrix

/-!
# Elliptic control of geometric product H1 on finite smooth tensors

Public module ID: M0609.

The factor parametrices act boundedly on the actual metric L2 Hilbert tensor
spaces. Their reconstruction identities control both mixed Sobolev norms.
The exact product energy then controls the original geometric H1 norm, for
any presentation. This is the anisotropic estimate needed before the graded
cross terms cancel; it does not assert isotropic PDO structure for a partial action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {n m r₀ r₁ s₀ s₁ : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hTM : T2Space M] [hTN : T2Space N]
  [hSCM : SecondCountableTopology M] [hSCN : SecondCountableTopology N]
  [hCM : CompactSpace M] [hCN : CompactSpace N]
  [MeasurableSpace M] [hBM : BorelSpace M]
  [MeasurableSpace N] [hBN : BorelSpace N]
  {μ : Measure M} {ν : Measure N}
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := m) ν]
  {E₀ : M → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [hE₀ : IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  {E₁ : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [hE₁ : IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  {F₀ : N → Type*}
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, NormedSpace ℂ (F₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [hF₀ : IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  {F₁ : N → Type*}
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [hF₁ : IsSmoothComplexBundle (n := m) (r := s₁) F₁]

include hM hN hTM hTN hSCM hSCN hCM hCN hBM hBN hμ hν hE₀ hE₁ hF₀ hF₁

variable (h₀ : SmoothHermitianMetric (n := n) (r := r₀) E₀)
  (h₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
  (k₀ : SmoothHermitianMetric (n := m) (r := s₀) F₀)
  (k₁ : SmoothHermitianMetric (n := m) (r := s₁) F₁)
  (P : PseudodifferentialOperator (n := n) (r := r₀) (q := r₁) E₀ E₁ μ 1)
  (Q : PseudodifferentialOperator (n := m) (r := s₀) (q := s₁) F₀ F₁ ν 1)

set_option maxHeartbeats 1500000 in
-- Apply the two factor parametrices on the original mixed tensor spaces.
/-- Factor ellipticity controls the geometric H1 norm of every finite smooth tensor sum. -/
theorem exists_externalTensorH1_elliptic_estimate (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorTopology (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
    ∀ (A : SmoothBundlePresentation (n := n + m) (r := r₀ * s₀)
        (externalTensorFiber E₀ F₀))
      (U : smoothSections (n := n) (r := r₀) E₀ ⊗[ℂ]
          smoothSections (n := m) (r := s₀) F₀ →ₗ[ℂ] A.SobolevSpace 1),
      (∀ u v, U (u ⊗ₜ[ℂ] v) = A.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v)) →
    ∃ C : ℝ, 0 < C ∧ ∀ z,
      ‖U z‖ ≤ C *
        (‖TensorProduct.map (h₀.smoothToL2 μ) (k₀.smoothToL2 ν) z‖ +
          ‖TensorProduct.map ((h₁.smoothToL2 μ).comp P.toLinearMap) (k₀.smoothToL2 ν) z‖ +
          ‖TensorProduct.map (h₀.smoothToL2 μ) ((k₁.smoothToL2 ν).comp Q.toLinearMap) z‖) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberNormedSpace (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorTopology (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s₀) E₀ F₀
  intro A U hU
  let A₀ := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r₀) E₀)
  let A₁ := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r₁) E₁)
  let B₀ := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s₀) F₀)
  let B₁ := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s₁) F₁)
  let C := externalTensorPresentation A₀ B₀
  let e := A.sobolevEquiv C 1
  let T := e.toLinearMap.comp U
  let SE := smoothSections (n := n) (r := r₀) E₀
  let SF := smoothSections (n := m) (r := s₀) F₀
  let J (a b : ℝ) : SE ⊗[ℂ] SF →ₗ[ℂ] A₀.SobolevSpace a ⊗[ℂ] B₀.SobolevSpace b :=
    TensorProduct.map (A₀.smoothToSobolev a) (B₀.smoothToSobolev b)
  have hT (u : SE) (v : SF) :
      T (u ⊗ₜ[ℂ] v) = C.smoothToSobolev 1 (externalTensorSection E₀ F₀ u v) := by
    change e (U (u ⊗ₜ[ℂ] v)) = _
    rw [hU]
    exact A.sobolevEquiv_smoothToSobolev C 1 _
  have hJ (a b : ℝ) (u : SE) (v : SF) :
      J a b (u ⊗ₜ[ℂ] v) = A₀.smoothToSobolev a u ⊗ₜ[ℂ] B₀.smoothToSobolev b v := rfl
  -- The exact finite-sum product energy compares the geometric and mixed norms.
  have hpure (u u' : SE) (v v' : SF) :
      inner ℂ (T (u ⊗ₜ[ℂ] v)) (T (u' ⊗ₜ[ℂ] v')) =
        inner ℂ (J 1 0 (u ⊗ₜ[ℂ] v)) (J 1 0 (u' ⊗ₜ[ℂ] v')) +
        inner ℂ (J 0 1 (u ⊗ₜ[ℂ] v)) (J 0 1 (u' ⊗ₜ[ℂ] v')) -
        inner ℂ (J 0 0 (u ⊗ₜ[ℂ] v)) (J 0 0 (u' ⊗ₜ[ℂ] v')) := by
    simp only [hT, hJ, TensorProduct.inner_tmul]
    exact inner_smoothToSobolev_one_externalTensor A₀ B₀ u u' v v'
  have hinner (x y : SE ⊗[ℂ] SF) :
      inner ℂ (T x) (T y) = inner ℂ (J 1 0 x) (J 1 0 y) +
        inner ℂ (J 0 1 x) (J 0 1 y) - inner ℂ (J 0 0 x) (J 0 0 y) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      induction y using TensorProduct.inductionOn with
      | tmul u' v' => exact hpure u u' v v'
      | add x y hx hy =>
        simp only [map_add, inner_add_right, hx, hy]
        ring
    | add x y hx hy =>
      simp only [map_add, inner_add_left, hx, hy]
      ring
  have henergy (z : SE ⊗[ℂ] SF) :
      ‖T z‖ ^ 2 = ‖J 1 0 z‖ ^ 2 + ‖J 0 1 z‖ ^ 2 - ‖J 0 0 z‖ ^ 2 := by
    have ht := congrArg Complex.re (hinner z z)
    have hTnorm : (inner ℂ (T z) (T z)).re = ‖T z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (T z)
    have h10 : (inner ℂ (J 1 0 z) (J 1 0 z)).re = ‖J 1 0 z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (J 1 0 z)
    have h01 : (inner ℂ (J 0 1 z) (J 0 1 z)).re = ‖J 0 1 z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (J 0 1 z)
    have h00 : (inner ℂ (J 0 0 z) (J 0 0 z)).re = ‖J 0 0 z‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (J 0 0 z)
    simpa only [Complex.add_re, Complex.sub_re, hTnorm, h10, h01, h00] using ht
  -- Actual bounded parametrix maps can be amplified, including all finite tensor sums.
  obtain ⟨RP, SP, hPsplit⟩ := P.exists_metricSobolev_left_parametrix h₀ h₁ hP A₀ A₁
  obtain ⟨RQ, SQ, hQsplit⟩ := Q.exists_metricSobolev_left_parametrix k₀ k₁ hQ B₀ B₁
  let e₀ := h₀.sobolevZeroEquivL2 (μ := μ) A₀
  let f₀ := k₀.sobolevZeroEquivL2 (μ := ν) B₀
  have he₀ (u : SE) : e₀.symm (h₀.smoothToL2 μ u) = A₀.smoothToSobolev 0 u := by
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    exact (h₀.sobolevZeroEquivL2_smooth A₀ u).symm
  have hf₀ (v : SF) : f₀.symm (k₀.smoothToL2 ν v) = B₀.smoothToSobolev 0 v := by
    apply f₀.injective
    rw [f₀.apply_symm_apply]
    exact (k₀.sobolevZeroEquivL2_smooth B₀ v).symm
  let I₀ := TensorProduct.map (h₀.smoothToL2 μ) (k₀.smoothToL2 ν)
  let IP := TensorProduct.map ((h₁.smoothToL2 μ).comp P.toLinearMap) (k₀.smoothToL2 ν)
  let IQ := TensorProduct.map (h₀.smoothToL2 μ) ((k₁.smoothToL2 ν).comp Q.toLinearMap)
  let LP := TensorProduct.mapL RP f₀.symm.toContinuousLinearMap
  let KP := TensorProduct.mapL SP f₀.symm.toContinuousLinearMap
  let LQ := TensorProduct.mapL e₀.symm.toContinuousLinearMap RQ
  let KQ := TensorProduct.mapL e₀.symm.toContinuousLinearMap SQ
  have hleft (z : SE ⊗[ℂ] SF) : J 1 0 z = LP (IP z) + KP (I₀ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [hJ, LP, KP, IP, I₀, TensorProduct.map_tmul, TensorProduct.mapL_tmul,
        LinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hf₀]
      rw [hPsplit, TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  have hright (z : SE ⊗[ℂ] SF) : J 0 1 z = LQ (IQ z) + KQ (I₀ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [hJ, LQ, KQ, IQ, I₀, TensorProduct.map_tmul, TensorProduct.mapL_tmul,
        LinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, he₀]
      rw [hQsplit, TensorProduct.tmul_add]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  let D := ‖LP‖ + ‖KP‖ + ‖LQ‖ + ‖KQ‖
  have hD : 0 ≤ D := by positivity
  refine ⟨‖e.symm.toContinuousLinearMap‖ * D + 1, by positivity, ?_⟩
  intro z
  have hmixed : ‖T z‖ ≤ ‖J 1 0 z‖ + ‖J 0 1 z‖ := by
    have hh := henergy z
    nlinarith [norm_nonneg (T z), norm_nonneg (J 1 0 z), norm_nonneg (J 0 1 z),
      sq_nonneg ‖J 0 0 z‖, mul_nonneg (norm_nonneg (J 1 0 z)) (norm_nonneg (J 0 1 z))]
  have hl : ‖J 1 0 z‖ ≤ ‖LP‖ * ‖IP z‖ + ‖KP‖ * ‖I₀ z‖ := by
    rw [hleft]
    exact (norm_add_le _ _).trans (add_le_add (LP.le_opNorm _) (KP.le_opNorm _))
  have hr : ‖J 0 1 z‖ ≤ ‖LQ‖ * ‖IQ z‖ + ‖KQ‖ * ‖I₀ z‖ := by
    rw [hright]
    exact (norm_add_le _ _).trans (add_le_add (LQ.le_opNorm _) (KQ.le_opNorm _))
  let b := ‖I₀ z‖ + ‖IP z‖ + ‖IQ z‖
  have h0b : ‖I₀ z‖ ≤ b := by
    dsimp [b]
    linarith [norm_nonneg (I₀ z), norm_nonneg (IP z), norm_nonneg (IQ z)]
  have hPb : ‖IP z‖ ≤ b := by
    dsimp [b]
    linarith [norm_nonneg (I₀ z), norm_nonneg (IP z), norm_nonneg (IQ z)]
  have hQb : ‖IQ z‖ ≤ b := by
    dsimp [b]
    linarith [norm_nonneg (I₀ z), norm_nonneg (IP z), norm_nonneg (IQ z)]
  have hTb : ‖T z‖ ≤ D * b := by
    calc
      ‖T z‖ ≤ ‖J 1 0 z‖ + ‖J 0 1 z‖ := hmixed
      _ ≤ (‖LP‖ * ‖IP z‖ + ‖KP‖ * ‖I₀ z‖) +
          (‖LQ‖ * ‖IQ z‖ + ‖KQ‖ * ‖I₀ z‖) := add_le_add hl hr
      _ ≤ (‖LP‖ * b + ‖KP‖ * b) + (‖LQ‖ * b + ‖KQ‖ * b) :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hPb (norm_nonneg _))
            (mul_le_mul_of_nonneg_left h0b (norm_nonneg _)))
          (add_le_add (mul_le_mul_of_nonneg_left hQb (norm_nonneg _))
            (mul_le_mul_of_nonneg_left h0b (norm_nonneg _)))
      _ = D * b := by dsimp [D]; ring
  have hUbound : ‖U z‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖T z‖ := by
    have hi : e.symm (T z) = U z := e.symm_apply_apply _
    exact hi ▸ e.symm.toContinuousLinearMap.le_opNorm (T z)
  change ‖U z‖ ≤ (‖e.symm.toContinuousLinearMap‖ * D + 1) * b
  calc
    ‖U z‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖T z‖ := hUbound
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (D * b) :=
      mul_le_mul_of_nonneg_left hTb (norm_nonneg _)
    _ ≤ (‖e.symm.toContinuousLinearMap‖ * D + 1) * b := by
      have hb : 0 ≤ b := by positivity
      nlinarith

end AtiyahSinger
