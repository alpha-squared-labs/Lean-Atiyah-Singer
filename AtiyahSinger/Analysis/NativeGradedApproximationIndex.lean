/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasGradedCompactApproximationIndex
public import AtiyahSinger.Analysis.NativeGradedPairedLimit

/-!
# The native graded index from four paired corner approximations

Public module ID: M0809.

The original atlas Sobolev realizations, native sum coordinates and four paired
corner limits are fixed. Their signed residuals and literal residual adjoints
correct the same native forward and reverse families. The completed graded
matrices use those same eight corners and four domain inclusions.

The graph estimates and cross-pairing identities compare these limits with the
specified closed operators. Their graph closures, formal adjunction, closed
ranges and finite kernels are hypotheses. Both native families are eventually
Fredholm, and their eventual index sum is assumed to vanish. Under these
conditions, the forward index eventually equals the difference of the two
specified kernel dimensions, with every native coordinate and sign retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E₀₀ : M → Type*} [∀ x, AddCommGroup (E₀₀ x)] [∀ x, Module ℂ (E₀₀ x)]
  [TopologicalSpace (TotalSpace Unit E₀₀)]
  {X₀₀ : Type*} [NormedAddCommGroup X₀₀] [InnerProductSpace ℂ X₀₀]
  [CompleteSpace X₀₀]
  {E₁₀ : M → Type*} [∀ x, AddCommGroup (E₁₀ x)] [∀ x, Module ℂ (E₁₀ x)]
  [TopologicalSpace (TotalSpace Unit E₁₀)]
  {X₁₀ : Type*} [NormedAddCommGroup X₁₀] [InnerProductSpace ℂ X₁₀]
  [CompleteSpace X₁₀]
  {E₀₁ : M → Type*} [∀ x, AddCommGroup (E₀₁ x)] [∀ x, Module ℂ (E₀₁ x)]
  [TopologicalSpace (TotalSpace Unit E₀₁)]
  {X₀₁ : Type*} [NormedAddCommGroup X₀₁] [InnerProductSpace ℂ X₀₁]
  [CompleteSpace X₀₁]
  {E₁₁ : M → Type*} [∀ x, AddCommGroup (E₁₁ x)] [∀ x, Module ℂ (E₁₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁₁)]
  {X₁₁ : Type*} [NormedAddCommGroup X₁₁] [InnerProductSpace ℂ X₁₁]
  [CompleteSpace X₁₁]

variable {S₀₀ S₁₀ S₀₁ S₁₁ Nplus Nminus : Type*}
  [AddCommGroup S₀₀] [Module ℂ S₀₀] [AddCommGroup S₁₀] [Module ℂ S₁₀]
  [AddCommGroup S₀₁] [Module ℂ S₀₁] [AddCommGroup S₁₁] [Module ℂ S₁₁]
  [AddCommGroup Nplus] [Module ℂ Nplus] [AddCommGroup Nminus] [Module ℂ Nminus]
  {Dplus Dminus Xplus Xminus : Type*}
  [NormedAddCommGroup Dplus] [NormedSpace ℂ Dplus]
  [NormedAddCommGroup Dminus] [NormedSpace ℂ Dminus]
  [NormedAddCommGroup Xplus] [NormedSpace ℂ Xplus]
  [NormedAddCommGroup Xminus] [NormedSpace ℂ Xminus]

omit [CompactSpace M] in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the specified Fredholm graphs and native approximation indices.
/-- Under the stated graph and Fredholm hypotheses, the native forward index stabilizes. -/
theorem eventually_index_eq_of_native_corner_approximation
    (A₀₀ : SmoothComplexBundleAtlas (n := n) E₀₀) (L₀₀ : AtlasBundlePresentation A₀₀)
    (i₀₀ : A₀₀.smoothSections →ₗ[ℂ] X₀₀)
    (Φ₀₀ : L₀₀.SobolevSpace 0 ≃L[ℂ] X₀₀)
    (hΦ₀₀ : ∀ u, Φ₀₀ (L₀₀.smoothToSobolev 0 u) = i₀₀ u)
    (A₁₀ : SmoothComplexBundleAtlas (n := n) E₁₀) (L₁₀ : AtlasBundlePresentation A₁₀)
    (i₁₀ : A₁₀.smoothSections →ₗ[ℂ] X₁₀)
    (Φ₁₀ : L₁₀.SobolevSpace 0 ≃L[ℂ] X₁₀)
    (hΦ₁₀ : ∀ u, Φ₁₀ (L₁₀.smoothToSobolev 0 u) = i₁₀ u)
    (A₀₁ : SmoothComplexBundleAtlas (n := n) E₀₁) (L₀₁ : AtlasBundlePresentation A₀₁)
    (i₀₁ : A₀₁.smoothSections →ₗ[ℂ] X₀₁)
    (Φ₀₁ : L₀₁.SobolevSpace 0 ≃L[ℂ] X₀₁)
    (hΦ₀₁ : ∀ u, Φ₀₁ (L₀₁.smoothToSobolev 0 u) = i₀₁ u)
    (A₁₁ : SmoothComplexBundleAtlas (n := n) E₁₁) (L₁₁ : AtlasBundlePresentation A₁₁)
    (i₁₁ : A₁₁.smoothSections →ₗ[ℂ] X₁₁)
    (Φ₁₁ : L₁₁.SobolevSpace 0 ≃L[ℂ] X₁₁)
    (hΦ₁₁ : ∀ u, Φ₁₁ (L₁₁.smoothToSobolev 0 u) = i₁₁ u)
    (H₀ : A₀₀.smoothSections →ₗ[ℂ] A₁₀.smoothSections)
    (H₀s : L₀₀.SobolevSpace 1 →L[ℂ] L₁₀.SobolevSpace 0)
    (hH₀s : ∀ u, H₀s (L₀₀.smoothToSobolev 1 u) = L₁₀.smoothToSobolev 0 (H₀ u))
    (V₀ : A₀₀.smoothSections →ₗ[ℂ] A₀₁.smoothSections)
    (V₀s : L₀₀.SobolevSpace 1 →L[ℂ] L₀₁.SobolevSpace 0)
    (hV₀s : ∀ u, V₀s (L₀₀.smoothToSobolev 1 u) = L₀₁.smoothToSobolev 0 (V₀ u))
    (V₁a : A₁₁.smoothSections →ₗ[ℂ] A₁₀.smoothSections)
    (V₁as : L₁₁.SobolevSpace 1 →L[ℂ] L₁₀.SobolevSpace 0)
    (hV₁as : ∀ u, V₁as (L₁₁.smoothToSobolev 1 u) = L₁₀.smoothToSobolev 0 (V₁a u))
    (H₁a : A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections)
    (H₁as : L₁₁.SobolevSpace 1 →L[ℂ] L₀₁.SobolevSpace 0)
    (hH₁as : ∀ u, H₁as (L₁₁.smoothToSobolev 1 u) = L₀₁.smoothToSobolev 0 (H₁a u))
    (H₀a : A₁₀.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
    (H₀as : L₁₀.SobolevSpace 1 →L[ℂ] L₀₀.SobolevSpace 0)
    (hH₀as : ∀ u, H₀as (L₁₀.smoothToSobolev 1 u) = L₀₀.smoothToSobolev 0 (H₀a u))
    (V₁ : A₁₀.smoothSections →ₗ[ℂ] A₁₁.smoothSections)
    (V₁s : L₁₀.SobolevSpace 1 →L[ℂ] L₁₁.SobolevSpace 0)
    (hV₁s : ∀ u, V₁s (L₁₀.smoothToSobolev 1 u) = L₁₁.smoothToSobolev 0 (V₁ u))
    (V₀a : A₀₁.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
    (V₀as : L₀₁.SobolevSpace 1 →L[ℂ] L₀₀.SobolevSpace 0)
    (hV₀as : ∀ u, V₀as (L₀₁.smoothToSobolev 1 u) = L₀₀.smoothToSobolev 0 (V₀a u))
    (H₁ : A₀₁.smoothSections →ₗ[ℂ] A₁₁.smoothSections)
    (H₁s : L₀₁.SobolevSpace 1 →L[ℂ] L₁₁.SobolevSpace 0)
    (hH₁s : ∀ u, H₁s (L₀₁.smoothToSobolev 1 u) = L₁₁.smoothToSobolev 0 (H₁ u))
    (C₀₀ : ℝ) (hC₀₀ : 0 ≤ C₀₀)
    (hbound₀₀ : ∀ u, ‖L₀₀.smoothToSobolev 1 u‖ ≤
      C₀₀ * (‖i₀₀ u‖ + ‖i₁₀ (H₀ u)‖ + ‖i₀₁ (V₀ u)‖))
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    (hbound₁₁ : ∀ u, ‖L₁₁.smoothToSobolev 1 u‖ ≤
      C₁₁ * (‖i₁₁ u‖ + ‖i₁₀ (V₁a u)‖ + ‖i₀₁ (H₁a u)‖))
    (C₁₀ : ℝ) (hC₁₀ : 0 ≤ C₁₀)
    (hbound₁₀ : ∀ u, ‖L₁₀.smoothToSobolev 1 u‖ ≤
      C₁₀ * (‖i₁₀ u‖ + ‖i₀₀ (H₀a u)‖ + ‖i₁₁ (V₁ u)‖))
    (C₀₁ : ℝ) (hC₀₁ : 0 ≤ C₀₁)
    (hbound₀₁ : ∀ u, ‖L₀₁.smoothToSobolev 1 u‖ ≤
      C₀₁ * (‖i₀₁ u‖ + ‖i₀₀ (V₀a u)‖ + ‖i₁₁ (H₁ u)‖))
    (hcross : ∀ s t, inner ℂ (i₁₀ (H₀ s)) (i₁₀ (V₁a t)) =
      inner ℂ (i₀₁ (V₀ s)) (i₀₁ (H₁a t)))
    (hcrossa : ∀ s t, inner ℂ (i₀₀ (H₀a s)) (i₀₀ (V₀a t)) =
      inner ℂ (i₁₁ (V₁ s)) (i₁₁ (H₁ t)))
    (s₀₀ : A₀₀.smoothSections ≃ₗ[ℂ] S₀₀) (s₁₀ : A₁₀.smoothSections ≃ₗ[ℂ] S₁₀)
    (s₀₁ : A₀₁.smoothSections ≃ₗ[ℂ] S₀₁) (s₁₁ : A₁₁.smoothSections ≃ₗ[ℂ] S₁₁)
    (out₀₀ : S₀₀ →ₗ[ℂ] X₀₀) (out₁₀ : S₁₀ →ₗ[ℂ] X₁₀)
    (out₀₁ : S₀₁ →ₗ[ℂ] X₀₁) (out₁₁ : S₁₁ →ₗ[ℂ] X₁₁)
    (sumPlus : (S₀₀ × S₁₁) →ₗ[ℂ] Nplus) (sumMinus : (S₁₀ × S₀₁) →ₗ[ℂ] Nminus)
    (nativePlusOne : Nplus →ₗ[ℂ] Dplus) (nativeMinusOne : Nminus →ₗ[ℂ] Dminus)
    (nativePlusZero : Nplus →ₗ[ℂ] Xplus) (nativeMinusZero : Nminus →ₗ[ℂ] Xminus)
    (phiPlus : Dplus ≃L[ℂ] WithLp 2 (L₀₀.SobolevSpace 1 × L₁₁.SobolevSpace 1))
    (phiMinus : Dminus ≃L[ℂ] WithLp 2 (L₁₀.SobolevSpace 1 × L₀₁.SobolevSpace 1))
    (psiPlus : Xplus ≃L[ℂ] WithLp 2 (X₀₀ × X₁₁))
    (psiMinus : Xminus ≃L[ℂ] WithLp 2 (X₁₀ × X₀₁))
    (K : ℕ → Nplus →ₗ[ℂ] Nminus) (Ka : ℕ → Nminus →ₗ[ℂ] Nplus)
    (R : ℕ → Dplus →L[ℂ] Xminus) (Ra : ℕ → Dminus →L[ℂ] Xplus)
    (qH₀ : ℕ → S₀₀ →ₗ[ℂ] S₁₀) (qH₀a : ℕ → S₁₀ →ₗ[ℂ] S₀₀)
    (qH₁ : ℕ → S₀₁ →ₗ[ℂ] S₁₁) (qH₁a : ℕ → S₁₁ →ₗ[ℂ] S₀₁)
    (qV₀ : ℕ → S₀₀ →ₗ[ℂ] S₀₁) (qV₀a : ℕ → S₀₁ →ₗ[ℂ] S₀₀)
    (qV₁ : ℕ → S₁₀ →ₗ[ℂ] S₁₁) (qV₁a : ℕ → S₁₁ →ₗ[ℂ] S₁₀)
    (W₀ : X₀₀ →L[ℂ] X₀₁) (W₁ : X₁₀ →L[ℂ] X₁₁)
    (hH₀ : ∃ (U : ℕ → L₀₀.SobolevSpace 1 →L[ℂ] X₁₀)
      (Ua : ℕ → L₁₀.SobolevSpace 1 →L[ℂ] X₀₀),
      (∀ m u, U m (L₀₀.smoothToSobolev 1 u) = out₁₀ (qH₀ m (s₀₀ u))) ∧
      (∀ m v, Ua m (L₁₀.smoothToSobolev 1 v) = out₀₀ (qH₀a m (s₁₀ v))) ∧
      Tendsto (fun m ↦ U m + (0 : X₀₀ →L[ℂ] X₁₀).comp
        (Φ₀₀.toContinuousLinearMap.comp (L₀₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₀.toContinuousLinearMap.comp H₀s)) ∧
      Tendsto (fun m ↦ Ua m + (0 : X₀₀ →L[ℂ] X₁₀).adjoint.comp
        (Φ₁₀.toContinuousLinearMap.comp (L₁₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₀.toContinuousLinearMap.comp H₀as)))
    (hH₁ : ∃ (U : ℕ → L₀₁.SobolevSpace 1 →L[ℂ] X₁₁)
      (Ua : ℕ → L₁₁.SobolevSpace 1 →L[ℂ] X₀₁),
      (∀ m u, U m (L₀₁.smoothToSobolev 1 u) = out₁₁ (qH₁ m (s₀₁ u))) ∧
      (∀ m v, Ua m (L₁₁.smoothToSobolev 1 v) = out₀₁ (qH₁a m (s₁₁ v))) ∧
      Tendsto (fun m ↦ U m + (0 : X₀₁ →L[ℂ] X₁₁).comp
        (Φ₀₁.toContinuousLinearMap.comp (L₀₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₁.toContinuousLinearMap.comp H₁s)) ∧
      Tendsto (fun m ↦ Ua m + (0 : X₀₁ →L[ℂ] X₁₁).adjoint.comp
        (Φ₁₁.toContinuousLinearMap.comp (L₁₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₁.toContinuousLinearMap.comp H₁as)))
    (hV₀ : ∃ (V : ℕ → L₀₀.SobolevSpace 1 →L[ℂ] X₀₁)
      (Va : ℕ → L₀₁.SobolevSpace 1 →L[ℂ] X₀₀),
      (∀ m u, V m (L₀₀.smoothToSobolev 1 u) = out₀₁ (qV₀ m (s₀₀ u))) ∧
      (∀ m v, Va m (L₀₁.smoothToSobolev 1 v) = out₀₀ (qV₀a m (s₀₁ v))) ∧
      Tendsto (fun m ↦ V m + W₀.comp
        (Φ₀₀.toContinuousLinearMap.comp (L₀₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₁.toContinuousLinearMap.comp V₀s)) ∧
      Tendsto (fun m ↦ Va m + W₀.adjoint.comp
        (Φ₀₁.toContinuousLinearMap.comp (L₀₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₀₀.toContinuousLinearMap.comp V₀as)))
    (hV₁ : ∃ (V : ℕ → L₁₀.SobolevSpace 1 →L[ℂ] X₁₁)
      (Va : ℕ → L₁₁.SobolevSpace 1 →L[ℂ] X₁₀),
      (∀ m u, V m (L₁₀.smoothToSobolev 1 u) = out₁₁ (qV₁ m (s₁₀ u))) ∧
      (∀ m v, Va m (L₁₁.smoothToSobolev 1 v) = out₁₀ (qV₁a m (s₁₁ v))) ∧
      Tendsto (fun m ↦ V m + W₁.comp
        (Φ₁₀.toContinuousLinearMap.comp (L₁₀.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₁.toContinuousLinearMap.comp V₁s)) ∧
      Tendsto (fun m ↦ Va m + W₁.adjoint.comp
        (Φ₁₁.toContinuousLinearMap.comp (L₁₁.sobolevInclusion 1 0 (by norm_num))))
        atTop (𝓝 (Φ₁₀.toContinuousLinearMap.comp V₁as))) :
    let cXE := WithLp.prodContinuousLinearEquiv 2 ℂ
      (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)
    let cXO := WithLp.prodContinuousLinearEquiv 2 ℂ
      (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ X₀₀ X₁₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ X₁₀ X₀₁
    (∀ u v, phiPlus (nativePlusOne (sumPlus (s₀₀ u, s₁₁ v))) =
      cXE.symm ((L₀₀.smoothToSobolev 1) u, (L₁₁.smoothToSobolev 1) v)) →
    (∀ u v, phiMinus (nativeMinusOne (sumMinus (s₁₀ u, s₀₁ v))) =
      cXO.symm ((L₁₀.smoothToSobolev 1) u, (L₀₁.smoothToSobolev 1) v)) →
    (∀ u v, psiPlus (nativePlusZero (sumPlus (s₀₀ u, s₁₁ v))) =
      cEven.symm (out₀₀ (s₀₀ u), out₁₁ (s₁₁ v))) →
    (∀ u v, psiMinus (nativeMinusZero (sumMinus (s₁₀ u, s₀₁ v))) =
      cOdd.symm (out₁₀ (s₁₀ u), out₀₁ (s₀₁ v))) →
    (∀ m s, R m (nativePlusOne s) = nativeMinusZero (K m s)) →
    (∀ m s, Ra m (nativeMinusOne s) = nativePlusZero (Ka m s)) →
    (∀ m a b, K m (sumPlus (a, b)) =
      sumMinus (qH₀ m a - qV₁a m b, qV₀ m a + qH₁a m b)) →
    (∀ m a b, Ka m (sumMinus (a, b)) =
      sumPlus (qH₀a m a + qV₀a m b, -qV₁ m a + qH₁ m b)) →
    let T := fun m ↦ psiMinus.toContinuousLinearMap.comp
      ((R m).comp phiPlus.symm.toContinuousLinearMap)
    let S := fun m ↦ psiPlus.toContinuousLinearMap.comp
      ((Ra m).comp phiMinus.symm.toContinuousLinearMap)
    let iEven := cEven.symm.toLinearMap.comp (i₀₀.prodMap i₁₁)
    let iOdd := cOdd.symm.toLinearMap.comp (i₁₀.prodMap i₀₁)
    let dSmooth := cOdd.symm.toLinearMap.comp
      (((i₁₀.comp H₀).coprod (-(i₁₀.comp V₁a))).prod
        ((i₀₁.comp V₀).coprod (i₀₁.comp H₁a)))
    let aSmooth := cEven.symm.toLinearMap.comp
      (((i₀₀.comp H₀a).coprod (i₀₀.comp V₀a)).prod
        ((-(i₁₁.comp V₁)).coprod (i₁₁.comp H₁)))
    ∀ (D : WithLp 2 (X₀₀ × X₁₁) →ₗ.[ℂ] WithLp 2 (X₁₀ × X₀₁))
      (Da : WithLp 2 (X₁₀ × X₀₁) →ₗ.[ℂ] WithLp 2 (X₀₀ × X₁₁)),
      D.IsClosed → Da.IsClosed →
      D.graph = (iEven.prod dSmooth).range.topologicalClosure →
      Da.graph = (iOdd.prod aSmooth).range.topologicalClosure →
      D.IsFormalAdjoint Da →
      IsClosed (D.toFun.range : Set (WithLp 2 (X₁₀ × X₀₁))) →
      IsClosed (Da.toFun.range : Set (WithLp 2 (X₀₀ × X₁₁))) →
      FiniteDimensional ℂ D.ker → FiniteDimensional ℂ Da.ker →
      (∀ᶠ m in atTop, (T m).IsFredholm ∧ (S m).IsFredholm) →
      (∀ᶠ m in atTop, (T m).index + (S m).index = 0) →
      ∀ᶠ m in atTop,
        (T m).index = (Module.finrank ℂ D.ker : ℤ) - Module.finrank ℂ Da.ker := by
  intro cXE cXO cEven cOdd hPhiPlus hPhiMinus hPsiPlus hPsiMinus hR hRa hK hKa
    T S iEven iOdd dSmooth aSmooth D Da hD hDa hgraph hgrapha hformal
    hDrange hDarange hDker hDaker hFredholm hindex
  -- Form the completed signed corners using the same four Sobolev inclusions.
  let J₀₀ := Φ₀₀.toContinuousLinearMap.comp (L₀₀.sobolevInclusion 1 0 (by norm_num))
  let J₁₀ := Φ₁₀.toContinuousLinearMap.comp (L₁₀.sobolevInclusion 1 0 (by norm_num))
  let J₀₁ := Φ₀₁.toContinuousLinearMap.comp (L₀₁.sobolevInclusion 1 0 (by norm_num))
  let J₁₁ := Φ₁₁.toContinuousLinearMap.comp (L₁₁.sobolevInclusion 1 0 (by norm_num))
  let BH₀ := Φ₁₀.toContinuousLinearMap.comp H₀s
  let BV₀ := Φ₀₁.toContinuousLinearMap.comp V₀s
  let BV₁a := Φ₁₀.toContinuousLinearMap.comp V₁as
  let BH₁a := Φ₀₁.toContinuousLinearMap.comp H₁as
  let BH₀a := Φ₀₀.toContinuousLinearMap.comp H₀as
  let BV₁ := Φ₁₁.toContinuousLinearMap.comp V₁s
  let BV₀a := Φ₀₀.toContinuousLinearMap.comp V₀as
  let BH₁ := Φ₁₁.toContinuousLinearMap.comp H₁s
  let TE := gradedBlockOperator BH₀ BV₀ BV₁a BH₁a
  let TO := cEven.symm.toContinuousLinearMap.comp
    (((BH₀a.coprod BV₀a).prod ((-BV₁).coprod BH₁)).comp cXO.toContinuousLinearMap)
  -- The two residuals keep the original factorization, order and adjoint signs.
  let pE₀ := (ContinuousLinearMap.fst ℂ
    (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)).comp cXE.toContinuousLinearMap
  let pE₁ := (ContinuousLinearMap.snd ℂ
    (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)).comp cXE.toContinuousLinearMap
  let pO₀ := (ContinuousLinearMap.fst ℂ
    (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)).comp cXO.toContinuousLinearMap
  let pO₁ := (ContinuousLinearMap.snd ℂ
    (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)).comp cXO.toContinuousLinearMap
  let WE :=
    cOdd.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inr ℂ X₁₀ X₀₁).comp
      (W₀.comp (J₀₀.comp pE₀))) +
    cOdd.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inl ℂ X₁₀ X₀₁).comp
      ((-W₁.adjoint).comp (J₁₁.comp pE₁)))
  let WO :=
    cEven.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inl ℂ X₀₀ X₁₁).comp
      (W₀.adjoint.comp (J₀₁.comp pO₁))) +
    cEven.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inr ℂ X₀₀ X₁₁).comp
      ((-W₁).comp (J₁₀.comp pO₀)))
  -- Use both properties of each corner pair for the same native forward and reverse limits.
  have hlimits : Tendsto (fun m ↦ T m + WE) atTop (𝓝 TE) ∧
      Tendsto (fun m ↦ S m + WO) atTop (𝓝 TO) := by
    exact tendsto_conjugate_pair_of_native_corner_limits
      (L₀₀.smoothToSobolev 1) (L₁₀.smoothToSobolev 1)
      (L₀₁.smoothToSobolev 1) (L₁₁.smoothToSobolev 1)
      s₀₀ s₁₀ s₀₁ s₁₁ out₀₀ out₁₀ out₀₁ out₁₁ sumPlus sumMinus
      nativePlusOne nativeMinusOne nativePlusZero nativeMinusZero
      phiPlus phiMinus psiPlus psiMinus K Ka R Ra
      qH₀ qH₀a qH₁ qH₁a qV₀ qV₀a qV₁ qV₁a
      BH₀ BH₀a BH₁ BH₁a BV₀ BV₀a BV₁ BV₁a J₀₀ J₁₀ J₀₁ J₁₁ W₀ W₁
      (L₀₀.denseRange_smoothToSobolev 1) (L₁₀.denseRange_smoothToSobolev 1)
      (L₀₁.denseRange_smoothToSobolev 1) (L₁₁.denseRange_smoothToSobolev 1)
      hH₀ hH₁ hV₀ hV₁ hPhiPlus hPhiMinus hPsiPlus hPsiMinus hR hRa hK hKa
  -- The existing compact comparison keeps the supplied graph and cutoff witnesses.
  have hcomparison := exists_graded_index_eq_of_compact_approximation
    A₀₀ L₀₀ i₀₀ Φ₀₀ hΦ₀₀ A₁₀ L₁₀ i₁₀ Φ₁₀ hΦ₁₀
    A₀₁ L₀₁ i₀₁ Φ₀₁ hΦ₀₁ A₁₁ L₁₁ i₁₁ Φ₁₁ hΦ₁₁
    H₀ H₀s hH₀s V₀ V₀s hV₀s V₁a V₁as hV₁as H₁a H₁as hH₁as
    H₀a H₀as hH₀as V₁ V₁s hV₁s V₀a V₀as hV₀as H₁ H₁s hH₁s
    C₀₀ hC₀₀ hbound₀₀ C₁₁ hC₁₁ hbound₁₁ C₁₀ hC₁₀ hbound₁₀
    C₀₁ hC₀₁ hbound₀₁ hcross hcrossa
    D Da hD hDa hgraph hgrapha hformal hDrange hDarange hDker hDaker W₀ W₁
    atTop T S hlimits.1 hlimits.2 hFredholm hindex
  exact hcomparison.2.mono fun _ hm ↦ hm.1

end AtiyahSinger
