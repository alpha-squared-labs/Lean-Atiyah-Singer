/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothBundleSumDecomposition

/-!
# Sobolev spaces of a specified smooth bundle sum

Public module ID: M0990.

The two original smooth inclusions and their inverse projections extend to
mutually inverse maps in every fixed Sobolev order. The presentations remain
specified, so this comparison identifies the actual graded-product H1 domain
with its native smooth direct-sum bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r₁ r₂ r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E₁ E₂ E : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₂)) E₂)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₂)) E₂]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₂)) E₂]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₂) E₂]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

include μ

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
/-- The specified smooth sum identifies its actual Sobolev completion with the two
original component completions, retaining the exact inverse projections on smooth sections. -/
theorem exists_sobolevEquiv_of_smoothBundleSum
    (e : ∀ x, (E₁ x × E₂ x) ≃ₗ[ℂ] E x)
    (h₁ : IsSmoothBundleMap (n := n) (r := r₁) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))))
    (h₂ : IsSmoothBundleMap (n := n) (r := r₂) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))))
    (A₁ : SmoothBundlePresentation (n := n) (r := r₁) E₁)
    (A₂ : SmoothBundlePresentation (n := n) (r := r₂) E₂)
    (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) :
    let p₁ := smoothSectionMap
      (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
      (isSmoothBundleMap_sumInverse e h₁ h₂).1
    let p₂ := smoothSectionMap
      (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
      (isSmoothBundleMap_sumInverse e h₁ h₂).2
    ∃ U : A.SobolevSpace s ≃L[ℂ] (A₁.SobolevSpace s × A₂.SobolevSpace s),
      ∀ u, U (A.smoothToSobolev s u) =
        (A₁.smoothToSobolev s (p₁ u), A₂.smoothToSobolev s (p₂ u)) := by
  classical
  let I₁ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))) h₁
  let I₂ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))) h₂
  let D₁ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).1
  let D₂ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).2
  let I := (I₁.sobolevRealization A₁ A s s (by simp)).coprod
    (I₂.sobolevRealization A₂ A s s (by simp))
  let J := (D₁.sobolevRealization A A₁ s s (by simp)).prod
    (D₂.sobolevRealization A A₂ s s (by simp))
  have hJ (u : smoothSections (n := n) (r := r) E) :
      J (A.smoothToSobolev s u) =
        (A₁.smoothToSobolev s (D₁.toLinearMap u), A₂.smoothToSobolev s (D₂.toLinearMap u)) := by
    exact Prod.ext (D₁.sobolevRealization_smoothToSobolev A A₁ s s (by simp) u)
      (D₂.sobolevRealization_smoothToSobolev A A₂ s s (by simp) u)
  have hI (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := n) (r := r₂) E₂) :
      I (A₁.smoothToSobolev s u, A₂.smoothToSobolev s v) =
        A.smoothToSobolev s (I₁.toLinearMap u + I₂.toLinearMap v) := by
    change I₁.sobolevRealization A₁ A s s (by simp) (A₁.smoothToSobolev s u) +
      I₂.sobolevRealization A₂ A s s (by simp) (A₂.smoothToSobolev s v) = _
    rw [I₁.sobolevRealization_smoothToSobolev, I₂.sobolevRealization_smoothToSobolev, map_add]
  -- The two inverse identities first hold on the exact same smooth section maps.
  have hsum (u : smoothSections (n := n) (r := r) E) :
      I₁.toLinearMap (D₁.toLinearMap u) + I₂.toLinearMap (D₂.toLinearMap u) = u := by
    apply Subtype.ext
    funext x
    change e x (((e x).symm (u.val x)).1, 0) +
      e x (0, ((e x).symm (u.val x)).2) = u.val x
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using
      (e x).apply_symm_apply (u.val x)
  have hproj (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := n) (r := r₂) E₂) :
      (D₁.toLinearMap (I₁.toLinearMap u + I₂.toLinearMap v),
        D₂.toLinearMap (I₁.toLinearMap u + I₂.toLinearMap v)) = (u, v) := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change ((e x).symm (e x (u.val x, 0) + e x (0, v.val x))).1 = u.val x
      rw [← map_add, (e x).symm_apply_apply]
      simp only [Prod.mk_add_mk, add_zero]
    · apply Subtype.ext
      funext x
      change ((e x).symm (e x (u.val x, 0) + e x (0, v.val x))).2 = v.val x
      rw [← map_add, (e x).symm_apply_apply]
      simp only [Prod.mk_add_mk, zero_add]
  have hAB : I.comp J = ContinuousLinearMap.id ℂ (A.SobolevSpace s) := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer (I.comp J).continuous
      (ContinuousLinearMap.id ℂ (A.SobolevSpace s)).continuous
    funext u
    change I (J (A.smoothToSobolev s u)) = A.smoothToSobolev s u
    rw [hJ, hI, hsum]
  have hBA : J.comp I = ContinuousLinearMap.id ℂ
      (A₁.SobolevSpace s × A₂.SobolevSpace s) := by
    apply DFunLike.coe_injective
    apply ((A₁.denseRange_smoothToSobolev s).prodMap
      (A₂.denseRange_smoothToSobolev s)).equalizer (J.comp I).continuous
        (ContinuousLinearMap.id ℂ (A₁.SobolevSpace s × A₂.SobolevSpace s)).continuous
    funext z
    change J (I (A₁.smoothToSobolev s z.1, A₂.smoothToSobolev s z.2)) =
      (A₁.smoothToSobolev s z.1, A₂.smoothToSobolev s z.2)
    rw [hI, hJ]
    exact Prod.ext (congrArg (A₁.smoothToSobolev s) (congrArg Prod.fst (hproj z.1 z.2)))
      (congrArg (A₂.smoothToSobolev s) (congrArg Prod.snd (hproj z.1 z.2)))
  let U : A.SobolevSpace s ≃L[ℂ] (A₁.SobolevSpace s × A₂.SobolevSpace s) :=
    { J.toLinearMap with
      invFun := I
      left_inv := fun x ↦ DFunLike.congr_fun hAB x
      right_inv := fun y ↦ DFunLike.congr_fun hBA y
      continuous_toFun := J.continuous
      continuous_invFun := I.continuous }
  exact ⟨U, hJ⟩

end AtiyahSinger
